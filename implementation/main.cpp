#include <iostream>
#include <algorithm>
#include <cstdio>
#include <vector>
#include <cstring>
#include <sstream>
#include <cctype>
#include <set>
#include <map>
#include <fstream>
#include <deque>
#include <iomanip>
#include <fstream>
#include <stack>
#include "Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back
#define A(i,j) (top->affexpr->children[i]->children[0]->expression[j+1])
#define b(i) (-1.0*top->affexpr->children[i]->children[0]->expression[0])

struct cond{
	int toChange;
	node* change;
	int src;
	int dest1;
	int dest2;
	bool probability;
	cond(int toChange,node* change,int src,int dest1,int dest2 = -1,double probability = -1.0){
		this->toChange = toChange;
		this->change = change;
		this->src = src;
		this->dest1 = dest1;
		this->dest2 = dest2;
		this->probability = probability;
	}
};

struct equation{
	node* affexpr;
	cond* condition;
	equation(){
		affexpr = NULL;
		condition = NULL;
	}
	equation(node* affexpr,cond* condition){
		this->affexpr = affexpr;
		this->condition = condition;
	}
};

stack<equation*> equations;

node* and_node(node* one,node* two){
	if(one->type!="bexpr" or two->type!="bexpr"){
		cerr<<"Taking and of wrong type of nodes"<<endl;
		return NULL;
	}
	node* node_and = NULL;
	node* temp_affexpr = NULL;
	node_and = new node("bexpr");
	node_and->constant = "or";
	int a = one->children.size(), b = two->children.size();
	for(int i = 0;i<a;i++){
		for(int j = 0;j<b;j++){
			temp_affexpr = new node("affexpr");
			temp_affexpr->constant = "and";
			temp_affexpr->children = one->children[i]->children;
			temp_affexpr->children.insert(temp_affexpr->children.end(),two->children[j]->children.begin(),two->children[j]->children.end());
			node_and->children.pb(temp_affexpr);
		}
	}
	return node_and;
}

void generate_equations(){ //Would use the ofstream file to write the equations into it later
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		if(it->second->type=="det"){
			//Invariant and guard imply the value decrease
			if(it->second->edges.size()==1){
				//First make a condition
				cond* condition = new cond(it->second->edges[0].toChange,it->second->edges[0].change,it->first,it->second->edges[0].next->label);
				// Guard would have been NULL here
				if(it->second->invariant==NULL){
					//This should never be the case as this would pose conditions that c==0 and d>0, which are not good
					// cerr<<"No invariant specified here"<<endl;
					//This would arise for the end states and skip and other special conditions
				}
				else{
					// Invariant implies the given condition
					int nEquations = it->second->invariant->children.size();
					for(int i=0;i<nEquations;i++){
						equations.push(new equation(it->second->invariant->children[i],condition));
					}
				}
			}
			else{
				//First make the 2 conditions required
				cond* condition0 = new cond(-1,NULL,it->first,it->second->edges[0].next->label);
				cond* condition1 = new cond(-1,NULL,it->first,it->second->edges[1].next->label);
				// Size is 2, so considering the guards is important and guards cannot be NULL
				if(it->second->invariant==NULL or it->second->edges[0].guard==NULL or it->second->edges[1].guard==NULL){
					//This should never be the case as this would pose conditions that c==0 and d>0, which are not good
					cerr<<"No invariant or no guard specified here"<<endl;
				}
				else{
					//First take and of guard and invariant and then make the corresponding equations
					node* n0 = and_node(it->second->invariant,it->second->edges[0].guard);
					node* n1 = and_node(it->second->invariant,it->second->edges[1].guard);
					int nEquations = n0->children.size();
					for(int i=0;i<nEquations;i++){
						equations.push(new equation(n0->children[i],condition0));
					}
					nEquations = n1->children.size();
					for(int i=0;i<nEquations;i++){
						equations.push(new equation(n1->children[i],condition1));
					}
				}
			}
		}
		else if(it->second->type=="ndet"){
			// First make the 2 conditions required
			cond* condition0 = new cond(-1,NULL,it->first,it->second->edges[0].next->label);
			cond* condition1 = new cond(-1,NULL,it->first,it->second->edges[1].next->label);
			//Invariant implies the value decrease for both the emerging transitions
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations.push(new equation(it->second->invariant->children[i],condition0));
			}
			for(int i=0;i<nEquations;i++){
				equations.push(new equation(it->second->invariant->children[i],condition1));
			}
		}
		else{
			//Make one condition for the expected value decrease
			cond* condition = new cond(-1,NULL,it->first,it->second->edges[0].next->label,it->second->edges[1].next->label,it->second->edges[0].probability);
			//Invariant implies the value decrease of expected value of ranking function, "prob" type node
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations.push(new equation(it->second->invariant->children[i],condition));
			}
		}
	}
}

int last_used_lambda = 0;

void print_equations(){
	vector<string> c;
	string negative_d; //negative component of d
	// string constant; //cons
	c.resize(nVariables);
	while(!equations.empty()){
		equation* top = equations.top();
		//A(i,j) means affexpr->children[i-1]->children[0]->expression[j] and b(i) translates to -1.0*affexpr->children[i-1]->children[0]->expression[0]
		//Creating a macro for this
		//Create c and d now
		if(top->condition->dest2==-1){
			if(top->condition->change==NULL){
				negative_d = "epsilon-f_"+to_string(top->condition->src)+"_0+f_"+to_string(top->condition->dest1)+"_0"; 
				for(int i=0;i<nVariables;i++){
					// c[i] = "";
					c[i] = "f_"+to_string(top->condition->dest1)+"_"+to_string(i+1)+"-f_"+to_string(top->condition->src)+"_"+to_string(i+1);
					// cout<<c[i]<<endl;
				}
			}
			else{
				// negative_d = "not set";
				negative_d = "epsilon-f_"+to_string(top->condition->src)+"_0+f_"+to_string(top->condition->dest1)+"_0";
				if(top->condition->change->expression[0]<0.0){
					negative_d = negative_d+to_string(top->condition->change->expression[0])+"f_"+to_string(top->condition->dest1)+"_"+to_string(top->condition->toChange);
				}
				else if(top->condition->change->expression[0]>0.0){
					negative_d = negative_d+"+"+to_string(top->condition->change->expression[0])+"f_"+to_string(top->condition->dest1)+"_"+to_string(top->condition->toChange);
				}
				for(int i = 0;i<nVariables;i++){
					if(i!=top->condition->toChange){
						c[i] = "f_"+to_string(top->condition->dest1)+"_"+to_string(i+1)+"-"+"f_"+to_string(top->condition->src)+"_"+to_string(i+1);
					}
					else{
						c[i] = "f_"+to_string(top->condition->dest1)+"_"+to_string(i+1)+"-"+"f_"+to_string(top->condition->src)+"_"+to_string(i+1);
					}
					c[i] = "not set";
				}
			}
		}
		else{
			// It was a stochastic node, means change would have been NULL
			negative_d = "epsilon-f_"+to_string(top->condition->src)+"_0+"+to_string(top->condition->probability)+"f_"+to_string(top->condition->dest1)+"_0+"+to_string(1.0-top->condition->probability)+"f_"+to_string(top->condition->dest2)+"_0"; 
			for(int i=0;i<nVariables;i++){
				c[i] = to_string(top->condition->probability)+"f_"+to_string(top->condition->dest1)+"_"+to_string(i+1)+to_string(1.0-top->condition->probability)+"f_"+to_string(top->condition->dest2)+"_"+to_string(i+1)+"-"+"f_"+to_string(top->condition->src)+"_"+to_string(i+1);
			}
		}
		//Printing equations
		int size = equations.top()->affexpr->children.size();
		for(int i=0;i<nVariables;++i){
			//Each iteration, print out a new equation! :)
			// cout<<A(0,i)<<"l_"<<to_string(last_used_lambda);
			cout<<c[i];
			for(int j=0;j<size;++j){
				if(A(j,i)>0){
					cout<<-A(j,i)<<"l_"<<to_string(last_used_lambda+j);
				}
				else if(A(j,i)<0){
					cout<<"+"<<-A(j,i)<<"l_"<<to_string(last_used_lambda+j);
				}
			}
			cout<<" = 0"<<endl;
		}
		//Printing the last equation
		cout<<negative_d;
		for(int i=0;i<size;++i){
			if(b(i)>0){
				cout<<"+"<<b(i)<<"l_"<<to_string(last_used_lambda+i);
			}
			else if(b(i)<0){
				cout<<b(i)<<"l_"<<to_string(last_used_lambda+i);
			}
		}
		cout<<" <= 0"<<endl;
		last_used_lambda += size;
		equations.pop();
	}
}

int main(){
	char input[MAXL];
	// Setting precision to the printing of the double variables in program
	// cout<<fixed<<setprecision(10);
	int r,i;
	for(i=0;(r=getchar())!=EOF;i++)
		input[i]=r;
	input[i]=0;
	program=input;
	nVariables = find_variables(); //To find the number of different variables of the type x_i in the program
	int start,end;
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	CFG_edge last_edge(label_map[end],-1,NULL);
	label_map[end]->edges.pb(last_edge);
	root=new node("stmt",0,program.length(),start,end);
	// cout<<"Input Code:"<<endl;
	// cout<<program<<endl;
	// cout<<"Parse Tree:"<<endl;
	// root->print();
	// cout<<"CFG:"<<endl;
	// for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
	// 	cout<<"------------------------"<<endl;
	// 	cout<<"Node "<<it->first<<endl;
	// 	it->second->print();
	// 	// cout<<it->second->label<<endl;
	// }
	// ofstream equationsfile;
	// equationsfile.open ("equations.txt");
	generate_equations();
	print_equations();
	// equationsfile.close();
	return 0;
}