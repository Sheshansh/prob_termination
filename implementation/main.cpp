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

struct cond{
	int src;
	int dest1;
	int dest2;
	bool probability;
	cond(int src,int dest1,int dest2 = 0,double probability = -1.0){
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

void generate_equations(ofstream& equationsfile){ //Would use the ofstream file to write the equations into it later
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		if(it->second->type=="det"){
			//Invariant and guard imply the value decrease
			if(it->second->edges.size()==1){
				//First make a condition
				cond* condition = new cond(it->first,it->second->edges[0].next->label);
				// Guard would have been NULL here
				if(it->second->invariant==NULL){
					//This should never be the case as this would pose conditions that c==0 and d>0, which are not good
					cerr<<"No invariant specified here"<<endl;
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
				cond* condition0 = new cond(it->first,it->second->edges[0].next->label);
				cond* condition1 = new cond(it->first,it->second->edges[1].next->label);
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
			cond* condition0 = new cond(it->first,it->second->edges[0].next->label);
			cond* condition1 = new cond(it->first,it->second->edges[1].next->label);
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
			cond* condition = new cond(it->first,it->second->edges[0].next->label,it->second->edges[1].next->label,it->second->edges[0].probability);
			//Invariant implies the value decrease of expected value of ranking function, "prob" type node
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations.push(new equation(it->second->invariant->children[i],condition));
			}
		}
	}
}

int main(){
	char input[MAXL];
	// cout<<fixed<<setprecision(10);
	int r,i;
	for(i=0;(r=getchar())!=EOF;i++)
		input[i]=r;
	input[i]=0;
	program=input;
	nVariables = find_variables(); //To find the number of different variables of the type x_i in the program
	id1->constant = "expression";
	id1->expression.resize(nVariables+1);
	id1->expression[1] = 1.0;
	int start,end;
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	CFG_edge last_edge(label_map[end],1,id1);
	label_map[end]->edges.pb(last_edge);
	root=new node("stmt",0,program.length(),start,end);
	cout<<"Input Code:"<<endl;
	cout<<program<<endl;
	cout<<"Parse Tree:"<<endl;
	root->print();
	cout<<"CFG:"<<endl;
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		cout<<"------------------------"<<endl;
		cout<<"Node "<<it->first<<endl;
		it->second->print();
		// cout<<it->second->label<<endl;
	}
	ofstream equationsfile;
	equationsfile.open ("equations.txt");
	generate_equations(equationsfile);
	equationsfile.close();
	return 0;
}