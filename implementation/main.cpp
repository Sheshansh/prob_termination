// Do I have to add a self loop on the end CFG location, because then the epsilon equation creates issues
// end node will always be 2
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
#include <queue>
#include "files/Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back
#define A(i,j) (front->affexpr->children[i]->children[0]->expression[j+1])
#define b(i) (-1.0*front->affexpr->children[i]->children[0]->expression[0])

stringstream buffer;

struct cond{
	bool strict;
	vector<string> c;
	string negative_d; //negative component of d
	cond(int equation_count,int toChange,node* change,int src,int dest1,int dest2 = -1,double probability = -1.0){
		strict = false;
		c.resize(nVariables);
		if(dest2==-1){
			if(change==NULL){
				buffer.clear();
				buffer.str(string());
				buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+f_"<<dest1<<"_0";
				negative_d = buffer.str();
				for(int i=0;i<nVariables;i++){
					buffer.clear();
					buffer.str(string());
					buffer<<"f_"<<dest1<<"_"<<i+1<<"-f_"<<src<<"_"<<i+1;
					c[i] = buffer.str();
				}
			}
			else{
				// cout<<"change is : src"<<src<<" dest:"<<dest1<<" toChange:"<<toChange<<" changed to:";
				// change->print();
				// cout<<endl;
				buffer.clear();
				buffer.str(string());
				buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+f_"<<dest1<<"_0";
				if(change->expression[0]<0.0){
					buffer<<change->expression[0]<<"f_"<<dest1<<"_"<<toChange;
				}
				else if(change->expression[0]>0.0){
					buffer<<"+"<<change->expression[0]<<"f_"<<dest1<<"_"<<toChange;
				}
				negative_d = buffer.str();
				for(int i = 0;i<nVariables;i++){
					buffer.clear();
					buffer.str(string());
					if((i+1)!=toChange){
						buffer<<"f_"<<dest1<<"_"<<i+1;
						if(change->expression[i+1]>0.0){
							buffer<<"+"<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
						else if(change->expression[i+1]<0.0){
							buffer<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
					}
					else{
						if(change->expression[i+1]!=0.0){
							buffer<<change->expression[i+1]<<"f_"<<dest1<<"_"<<toChange;
						}
						// change->print();
						// cout<<""<<endl;
					}
					buffer<<"-f_"<<src<<"_"<<i+1;
					c[i] = buffer.str();
					// cout<<c[i]<<endl;
				}
			}
		}
		else{
			// It was a stochastic node, means change would have been NULL
			buffer.clear();
			buffer.str(string());
			buffer<<"eps"<<equation_count<<"-f_"<<src<<"_0+"<<probability<<"f_"<<dest1<<"_0+"<<1.0-probability<<"f_"<<dest2<<"_0"; 
			negative_d = buffer.str();
			for(int i=0;i<nVariables;i++){
				buffer.clear();
				buffer.str(string());
				buffer<<probability<<"f_"<<dest1<<"_"<<i+1<<"+"<<1.0-probability<<"f_"<<dest2<<"_"<<i+1<<"-f_"<<src<<"_"<<i+1;
				c[i] = buffer.str();
			}
		}
	}
	cond(int location_id){
		strict = (location_id!=2);
		c.resize(nVariables);
		for(int i=0;i<nVariables;++i){
			buffer.clear();
			buffer.str(string());
			buffer<<"-f_"<<location_id<<"_"<<i+1;
			c[i] = buffer.str();
		}
		buffer.clear();
		buffer.str(string());
		buffer<<"-f_"<<location_id<<"_"<<0;
		negative_d = buffer.str();
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

map<int,equation*> equations;
int equations_counter = 0;
int epsilons_used = 0;

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
			if(it->second->edges.empty()){
				//Code for the last node
			}
			else if(it->second->edges.size()==1){
				//First make a condition
				cond* condition = new cond(++equations_counter,it->second->edges[0].toChange,it->second->edges[0].change,it->first,it->second->edges[0].next->label);
				// Guard would have been NULL here
				if(it->second->invariant==NULL){
					//This should never be the case as this would pose conditions that c==0 and d>0, which are not good
					cerr<<"No invariant specified here"<<endl;
				}
				else{
					// Invariant implies the given condition
					int nEquations = it->second->invariant->children.size();
					for(int i=0;i<nEquations;i++){
						equations[equations_counter] = new equation(it->second->invariant->children[i],condition);
						// equations.push(new equation(it->second->invariant->children[i],condition));
					}
				}
			}
			else{
				//First make the 2 conditions required
				cond* condition0 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label);
				cond* condition1 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[1].next->label);
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
						equations[equations_counter-1] = new equation(n0->children[i],condition0);
						// equations.push(new equation(n0->children[i],condition0));
					}
					nEquations = n1->children.size();
					for(int i=0;i<nEquations;i++){
						equations[equations_counter] = new equation(n1->children[i],condition1);
						// equations.push(new equation(n1->children[i],condition1));
					}
				}
			}
		}
		else if(it->second->type=="ndet"){
			// First make the 2 conditions required
			cond* condition0 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label);
			cond* condition1 = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[1].next->label);
			//Invariant implies the value decrease for both the emerging transitions
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations[equations_counter-1] = new equation(it->second->invariant->children[i],condition0);
				// equations.push(new equation(it->second->invariant->children[i],condition0));
			}
			for(int i=0;i<nEquations;i++){
				equations[equations_counter] = new equation(it->second->invariant->children[i],condition1);
				// equations.push(new equation(it->second->invariant->children[i],condition1));
			}
		}
		else{
			//Make one condition for the expected value decrease
			cond* condition = new cond(++equations_counter,-1,NULL,it->first,it->second->edges[0].next->label,it->second->edges[1].next->label,it->second->edges[0].probability);
			//Invariant implies the value decrease of expected value of ranking function, "prob" type node
			int nEquations = it->second->invariant->children.size();
			for(int i=0;i<nEquations;i++){
				equations[equations_counter] = new equation(it->second->invariant->children[i],condition);
				// equations.push(new equation(it->second->invariant->children[i],condition));
			}
		}
	}
	epsilons_used = equations_counter;
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		// Invariant implies the ranking function to be positive
		int nEquations = it->second->invariant->children.size();
		for(int i=0;i<nEquations;i++){
			cond* condition = new cond(it->first);
			equations[++equations_counter] = new equation(it->second->invariant->children[i],condition);
			// equations.push(new equation(it->second->invariant->children[i],condition));
		}
	}
}

int last_used_lambda = 0;

void print_equations(ofstream& equationsfile){
	// <flag> to be changed
	
	equationsfile<<"maximize ";
	for(int i=1;i<=epsilons_used;++i){
		if(equations.find(i)!=equations.end()){
			equationsfile<<"+eps"<<i;
		}
	}
	equationsfile<<"\n\nst\n\n";
	for(int i=1;i<=epsilons_used;++i){
		if(equations.find(i)!=equations.end()){
			equationsfile<<"eps"<<i<<" >= 0\neps"<<i<<" <= 1"<<endl;
		}
	}
	

	for(map<int,equation*>::iterator it = equations.begin();it!=equations.end();++it){
		equation* front = it->second;
		// A(i,j) means affexpr->children[i-1]->children[0]->expression[j] and b(i) translates to -1.0*affexpr->children[i-1]->children[0]->expression[0]
		// Creating a macro for this
		//Printing equations
		int size = front->affexpr->children.size();
		for(int i=0;i<nVariables;++i){
			// Each iteration, print out a new equation! :)
			equationsfile<<front->condition->c[i];
			for(int j=0;j<size;++j){
				if(A(j,i)>0){
					equationsfile<<-A(j,i)<<"l"<<to_string(last_used_lambda+j);
				}
				else if(A(j,i)<0){
					equationsfile<<"+"<<-A(j,i)<<"l"<<to_string(last_used_lambda+j);
				}
			}
			equationsfile<<" = 0"<<endl;
		}
		// Printing the last equation
		equationsfile<<front->condition->negative_d;
		for(int i=0;i<size;++i){
			if(b(i)>0){
				equationsfile<<"+"<<b(i)<<"l"<<to_string(last_used_lambda+i);
			}
			else if(b(i)<0){
				equationsfile<<b(i)<<"l"<<to_string(last_used_lambda+i);
			}
		}
		if(front->condition->strict){
			equationsfile<<" < 0"<<endl;
		}
		else{
			equationsfile<<" <= 0"<<endl;
		}
		last_used_lambda += size;
	}

	equationsfile<<"\nbounds\n\n";
	//Loop to print bounds on other variables
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		for(int j=0;j<=nVariables;j++){
			equationsfile<<"-inf<= f_"<<it->first<<"_"<<j<<" <= +inf"<<endl;
		}
	}
	equationsfile<<"end"<<endl;
}

bool process_equations_output(){
	bool to_return = false;
	ifstream to_process("files/EquationsOutput");
	string line;
	getline(to_process,line);
	if(line=="CPLEX> Variable Name           Solution Value"){
		string temp1,temp2;
		while(to_process>>temp1>>temp2){
			// cout<<temp1<<" "<<temp2<<endl;
			if(temp1.length()>3){
				if(temp1.substr(0,3)=="eps"){
					// cout<<stoi(temp1.substr(3))<<endl;
					equations.erase(stoi(temp1.substr(3)));
					to_return = true;
					//Removing those equations whose epsilon is 1
				}
			}
		}
	}
	return to_return;
}

int main(){
	int start,end;
	char input[MAXL];
	// Setting precision to the printing of the double variables in program
	// cout<<fixed<<setprecision(10);
	int r,i;
	for(i=0;(r=getchar())!=EOF;i++)
		input[i]=r;
	input[i]=0;
	program=input;
	nVariables = find_variables(); //To find the number of different variables of the type x_i in the program
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	// Code for adding self loop
	// CFG_edge last_edge(label_map[end],-1,NULL);
	// label_map[end]->edges.pb(last_edge);
	int begin = 0;
	int endprog = program.length();
	skip_spaces(begin,endprog);
	if(program[endprog-1]==']'){
		//This means that there is an end invariant in the program and we can store that into label_map[end]
		int open = -1;
		for(int i = endprog-1;i>=0;--i){
			if(program[i]=='['){
				open = i;
				break;
			}
		}
		if(open==-1){
			cerr<<"Some error with square brackets and end invariant"<<endl;
		}
		label_map[end]->invariant = new node("bexpr",open+1,endprog);
		endprog = open;
	}
	skip_spaces(begin,endprog);
	root=new node("stmt",begin,endprog,start,end);
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
	generate_equations();
	ofstream equationsfile;
	for(int loop_counter=0;loop_counter<100;++loop_counter){	
		cout<<"Iteration"<<loop_counter+1<<"->"<<endl;
		equationsfile.open("files/equations.lp");
		print_equations(equationsfile);
		equationsfile.close();
		// Jugaad for calling cplex from within the code
		if(system("./files/script.sh")!=0){
			cout<<"Something wrong with the script analysing equations"<<endl;
		}
		//Processing the EquationsOutput file
		bool state = process_equations_output();
		if(state==false){
			cout<<"No solution possible"<<endl;
			string command;
			command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
			system(command.c_str());
			break;
		}
		else{
			//Some equation was deleted, some epsilon was 1
			// cout<<equations.begin()->first<<" "<<epsilons_used<<endl;
			if(equations.begin()->first>epsilons_used){
				cout<<"Solution found"<<endl;
				string command;
				command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
				system(command.c_str());
				break;
			}
			else{
				cout<<"Going into another iteration"<<endl;
			}
		}
		string command;
		command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
		system(command.c_str());
		// temporarily for just one iteration
	}
	return 0;
}