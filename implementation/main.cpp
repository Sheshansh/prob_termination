// Do I have to add a self loop on the end CFG location, because then the epsilon equation creates issues
// end node will always be 2
/*
Comments:
	Considering start invariant and neglecting all other invariants, also the start invariant should be a polyhedra(Which I think would not pose a problem)
	https://tapas.labri.fr/wp/wp-content/uploads/2017/02/FAST-manual.pdf
*/
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
					}
					buffer<<"-f_"<<src<<"_"<<i+1;
					c[i] = buffer.str();
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

void generate_equations(){ //Would use the ostream file to write the equations into it later
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		if(it->second->invariant==NULL){
			// cout<<endl;
			continue;
		}
		// it->second->invariant->print();
		// cout<<endl;
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
					//It is the case when the invariant is false
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
		int nEquations = 0;
		if(it->second->invariant!=NULL){
			nEquations = it->second->invariant->children.size();
		}
		for(int i=0;i<nEquations;i++){
			cond* condition = new cond(it->first);
			equations[++equations_counter] = new equation(it->second->invariant->children[i],condition);
			// equations.push(new equation(it->second->invariant->children[i],condition));
		}
	}
}

int last_used_lambda = 0;

void print_equations(ostream& equationsfile){
	last_used_lambda = 0;
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
			equationsfile<<" <= 0"<<endl;
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
			if(temp1.length()>3){
				if(temp1.substr(0,3)=="eps"){
					equations.erase(stoi(temp1.substr(3)));
					to_return = true;
					//Removing those equations whose epsilon is 1
				}
			}
		}
	}
	return to_return;
}

string start_invariant(){
	if(label_map[1]->invariant == NULL){
		return "true";
	}
	else{
		buffer.clear();
		buffer.str(string());
		label_map[1]->invariant->print(buffer,"&&","||");
		return buffer.str();
	}
}

int last_dummy_state_used = 0;

void print_fast(ostream& fastfile){
	fastfile<<"model main{\n\n";
	fastfile<<"\tvar "<<variable[1];
	for(int i=2;i<=nVariables;++i){
		fastfile<<", "<<variable[i];
	}
	fastfile<<";\n\n";

	fastfile<<"\tstates state_1";
	for(int i=2;i<=last_used_label;++i){
		fastfile<<", state_"<<i;
	}
	for(int i=1;i<=dummy_states_needed;++i){
		fastfile<<",dummy_"<<i;
	}
	fastfile<<";\n\n";

	for(int i=1;i<=last_used_label;++i){
		CFG_location* state = label_map[i];
		for(int j=0;j<state->edges.size();++j){
			if(state->edges[j].change!=NULL){
				if(state->edges[j].change->delta!=0){
					//Add the four transitions and the job would be done
					//diverge 1
					++last_dummy_state_used;
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_diverge1"<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= dummy_"<<last_dummy_state_used<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ;\n\t};\n\n";
					//converge 1
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_converge1"<<" := {\n";
					fastfile<<"\t\tfrom\t:= dummy_"<<last_dummy_state_used<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
						fastfile<<"+"<<state->edges[j].change->delta;
					}
					fastfile<<";\n\t};\n\n";
					

					//diverge 2
					++last_dummy_state_used;
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_diverge2"<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= dummy_"<<last_dummy_state_used<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ;\n\t};\n\n";
					//converge 2
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<"_converge2"<<" := {\n";
					fastfile<<"\t\tfrom\t:= dummy_"<<last_dummy_state_used<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					if(state->edges[j].guard!=NULL){
						cerr<<"guard in an assignment"<<endl;
					}
					fastfile<<"\t\tguard\t:= true;\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
						fastfile<<"-"<<state->edges[j].change->delta;
					}
					fastfile<<";\n\t};\n\n";
				}
				else{
					fastfile<<"\ttransition t_"<<i<<"_"<<j<<" := {\n";
					fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
					fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
					fastfile<<"\t\tguard\t:= ";
					if(state->edges[j].guard==NULL){
						fastfile<<"true";
					}
					else{
						node* temp;
						if(label_map[i]->invariant!=NULL){
							temp = and_node(state->edges[j].guard,label_map[i]->invariant);
						}
						else{
							temp = state->edges[j].guard;
						}
						temp->print(fastfile,"&&","||","",true);
					}
					fastfile<<";\n";
					fastfile<<"\t\taction\t:= ";
					if(state->edges[j].change!=NULL){
						fastfile<<variable[state->edges[j].toChange]<<"' = ";
						state->edges[j].change->print(fastfile,"&&","||","",true);
					}
					fastfile<<";\n\t};\n\n";
				}
			}
			else{
				fastfile<<"\ttransition t_"<<i<<"_"<<j<<" := {\n";
				fastfile<<"\t\tfrom\t:= state_"<<i<<";\n";
				fastfile<<"\t\tto\t:= state_"<<state->edges[j].next->label<<";\n";
				fastfile<<"\t\tguard\t:= ";
				if(state->edges[j].guard==NULL){
					fastfile<<"true";
				}
				else{
					node* temp;
					if(label_map[i]->invariant!=NULL){
						temp = and_node(state->edges[j].guard,label_map[i]->invariant);
					}
					else{
						temp = state->edges[j].guard;
					}
					temp->print(fastfile,"&&","||","",true);
				}
				fastfile<<";\n";
				fastfile<<"\t\taction\t:= ;\n\t};\n\n";
			}
		}
	}

	fastfile<<"}\n\nstrategy main_s{\n\n";
	fastfile<<"\tRegion init := {state = state_1 && "<<start_invariant()<<"};\n\n";
	fastfile<<"}";
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
	int begin = 0;
	int endprog = program.length();
	skip_spaces(begin,endprog);
	nVariables = find_variables(begin,endprog); //To find the number of different variables of the type x_i in the program
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	// Code for adding self loop
	// CFG_edge last_edge(label_map[end],-1,NULL);
	// label_map[end]->edges.pb(last_edge);
	root=new node("stmt",begin,endprog,start,end);
	ofstream fastfile;
	fastfile.open("files/aspic.fast");
	ostream* outfast = &fastfile;
	print_fast(*outfast);
	fastfile.close();
	if(system("./files/invariant_script.sh")!=0){
		cout<<"Something wrong with the script to find invariants";
	}
	
	// // Code for analysing files/InvariantOutput comes here
	ifstream invariant_file("files/InvariantOutput");
	for(int i=1;i<=last_used_label;){
		string line;
		getline(invariant_file,line);
		size_t open = line.find('{');
		if(open!=string::npos){
			size_t close = line.find('}');
			string invariant_string = part(line,open+1,close);
			if(invariant_string=="true"){
				if(label_map[i]->invariant==NULL){
					label_map[i]->invariant = new node("bexpr");
					node* concerned_node = label_map[i]->invariant;
					concerned_node->children.resize(1);
					concerned_node->children[0] = new node("affexpr");
					concerned_node->children[0]->children.resize(1);
					concerned_node->children[0]->children[0] = new node("literal");
					concerned_node->children[0]->children[0]->constant = "<=";
					concerned_node->children[0]->children[0]->children.resize(1);
					concerned_node->children[0]->children[0]->children[0] = new node("expr");
					concerned_node->children[0]->children[0]->children[0]->expression.resize(nVariables+1);
				}
			}
			else if(invariant_string!="false"){
				bool temp;
				node* generated_invariant = new node("bexpr",invariant_string,temp);
				if(label_map[i]->invariant==NULL){
					label_map[i]->invariant = generated_invariant;
				}
				else if(i!=1){
					label_map[i]->invariant = and_node(label_map[i]->invariant,generated_invariant);
				}
			}
			i++;
		}
	}	
	// // Code to print the tree structure etc.
	// cout<<"Input Code:"<<endl;
	// cout<<program<<endl;
	// cout<<"Parse Tree:"<<endl;
	// root->print(cout,"&&","||","*",false);
	// cout<<"CFG:"<<endl;
	// for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
	// 	cout<<"------------------------"<<endl;
	// 	cout<<"Node "<<it->first<<endl;
	// 	it->second->print();
	// 	// cout<<it->second->label<<endl;
	// }
	
	generate_equations();
	ofstream equationsfile;
	bool solved = false;
	int loop_counter=0;
	for(;loop_counter<100;++loop_counter){	
		equationsfile.open("files/equations.lp");
		ostream* equation_output_file = &equationsfile;
		print_equations(*equation_output_file);
		equationsfile.close();
		// Jugaad for calling cplex from within the code
		if(system("./files/script.sh")!=0){
			cout<<"Something wrong with the script analysing equations"<<endl;
		}
		//Processing the EquationsOutput file
		bool state = process_equations_output();
		if(state==false){
			string command;
			command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
			system(command.c_str());
			break;
		}
		else{
			//Some equation was deleted, some epsilon was 1
			if(equations.begin()->first>epsilons_used){
				solved = true;
				string command;
				command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
				system(command.c_str());
				break;
			}
			else{
			}
		}
		string command;
		command = "mv files/EquationsOutput files/EquationsOutput" + to_string(loop_counter);
		system(command.c_str());
		// temporarily for just one iteration
	}
	cout<<"The number of states in pCFG generated is "<<last_used_label<<endl;
	if(solved){
		cout<<"Found a solution of dimension "<<loop_counter+1<<"."<<endl;
	}
	else{
		cout<<"No solution found, stopped after "<<loop_counter+1<<" iterations"<<endl;
	}
	return 0;
}