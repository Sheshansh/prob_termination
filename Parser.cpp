//Compile with C++11
//The variable names should be of the form x_i where i is a number and the indexing starts from 1 i.e. the variables in the program are of the form x_1, x_2 ... x_n.
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
#include "Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back
#define make_edge(a,b,c) edge((int*)(a),(int*)(b),(c))
#define mp make_pair

string program;
int nVariables;
int last_used_label = 0;
map<int,CFG_location*> label_map;
node* id1 = new node("expr");

void skip_spaces(int &begin, int &end){ //skips the spaces in the beginning and the end
  while(begin<program.size() and isspace(program[begin]))
	begin++;
  while(end>0 and isspace(program[end-1]))
	end--;
}

node::node(string t){
	bracket = NULL;
	begin = -1;
	end = -1;
	type = t;
	constant = "";
}

node::node(string t, int b, int e, int s, int l){
	bracket = NULL;
	type = t;
	begin = b;
	end = e;
	skip_spaces(begin,end);
	if(begin>end){
		cerr<<"Error! begin= "<<b<<" end= "<<e<<endl;
	}
	process(s,l);
}

node* negation(node* tonegate){
	if(tonegate->type=="bexpr" and tonegate->constant=="or"){
		node* negative;
		negative = new node("bexpr");
		negative->constant = "or";
		negative->children.resize(1);
		negative->children[0] = new node("affexpr");
		negative->children[0]->constant = "and";
		int ORs = tonegate->children.size();
		for(int i = 0;i<ORs;++i){
			//Multply this set of AND to the present collection
			vector<node*> before_multiplication = negative->children;
			vector<node*> after_multiplication;
			int before_size = before_multiplication.size();
			negative->children.clear();
			int ANDs = tonegate->children[i]->children.size();
			for(int j = 0;j<ANDs;++j){
				node* ch = new node("literal");
				ch->constant = "not";
				ch->children.pb(tonegate->children[i]->children[j]); //Now ch contains the negated literal
				//<flag> High optimisation possible here by the !<= ::= >= and ~~ ::= nothing
				after_multiplication = before_multiplication;
				for(int k = 0;k<before_size;++k){
					after_multiplication[k]->children.pb(ch);
				}
				negative->children.insert(negative->children.end(),after_multiplication.begin(),after_multiplication.end());
				//Appending the children after appending one element from the to be multiplied set to each of the children
			}
		}
		return negative;
	}
	cerr<<"Wrong argument in negation, passed a"<<tonegate->type<<endl;	
	return NULL;
}

void node::proc_stmt(int s,int l){
	skip_spaces(begin,end);
	if(part(program,begin,end)=="skip"){
		constant = "skip";
		CFG_edge temporary_edge(label_map[l],1,id1);
		label_map[s]->edges.pb(temporary_edge);
		// cout<<"Adding edge from "<<s<<"to"<<l<<endl;
		return;
	}
	//look for semicolons
	int open = 0; //open if's and while's
	for(int i = begin;i<end;++i){
		if(part(program,i,i+2)=="if" or part(program,i,i+5)=="while" or program[i]=='('){ //Can give seg faults in some extremely unlucky situations
			open++;
		}
		else if(part(program,i,i+2)=="od" or part(program,i,i+2)=="fi" or program[i]==')'){ //Can give errors in stupid cases
			open--;
		}
		else if(open==0 and program[i]==';'){
			constant = "several statements";
			children.resize(2);
			int mid = ++last_used_label;
			label_map[mid] = new CFG_location("det",mid);
			children[0] = new node("stmt",begin,i,s,mid);
			children[1] = new node("stmt",i+1,end,mid,l);
			return;
		}
	}

	// //look for brackets
	// skip_spaces(begin,end);
	// if(program[begin]=='['){
	// 	int closed_bracket=-1;
	// 	for(int j=begin+1;j<end;++j)
	// 		if(program[j]==']'){
	// 			closed_bracket=j; break;
	// 		}
	// 	bracket=new node("bexpr",begin+1,closed_bracket);
	// 	begin=closed_bracket+1;
	// }
	// skip_spaces(begin,end);

	//check if it is a while
	if(part(program,begin,begin+5)=="while"){
		int firstdo = -1,lastod = -1;
		for(int i = begin;i<end;++i){
			if(part(program,i,i+2)=="do"){
				firstdo = i;
				break;
			}
		}
		for(int i = end-2;i>=begin;--i){
			if(part(program,i,i+2)=="od"){
				lastod = i;
				break;
			}
		}
		if(firstdo==-1 or lastod==-1){
			cerr<<"Bad while in range ["<<begin<<","<<end<<")"<<endl;
		}
		constant = "while";
		children.resize(2);
		children[0] = new node("bexpr",begin+5,firstdo);
		int mid = ++last_used_label;
		label_map[mid] = new CFG_location("det",mid);
		node* temporary_node;
		temporary_node = negation(children[0]);
		CFG_edge temporary_edge1(label_map[l],1,id1,children[0]);
		CFG_edge temporary_edge2(label_map[mid],1,id1,temporary_node);
		label_map[s]->edges.pb(temporary_edge1);
		label_map[s]->edges.pb(temporary_edge2);
		// cout<<"Adding edge from "<<s<<"to"<<l<<endl;
		// cout<<"Adding edge from "<<s<<"to"<<mid<<endl;

		children[1] = new node("stmt",firstdo+2,lastod,mid,s);
		return;
	}
	//check if it is an if
	if(part(program,begin,begin+2)=="if"){
		int firstthen = -1; //first then
		for(int i = begin;i<end;++i){
			if(part(program,i,i+4)=="then"){
				firstthen = i;
				break;
			}
		}
		int lastfi = -1;
		for(int i = end-1;i>=begin;--i){
			if(part(program,i,i+2)=="fi"){
				lastfi = i;
				break;
			}
		}
		if(lastfi==-1 or firstthen==-1){
			cerr<<"Invalid if between ["<<begin<<", "<<end<<")"<<endl;
		}
		int correselse = -1; //corresponding else
		int ifcnt = 0;
		for(int i = begin;i<end;++i){
			if(part(program,i,i+2)=="if"){
				ifcnt++;
			}
			else if(part(program,i,i+4)=="else"){
				ifcnt--;
				if(ifcnt==0){
					correselse = i;
					break;
				}
			}
		}
		int case1 = ++last_used_label;
		int case2 = ++last_used_label;
		label_map[case1] = new CFG_location("det",case1);
		label_map[case2] = new CFG_location("det",case2);
		CFG_edge temporary_edge1(label_map[case1],1,id1);
		CFG_edge temporary_edge2(label_map[case2],1,id1);
		constant = "if";
		children.resize(3);
		children[0] = new node("ndbexpr",begin+2,firstthen);
		if(children[0]->constant=="prob"){
			label_map[s]->type = "prob";
			temporary_edge1.probability = stod(children[0]->children[0]->constant);
			label_map[s]->edges.pb(temporary_edge1);
			temporary_edge2.probability = 1.0 - temporary_edge1.probability;
			label_map[s]->edges.pb(temporary_edge2);
		}
		else if(children[0]->constant=="star"){
			label_map[s]->type = "ndet";
			label_map[s]->edges.pb(temporary_edge1);
			label_map[s]->edges.pb(temporary_edge2);
		}
		else{
			temporary_edge1.guard = children[0]->children[0]; //It is ndbexpr->bexpr
			temporary_edge2.guard = negation(children[0]->children[0]);
			label_map[s]->edges.pb(temporary_edge1);
			label_map[s]->edges.pb(temporary_edge2);
		}
		// cout<<"Adding edge from "<<s<<"to"<<case1<<endl;
		// cout<<"Adding edge from "<<s<<"to"<<case2<<endl;
		children[1]=new node("stmt",firstthen+4,correselse,case1,l);
		children[2]=new node("stmt",correselse+4,lastfi,case2,l);
		return;
	}

	//The statement is a assignment
	constant = "single assgn";
	children.resize(1);
	children[0] = new node("assgn",begin,end,s,l);
}

void node::proc_assgn(int s,int l){
	skip_spaces(begin,end);
	int pos = -1;
	for(int i = begin;i<end;++i){
		if(part(program,i,i+2)==":="){
			pos = i;
			break;
		}
	}
	if(pos==-1){
		cerr<<"Wrong assignment between ["<<begin<<","<<end<<")"<<endl;
	}
	else{
		children.resize(2);
		children[0] = new node("pvar",begin,pos);
		//Checking the sample() format
		int samplepos = pos+2;
		while(isspace(program[samplepos])){
			samplepos++;
		}
		if(part(program,samplepos,samplepos+6)=="sample"){
			int semicolon = -1;
			constant = "assignment from distribution";
			for(int i = samplepos+6;i<end;i++){
				if(program[i]==';'){
					semicolon = i;
					break;
				}
			}
			if(semicolon == -1){
				cerr<<"Mean value not found in the from distribution assignment between ["<<begin<<","<<end<<")"<<endl;
			}
			else{
				int temp = samplepos+6;
				while(temp<semicolon){
					if(program[temp]=='('){
						break;
					}
					temp++;
				}
				if(program[temp]!='('){
					cerr<<"Wrong assignment from distribution between ["<<begin<<","<<end<<")"<<endl;
				}
				temp++;
				while(isspace(program[temp]) and temp<semicolon){
					temp++;
				}
				constant = part(program,temp,semicolon); //Gives the distribution
				children[1] = new node("expr",semicolon+1,end-1); //Though it is just a constant but still storing it in an expression because of consistency
				label_map[s]->type = "det"; //<flag> Considering that it is just the same as assigning the variable the constant value
				CFG_edge temporary_edge(label_map[l],stoi(part(program,children[0]->begin+2,children[0]->end)),children[1]);
				label_map[s]->edges.pb(temporary_edge);
				// cout<<"Adding edge from "<<s<<"to"<<l<<endl;
				// cout<<label_map[l]<<endl;
			}
		}
		else{
			constant = "simple assignment";
			children[1] = new node("expr",pos+2,end); //rexpr is nothing but an expr, a expression
			label_map[s]->type = "det";
			CFG_edge temporary_edge(label_map[l],stoi(part(program,children[0]->begin+2,children[0]->end)),children[1]);
			label_map[s]->edges.pb(temporary_edge);
			// cout<<"Adding edge from "<<s<<"to"<<l<<endl;
			// cout<<label_map[l]<<endl;
		}
	}
}

void node::proc_affexpr(){
	constant = "and";
	skip_spaces(begin,end);
	int AND = -1;
	for(int i = begin+1;i<end-3;++i){
		if(part(program,i,i+3)=="and" and isspace(program[i-1]) and isspace(program[i+3])){
			AND = i;
			break;
		}
	}
	if(AND==-1){
		node* ch = new node("literal",begin,end);
		children.pb(ch);
	}
	else{
		node* ch = new node("literal",begin,AND);
		children.pb(ch);
		begin = AND + 3;
		proc_affexpr();
	}
}

void node::proc_pvar(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
}

void node::recursively_form_vector(int begin,int end){ //Note that this shadows the original ones
	skip_spaces(begin,end);
	int plusminus = -1;
	// Implemented as a linear but still recursive function
	for(int i = begin;i<end;++i){
		if(program[i]=='+' or program[i]=='-'){
			plusminus = i;
			break;
		}
	}
	if(plusminus!=-1){
		recursively_form_vector(begin,plusminus);
		recursively_form_vector(plusminus+1,end);
		return;
	}
	int lastdot = -1;
	for(int i=begin;i<end;++i){ //Assuming that the program variable names don't contain dot anywhere
		if(program[i]=='.' or program[i]=='*'){
			lastdot = i;
		}
	}
	if(lastdot==-1 and !isdigit(program[begin])){
		if(part(program,begin,begin+2)!="x_"){
			cerr<<"Error in the variable in ["<<begin<<","<<end<<") i.e.:"<<part(program,begin,end)<<endl;
		}
		expression[stoi(part(program,begin+2,end))]+=1.0;
		// children[0] = new node("pvar",begin,end);
		return;
	}
	if(program[lastdot]=='*' or !isdigit(program[lastdot+1])){
		int block=lastdot+1;
		skip_spaces(begin,lastdot);
		skip_spaces(block,end);
		if(part(program,block,block+2)!="x_"){
			cerr<<"Error in the variable in ["<<block<<","<<end<<")"<<endl;
		}
		expression[stoi(part(program,block+2,end))] += stod(part(program,begin,lastdot));
	}
	else{
		expression[0] += stod(part(program,begin,end));
		return;
	}
}

void node::proc_expr(){
	skip_spaces(begin,end);
	constant = "expression";
	expression.resize(nVariables+1);
	recursively_form_vector(begin,end);
}

void node::proc_constant(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
	if(constant[0]=='.'){
		constant="0"+constant;
	}
}

void node::proc_literal(){
	skip_spaces(begin,end);
	if(program[begin]=='~' or program[begin]=='!'){ //Assuming the sign for negation could be '!' or '~'
		constant = "not";
		children.resize(1);
		children[0] = new node("literal",begin+1,end);
		return;
	}
	int sign = -1;
	for(int i = begin;i<end-1;++i){
		if(part(program,i,i+2)=="<=" or part(program,i,i+2)==">="){
			sign = i;
			break;
		}
	}
	if(sign!=-1){
		constant=part(program,sign,sign+2);
		children.resize(2);
		children[0] = new node("expr",begin,sign);
		children[1] = new node("expr",sign+2,end);
	}
	else{
		cerr<<"Invalid literal between "<<begin<<" "<<end<<endl;
	}
}

void node::proc_bexpr(){
	constant = "or";
	skip_spaces(begin,end);
	int OR = -1;
	for(int i=begin+1;i<end-2;++i){
		if(part(program,i,i+2)=="or" and isspace(program[i-1]) and isspace(program[i+2])){
			OR = i;
			break;
		}
	}
	if(OR==-1){
		node* ch = new node("affexpr",begin,end);
		children.pb(ch);
	}
	else{
		node* ch = new node("affexpr",begin,OR);
		children.pb(ch);
		begin = OR+2;
		proc_bexpr();
	}
}

void node::proc_ndbexpr(){
	skip_spaces(begin,end);
	if(part(program,begin,end)=="*"){
		constant = "star";
		return;
	}
	if(part(program,begin,begin+4)=="prob"){
		constant = "prob";
		int open = -1,close = -1;
		for(int i=begin;i<end;++i){
			if(program[i]=='('){
				open = i;
			}
			else if(program[i]==')'){
				close = i;
				break;
			}
		}
		if(open==-1 or close==-1){
			cerr<<"Invalid probability"<<endl;
		}
		node* ch = new node("constant",open+1,close);
		children.pb(ch);
		return;
	}
	constant = "single bexpr";
	children.resize(1);
	children[0]=new node("bexpr",begin,end);
}

void node::process(int s, int l){
	if(type=="stmt"){
		proc_stmt(s,l);
	}
	else if(type=="affexpr"){
		proc_affexpr();
	}
	else if(type=="expr"){
		proc_expr();
	}
	else if(type=="bexpr"){
		proc_bexpr();
	}
	else if(type=="literal"){
		proc_literal();
	}
	else if(type=="ndbexpr"){
		proc_ndbexpr();
	}
	else if(type=="pvar"){
		proc_pvar();
	}
	else if(type=="constant"){
		proc_constant();
	}
	else if(type=="assgn"){
		proc_assgn(s,l);
	}
	else{
		cerr<<"Undefined type between "<<begin<<" "<<end<<endl<<part(program,begin,end)<<endl;
	}
}

node* root;

int find_variables(){
	set<string> variables;
	for(int i = 0;i<program.length()-1;i++){
		if(part(program,i,i+2)=="x_"){
			int variable_parser = i+2;
			while(isdigit(program[variable_parser])){
				variable_parser++;
			}
			string variable = part(program,i,variable_parser);
			variables.insert(variable);
		}
	}
	return variables.size();
}

void node::print(){
	cout<<"Add: "<<this<<"\t";
	cout<<"Type: "<<type<<"\t";
	cout<<"Range: ["<<begin<<", "<<end<<")\t";
	cout<<"Const: |"<<constant<<"|"<<endl;
	if(begin!=-1 and end!=-1 and begin<=end){
		cout<<"Text: "<<program.substr(begin, end-begin)<<endl;
	}
	if(type=="expr"){
		cout<<"Expression: ";
		if(expression[0]!=0.0){
			cout<<expression[0];
		}
		for(int i = 1;i<=nVariables;i++){
			if(expression[i]!=0.0){
				if(expression[i]>0.0){
					cout<<"+"<<expression[i]<<"*x_"<<i;
				}
				else{
					cout<<expression[i]<<"*x_"<<i;
				}
			}
		}
		cout<<endl;
	}
	cout<<"Children: ";
	for(int i = 0;i<children.size();++i){
		cout<<children[i]<<"\t";
	}
	if(bracket!=NULL){
		cout<<"Bracket: "<<bracket;
	}
	cout<<endl<<"--------------------"<<endl;
	for(int i=0;i<children.size();++i){
		children[i]->print();
	}
	if(bracket!=NULL){
		bracket->print();
	}
}

CFG_edge::CFG_edge(){
	guard = NULL;
	next = NULL;
	toChange = 0;
	change = NULL;
	probability = 1.0;
}

CFG_edge::CFG_edge(CFG_location* next1,int toChange1,node* change1,node* guard1,double probability1){
	next = next1;
	toChange = toChange1;
	change = change1;
	guard = guard1;
	probability = probability1;
}

void CFG_edge::print(){
	if(next!=NULL){
		cout<<"Destination: "<<next->label<<endl;
	}
	else{
		cout<<"Error! Error! Error!"<<endl;
	}
	if(toChange!=0){
		cout<<"Variable to be changed is x_"<<toChange<<endl;
	}
	// if(change!=NULL){
	// 	cout<<"Changed to: "<<endl;
	// 	// change->print();
	// }
	// if(guard!=NULL){
	// 	cout<<"Guard is: "<<endl;
	// 	// guard->print();
	// }
	cout<<"Probability to occur is"<<probability<<endl<<endl; 
}

CFG_location::CFG_location(string type,int label){
	this->label=label;
	this->type=type;
}

void CFG_location::print(){
	// cout<<"Label: "<<label<<endl;
	cout<<"Type: "<<type<<endl;
	// cout<<"Edges: "<<endl;
	int i=1;
	for(vector<CFG_edge>::iterator it = edges.begin();it!=edges.end();++it){
		cout<<"Edge #"<<i<<endl;
		it->print();
		i++;
	}
}

int main(){
	char input[MAXL];
	cout<<fixed<<setprecision(10);
	int r,i;
	for(i=0;(r=getchar())!=EOF;i++)
		input[i]=r;
	input[i]=0;
	program=input;
	nVariables = find_variables(); //To find the number of different variables of the type x_i in the program
	id1->constant = "expression";
	id1->expression.resize(nVariables+1);
	id1->expression[1] = 1.0;
	cout<<"Input Code:"<<endl;
	cout<<program<<endl;
	cout<<"Parse Tree:"<<endl;
	int start,end;
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	root=new node("stmt",0,program.length(),start,end);
	// root->print();
	cout<<"CFG:"<<endl;
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		cout<<"------------------------"<<endl;
		cout<<"Node "<<it->first<<endl;
		it->second->print();
		// cout<<it->second->label<<endl;
	}
	return 0;
}