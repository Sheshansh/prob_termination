//Compile with C++11
//The variable names should be of the form x_i where i is a number and the indexing starts from 1 i.e. the variables in the program are of the form x_1, x_2 ... x_n.
//Assuming * is for multiplication rather than .
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
#include <stdlib.h>
#include "Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back

string program;
int nVariables;
int last_used_label = 0;
map<int,CFG_location*> label_map;
map<string,int> variableId;
map<int,string> variable;

void skip_spaces(int &begin, int &end){ //skips the spaces in the beginning and the end
	while(begin<program.size() and isspace(program[begin])){
		begin++;
	}
	while(end>0 and isspace(program[end-1])){
		end--;
	}
}

void skip_spaces(string& line){
	int begin = 0,end = line.length();
	while(begin<line.size() and isspace(line[begin])){
		begin++;
	}
	while(end>0 and isspace(line[end-1])){
		end--;
	}
	line = part(line,begin,end);
}

node::node(string t){
	bracket = NULL;
	begin = -1;
	end = -1;
	type = t;
	constant = "";
	strict = false;
}

node::node(string t, int b, int e, int s, int l, bool negate){
	bracket = NULL;
	type = t;
	begin = b;
	strict = false;
	end = e;
	skip_spaces(begin,end);
	if(begin>end){
		cerr<<"Error! begin= "<<b<<" end= "<<e<<endl;
	}
	process(s,l,negate);
}

node::node(string t, string l, bool& to_return){
	strict = false;
	type = t;
	if(t=="bexpr"){
		children.resize(1);
		children[0] = new node("affexpr");
		stringstream line_stream;
		line_stream.str(l);
		string comma_sep;
		while(getline(line_stream,comma_sep,',')){
			skip_spaces(comma_sep);
			bool return_value = false;
			node* formed_literal = new node("literal",comma_sep, return_value);
			children[0]->children.pb(formed_literal);
			if(return_value){
				node* other_literal = new node("literal");
				other_literal->constant = "<=";
				other_literal->children.resize(1);
				other_literal->children[0] = new node("expr");
				other_literal->children[0]->expression.resize(nVariables+1);
				for(int i=0;i<=nVariables;++i){
					other_literal->children[0]->expression[i] = -1.0*formed_literal->children[0]->expression[i];
				}
				children[0]->children.pb(other_literal);
				// formed_literal->print();
				// cout<<endl;
				// other_literal->print();
				// cout<<endl;

			}
		}
	}
	else if(t=="literal"){
		constant = "and";
		if(proc_literal(false,false,l)){
			to_return = true;
		}
	}
	else if(t=="expr"){
		constant = "expression";
		proc_expr(l);
	}
	else{
		cerr<<"Wrong usage"<<endl;
		return;
	}
	
}

void vcopy(vector<node*> &sink,vector<node*> &tocopy){
	sink.clear();
	int size = tocopy.size();
	sink.resize(size);
	for(int i=0;i<size;++i){
		sink[i] = new node(tocopy[i]->type);
		sink[i]->constant = tocopy[i]->constant;
		sink[i]->begin = tocopy[i]->begin;
		sink[i]->end = tocopy[i]->end;
		sink[i]->bracket = tocopy[i]->bracket;
		sink[i]->expression = tocopy[i]->expression;
		sink[i]->children = tocopy[i]->children;
	}
}

node* negation(node* tonegate){
	if(tonegate->type=="bexpr" and tonegate->constant=="or"){
		vector<node*> before_multiplication;
		node* negative;
		negative = new node("bexpr");
		negative->constant = "or";
		negative->children.resize(1);
		negative->children[0] = new node("affexpr");
		negative->children[0]->constant = "and";
		int ORs = tonegate->children.size();
		for(int i = 0;i<ORs;++i){
			//Multply this set of AND to the present collection
			vcopy(before_multiplication,negative->children);
			vector<node*> after_multiplication;
			int before_size = before_multiplication.size();
			negative->children.clear();
			int ANDs = tonegate->children[i]->children.size();
			for(int j = 0;j<ANDs;++j){
				node* ch = new node("literal");
				ch->constant = "<=";
				ch->children.resize(1);
				ch->children[0] = new node("expr");
				ch->children[0]->constant = "expression";
				ch->children[0]->expression.resize(nVariables+1);
				ch->strict = !(tonegate->children[i]->children[j]->strict);
				for(int k=0;k<=nVariables;++k){
					ch->children[0]->expression[k] = -1.0*tonegate->children[i]->children[j]->children[0]->expression[k];
				}
				vcopy(after_multiplication,before_multiplication);
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

void node::proc_stmt(int s,int l){
	
	// Code to add invariants manually at each node
	skip_spaces(begin,end);
	if(program[begin]=='['){
		int closed_bracket = -1;
		for(int j = begin+1;j<end;++j){
			if(program[j]==']'){
				closed_bracket = j;
				break;
			}
		}
		bracket = new node("bexpr",begin+1,closed_bracket);
		label_map[s]->invariant = bracket;
		begin = closed_bracket+1;
	}
	
	skip_spaces(begin,end);
	if(part(program,begin,end)=="skip"){
		constant = "skip";
		CFG_edge temporary_edge(label_map[l],-1,NULL);
		label_map[s]->edges.pb(temporary_edge);
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

	//look for brackets
	// Assuming the invariants are at the beginning itself
	skip_spaces(begin,end);
	

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
		CFG_edge temporary_edge1(label_map[mid],-1,NULL,children[0]);
		CFG_edge temporary_edge2(label_map[l],-1,NULL,temporary_node);
		label_map[s]->edges.pb(temporary_edge1);
		label_map[s]->edges.pb(temporary_edge2);
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
		CFG_edge temporary_edge1(label_map[case1],-1,NULL);
		CFG_edge temporary_edge2(label_map[case2],-1,NULL);
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
		cerr<<"Wrong assignment between ["<<begin<<","<<end<<") i.e. "<<part(program,begin,end)<<endl;
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
				CFG_edge temporary_edge(label_map[l],variableId[part(program,children[0]->begin,children[0]->end)],children[1]);
				label_map[s]->edges.pb(temporary_edge);
			}
		}
		else{
			constant = "simple assignment";
			children[1] = new node("expr",pos+2,end); //rexpr is nothing but an expr, a expression
			label_map[s]->type = "det";
			CFG_edge temporary_edge(label_map[l],variableId[part(program,children[0]->begin,children[0]->end)],children[1]);
			label_map[s]->edges.pb(temporary_edge);
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
		int begin_backup = begin;
		children.pb(ch);
		begin = AND + 3;
		proc_affexpr();
		begin = begin_backup;
	}
}

void node::proc_pvar(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
}

void node::analyse_expr(int begin,int end,bool negate){
	skip_spaces(begin,end);
	int star = -1;
	for(int i = begin;i<end;++i){ //Assuming that the program variable names don't contain star anywhere
		if(program[i]=='*'){
			star = i;
		}
	}
	if(star==-1){
		if(isdigit(program[begin])){
			if(negate){
				expression[0] -= stod(part(program,begin,end));
			}
			else{
				expression[0] += stod(part(program,begin,end));
			}
		}
		else{
			if(negate){
				expression[variableId[part(program,begin,end)]] -= 1.0;
			}
			else{
				expression[variableId[part(program,begin,end)]] += 1.0;
			}
		}
	}
	else{
		int block=star+1;
		skip_spaces(begin,star);
		skip_spaces(block,end);
		map<string, int>::iterator it = variableId.find(part(program,block,end));
		if(it==variableId.end()){
			cerr<<"Error in the variable in ["<<block<<","<<end<<")"<<"begin = "<<begin<<endl;
		}
		expression[it->second] += stod(part(program,begin,star));
	}
}

void node::analyse_expr(string l,bool negate){
	int x_pos = -1;
	for(int i = 0;i<l.length();++i){
		if(!isdigit(l[i]) and l[i]!='.'){
			x_pos = i;
			break;
		}
	}
	if(x_pos!=-1){
		if(x_pos==0){
			if(negate){
				expression[variableId[part(l,x_pos,l.length())]] -= 1.0;
			}
			else{
				expression[variableId[part(l,x_pos,l.length())]] += 1.0;
			}
		}
		else{
			if(negate){
				expression[0] -= stod(part(l,0,x_pos));
			}
			else{
				expression[0] += stod(part(l,0,x_pos));
			}
		}
	}
	else{
		if(negate){
			expression[0] -= stod(l);
		}
		else{
			expression[0] += stod(l);
		}
	}
}

void node::form_vector(int begin,int end,bool negate){ //Note that this shadows the original ones
	skip_spaces(begin,end);
	int plusminus = -1;
	// Implemented as a linear but still recursive function
	for(int i = begin+1;i<end;++i){
		if(program[i]=='+' or program[i]=='-'){
			plusminus = i;
			break;
		}
	}
	if(plusminus!=-1){
		analyse_expr(begin,plusminus,negate);
		form_vector(plusminus+1,end,program[plusminus]=='-');
	}
	else{
		analyse_expr(begin,end,negate);
	}
}

void node::form_vector(string l,bool negate){
	skip_spaces(l);
	int plusminus = -1;
	// Implemented as a linear but still recursive function
	for(int i = 1;i<l.length();++i){
		if(l[i]=='+' or l[i]=='-'){
			plusminus = i;
			break;
		}
	}
	if(plusminus!=-1){
		analyse_expr(part(l,0,plusminus),negate);
		form_vector(part(l,plusminus+1,l.length()),l[plusminus]=='-');
	}
	else{
		analyse_expr(l,negate);
	}
}

void node::proc_expr(){
	skip_spaces(begin,end);
	constant = "expression";
	expression.resize(nVariables+1);
	form_vector(begin,end,false);
}

void node::proc_expr(string l){
	skip_spaces(l);
	expression.resize(nVariables+1);
	form_vector(l,false);
}

void node::proc_constant(){
	skip_spaces(begin,end);
	constant = part(program,begin,end);
	if(constant[0]=='.'){
		constant="0"+constant;
	}
}

bool node::proc_literal(bool negate,bool strategic, string line){
	bool to_return = false;
	if(strategic){
		skip_spaces(begin,end);
		if(program[begin]=='~' or program[begin]=='!'){ //Assuming the sign for negation could be '!' or '~'
			begin = begin+1;
			proc_literal(!negate);
			return to_return;
		}
		int sign = -1;
		for(int i = begin;i<end-1;++i){
			if(program[i]=='<' or program[i]=='>'){
				sign = i;
				break;
			}
		}
		if(sign==-1){
			cerr<<"Invalid literal between "<<begin<<" "<<end<<endl;
		}
		else{
			if(program[sign+1]=='='){
				if(!negate){
					constant=part(program,sign,sign+2);
				}
				else{
					if(part(program,sign,sign+2)==">="){
						constant = "<=";
					}
					else{
						constant = ">=";
					}
				}
				children.resize(2);
				children[0] = new node("expr",begin,sign);
				children[1] = new node("expr",sign+2,end);
			}
			else{
				strict = true;
				if(!negate){
					if(program[sign]=='>'){
						constant = ">=";
					}
					else{
						constant = "<=";
					}
				}
				else{
					if(program[sign]=='>'){
						constant = "<=";
					}
					else{
						constant = ">=";
					}
				}
				children.resize(2);
				children[0] = new node("expr",begin,sign);
				children[1] = new node("expr",sign+1,end);
			}
		}
	}
	else{
		int sign = -1;
		for(int i=0;i<line.length()-1;++i){
			if(line[i]=='<' or line[i]=='>' or line[i]=='='){
				sign = i;
				break;
			}
		}
		children.resize(2);
		bool temp;
		children[0] = new node("expr",part(line,0,sign),temp);
		if(sign==-1){
			cerr<<"Invalid literal";
		}
		else if(part(line,sign,sign+2)==">="){
			constant = ">=";
			children[1] = new node("expr",part(line,sign+2,line.length()),temp);
		}
		else if(part(line,sign,sign+2)=="<="){
			constant = "<=";
			children[1] = new node("expr",part(line,sign+2,line.length()),temp);
		}
		else if(line[sign]=='>'){
			constant = ">=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
		}
		else if(line[sign]=='<'){
			constant = "<=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
		}
		else{
			constant = "<=";
			children[1] = new node("expr",part(line,sign+1,line.length()),temp);
			to_return = true;
		}
	}

	if(constant=="<="){
		for(int i=0;i<=nVariables;i++){
			children[0]->expression[i] = children[0]->expression[i]-children[1]->expression[i];
			children[1]->expression[i] = 0;
		}
	}
	else{
		constant = "<=";
		for(int i=0;i<=nVariables;i++){
			children[0]->expression[i] = children[1]->expression[i]-children[0]->expression[i];
		}
	}
	delete children[1];
	children.resize(1);
	return to_return;
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
		int begin_backup = begin;
		begin = OR+2;
		proc_bexpr();
		begin = begin_backup;
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

void node::process(int s, int l, bool negate){
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
		proc_literal(negate);
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

int find_variables(int& begin, int &end){
	int toReturn = 0;
	if(part(program,begin,begin+3)!="var"){
		cerr<<"No variables specified"<<endl;
		exit(0);
	}
	int semicolon = -1;
	for(int i=begin;i<end;i++){
		if(program[i]==';'){
			semicolon = i;
			break;
		}
	}
	if(semicolon==-1){
		cerr<<"No semicolon in program";
		exit(0);
	}
	istringstream ss(part(program,begin+3,semicolon));
	string token;
	while(getline(ss,token,',')){
		skip_spaces(token);
		toReturn++;
		variable[toReturn] = token;
		variableId[token] = toReturn;
	}
	begin = semicolon+1;
	return toReturn;
}

void node::print(ostream& outputfile, string and_string, string or_string, string multiply_string, bool bruteforce){
	if(type=="expr"){
		bool something_printed = false;
		if(expression[0]!=0.0){
			outputfile<<expression[0];
			something_printed = true;
		}
		for(int i = 1;i<=nVariables;i++){
			if(expression[i]!=0.0){
				if(expression[i]>0.0){
					if(something_printed==true){
						outputfile<<"+"<<expression[i]<<multiply_string<<variable[i];
					}
					else{
						outputfile<<expression[i]<<multiply_string<<variable[i];
					}
					something_printed = true;
				}
				else{
					outputfile<<expression[i]<<multiply_string<<variable[i];
					something_printed = true;
				}
			}
		}
		if(!something_printed){
			outputfile<<"0";
		}
		return;
	}
	else if(type=="literal"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		if(strict and bruteforce){
			if(constant=="<="){
				outputfile<<"<0";
			}
			else{
				outputfile<<">0";				
			}
		}
		else{
			outputfile<<constant<<"0";
		}
		return;
	}
	else if(type=="affexpr"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		for(int i=1;i<children.size();++i){
			outputfile<<" "<<and_string<<" ";
			children[i]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		return;
	}
	else if(type=="bexpr"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		for(int i=1;i<children.size();++i){
			outputfile<<" "<<or_string<<" ";
			children[i]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		return;
	}
	else if(type=="ndbexpr"){
		if(constant=="single bexpr"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else{
			// <flag>
		}
	}
	else if(type=="stmt"){
		if(constant=="skip"){
			// Do nothing
		}
		else if(constant=="several statements"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<endl;
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else if(constant=="while"){
			outputfile<<"while(";
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"){\n\n";
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}";
		}
		else if(constant=="if"){
			outputfile<<"if(";
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"){\n\n";
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}\nelse{\n\n";
			children[2]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			outputfile<<"\n}";
		}
		else if(constant=="single assgn"){
			children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
			cout<<";\n";
		}
		else{
			cerr<<"Wrong constant in statement node\n";
		}
	}
	else if(type=="assgn"){
		children[0]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		outputfile<<" = ";
		if(constant=="assignment from distribution"){
			// <flag>
		}
		else if(constant=="simple assignment"){
			children[1]->print(outputfile,and_string,or_string,multiply_string,bruteforce);
		}
		else{
			cerr<<"Some wrong constant type in assignment\n";
		}
	}
	else if(type=="pvar" || type=="constant"){
		outputfile<<constant;
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
	if(change!=NULL){
		cout<<"Change: x_"<<toChange<<" changed to ";
		change->print();
		cout<<endl;
	}
	if(guard!=NULL){
		cout<<"Guard is: "<<endl;
		guard-> print();
	}
	cout<<"Probability to occur is"<<probability<<endl<<endl; 
}

CFG_location::CFG_location(string type,int label){
	this->label = label;
	this->type = type;
	invariant = NULL;
}

void CFG_location::print(){
	cout<<"Type: "<<type<<endl;
	if(invariant!=NULL){
		cout<<"Invariant: ";
		cout<<invariant<<" : ";
		invariant->print();
		cout<<endl;
	}

	int i=1;
	for(vector<CFG_edge>::iterator it = edges.begin();it!=edges.end();++it){
		cout<<"Edge #"<<i<<endl;
		it->print();
		i++;
	}
}