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

stack<equation> equations;

void generate_equations(ofstream& equationsfile){ //Would use the ofstream file to write the equations into it later
	for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
		if(it->second->type=="det"){
			//Invariant and guard imply the value decrease
			// if()
		}
		else if(it->second->type=="ndet"){
			//Invariant and implies the value decrease for both
		}
		else{
			//Invariant implies the value decrease of expected value of ranking function
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