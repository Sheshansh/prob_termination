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
#include "Parser.h"
using namespace std;
#define MAXL 100000 //Maximum length of the program
#define part(x,a,b) (x.substr((a),((b)-(a))))
#define pb push_back
#define make_edge(a,b,c) edge((int*)(a),(int*)(b),(c))
#define mp make_pair

void generate_equations(ofstream& equationsfile){
	
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
	// cout<<"Input Code:"<<endl;
	// cout<<program<<endl;
	// cout<<"Parse Tree:"<<endl;
	int start,end;
	start = ++last_used_label;
	end = ++last_used_label;
	label_map[start] = new CFG_location("det",start);
	label_map[end]	 = new CFG_location("det",end);
	root=new node("stmt",0,program.length(),start,end);
	// root->print();
	// cout<<"CFG:"<<endl;
	// for(map<int,CFG_location*>::iterator it = label_map.begin();it!=label_map.end();++it){
	// 	cout<<"------------------------"<<endl;
	// 	cout<<"Node "<<it->first<<endl;
	// 	it->second->print();
	// 	// cout<<it->second->label<<endl;
	// }
	ofstream equationsfile;
	equationsfile.open ("equations.txt");
	generate_equations(equationsfile);
	equationsfile.close();
	return 0;
}