#include <string>
using namespace std;

struct node{
	string type; //The type of entity that this node corresponds to
	string constant; //The constant factor (subtype) of this node
	bool strict;
	int begin,end; //begin and end point in program
	vector<node *> children; //children in the parse tree
	node *bracket; //bexpr written in bracket next to this node (for stmt only)
	vector<double> expression; //for expressions only
	double delta;
	//constructor
	node(string t);
	node(string t, int b, int e, int s = 0, int l = 0, bool negate = false);
	node(string t, string line, bool& to_return);
private:
//procs
	void proc_stmt(int s,int l);
	void proc_assgn(int s,int l);
	void proc_affexpr(); //
	void proc_pvar();
	void analyse_expr(int begin,int end,bool negate);
	void analyse_expr(string l,bool negate);
	void proc_expr(); //
	void proc_expr(string l); //
	void proc_constant();
	bool proc_literal(bool negate, bool strategic = true, string line = "");
	void proc_bexpr(); //
	void proc_ndbexpr();
	void form_vector(int begin,int end,bool negate);
	void form_vector(string l,bool negate);
//main process
	void process(int s, int l, bool negate);
public:
	void print(ostream& outputfile = cout,string and_string = "and", string or_string = "or", string multiply_string = "", bool bruteforce = false);
};

struct CFG_location;

struct CFG_edge{
public:
	CFG_location* next;
	int toChange;
	node* change; // An expr node
	node* guard; // A bexpr node
	double probability;
	CFG_edge();
	CFG_edge(CFG_location* next,int toChange,node* change,node* guard=NULL,double probability=1.0);
	void print();
};

struct CFG_location{
public:
	int label;
	string type; // det ndet and prob
	vector<CFG_edge> edges;
	CFG_location(string type,int label);
	vector<int> ranking_function;
	node* invariant; // A bexpr node
	void print();
};

void skip_spaces(int &begin, int &end);
void vcopy(vector<node*> &sink,vector<node*> &tocopy);
node* negation(node* tonegate);
node* and_node(node* one,node* two);
int find_variables(int& begin, int& end);

extern string program;
extern int nVariables;
extern int last_used_label;
extern map<int,CFG_location*> label_map;
extern node* root;
extern map<string,int> variableId;
extern map<int,string> variable;
extern int dummy_states_needed; //For adding the if * condition in fast file