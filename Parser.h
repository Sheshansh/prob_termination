#include <string>
using namespace std;

struct node{
	string type; //The type of entity that this node corresponds to
	string constant; //The constant factor (subtype) of this node
	int begin,end; //begin and end point in program
	vector<node *> children; //children in the parse tree
	node *bracket; //bexpr written in bracket next to this node (for stmt only)
	vector<double> expression; //for expressions only
	//constructor
	node(string t);
	node(string t, int b, int e, int s = 0, int l = 0);
private:
//procs
	void proc_stmt(int s,int l);
	void proc_assgn();
	void proc_affexpr();
	void proc_pvar();
	void recursively_form_vector(int begin,int end);
	void proc_expr();
	void proc_constant();
	void proc_literal();
	void proc_bexpr();
	void proc_ndbexpr();
//main process
	void process(int s, int l);
public:
	void print();
};

struct CFG_location;

struct CFG_edge{
	CFG_location* next;
	int toChange;
	node* change; // An expr node
	node* guard; // A bexpr node
	double probability;
	CFG_edge();
	CFG_edge(CFG_location* next,int toChange,node* change,node* guard=NULL,double probability=0);
};

struct CFG_location{
	int label;
	string type; //Deterministic == true and non-deterministic == false #convention
	vector<CFG_edge> edges;
	CFG_location(string type,int label);
};