## Setup

Download all the files.
Most of the neccessary tools are included (the main tool, and the invariant generator binary, downloaded from aspic website) except for CPLEX because of memory occupied by CPLEX. Make sure that you use the full version. Otherwise it poses unnecessary constraints.
The code calls the script implementation/files/script.sh to execute CPLEX. So, change the address of cplex executable in script.sh from "/opt/ibm/ILOG/CPLEX_Studio1271/cplex/bin/x86-64_linux/cplex" to whatever it is on the machine you want to run this tool on.

## How to Run
Just compile the files by using 
$ make
The executable is a.out. To run use
./a.out < "path_of_program_file"
The folder "examples" contains many examples used during development.

Program format/Things to note:
1. Declare all the variables in the beginning of the program as
 var <variable-1>, <variable-2>, ...;
2. After variable declaration, write the program in the format described in the paper. But, for assignment from distribtion, the syntax is "[lower_bound,upper_bound]". Ex: "x:=x+[-1,1]".
3. The invariants if provided, maually should be put in before the statements in square brackets. The invariant provided at start is particularly useful because it is provided into the invariant generation tool and hence can propagate to other nodes in the pCFG as well.
4. The code calls the implementation/files/invariant_script.sh to call the invariant generator executable i.e. aspic. Sometimes changing the delay and descend paramters help in finding out the LexRSM in this tool. Use aspic help to know usage. Or read its documentation.
