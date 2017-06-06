g++ Parser.cpp main.cpp -std=c++11 -g
./a.out < program
/opt/ibm/ILOG/CPLEX_Studio_Community127/cplex/bin/x86-64_linux/cplex -c "read equations.lp" "optimize" "display solution variables *"
rm a.out
rm cplex.log
rm equations.lp