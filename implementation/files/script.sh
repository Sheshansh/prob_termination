/opt/ibm/ILOG/CPLEX_Studio_Community127/cplex/bin/x86-64_linux/cplex -c "read equations.lp" "optimize" "display solution variables *" > EquationsOutput
awk 'NR > 27 { print }' < EquationsOutput > EquationsOutput.tmp
cp EquationsOutput.tmp EquationsOutput
rm EquationsOutput.tmp