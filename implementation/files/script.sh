/opt/ibm/ILOG/CPLEX_Studio_Community127/cplex/bin/x86-64_linux/cplex -c "read files/equations.lp" "optimize" "display solution variables *" > files/EquationsOutput
# Awk script for trimming EquationsOutput
awk 'BEGIN {x=0} /^CPLEX>/{x++} x==3{print}' < files/EquationsOutput > EquationsOutput.tmp
cp EquationsOutput.tmp files/EquationsOutput
rm EquationsOutput.tmp
rm cplex.log