# The script would differ based on the installation directory of cplex
# This is the path to the executable of CPLEX followed by proper arguments needed
/opt/ibm/ILOG/CPLEX_Studio1271/cplex/bin/x86-64_linux/cplex -c "read files/equations.lp" "optimize" "display solution variables *" > files/EquationsOutput
# Awk script for trimming EquationsOutput
awk 'BEGIN {x=0} /^CPLEX>/{x++} x==3{print}' < files/EquationsOutput > EquationsOutput.tmp
mv EquationsOutput.tmp files/EquationsOutput
rm cplex.log