./files/aspicV3.4 files/aspic.fast > files/InvariantOutput
awk 'BEGIN {x=0} /^"*** Results :"/{x=1} x==1{print}' < files/InvariantOutput > InvariantOutput.tmp
mv InvariantOutput.tmp files/InvariantOutput
rm aspic.log