Just compile the files by using 
$ make
The executable is a.out. To run use
./a.out < "name_of_program_file"
A sample program file is given with name program

Conditions for using the tool:
1. Declare all the variables in the beginning of the program as
 var <variable-1>, <variable-2>, ...;
2. Start invariant is taken as the start condition for the program and propogated though the invariant genration tool aspic, all other invariants are taken conjuncts with the invariants generated. To declare invariant put it in [square brackets] at the relevant point in the program.