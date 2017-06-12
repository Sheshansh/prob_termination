Just compile the files by using 
$ make
The executable is a.out. To run use
./a.out < "name_of_program_file"
A sample program file is given with name program

Special conditions for the program:
1. The variables names are of the format x_<integer>.
2. Only allows start invariant, in square brackets at the beginning of the program. All other invariants are ignored. Also, the start invariant should be a polyhedra because of the reasons of aspic (Not yet made to do analysis for general start conditions)