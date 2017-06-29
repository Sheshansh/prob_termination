all:
	g++ files/Parser.cpp main.cpp -std=c++11 -g
wrapper: files/Parser.cpp files/Parser.h c_wrapper.cpp
	g++ files/Parser.cpp c_wrapper.cpp -std=c++11 -g -o wrapper
large: files/Parser.cpp files/Parser.h large_ifs.cpp
	g++ files/Parser.cpp large_ifs.cpp -std=c++11 -g -o large_ifs