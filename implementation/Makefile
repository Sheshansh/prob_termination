all:
	g++ files/Parser.cpp main.cpp -std=c++11 -g
wrapper: files/Parser.cpp c_wrapper.cpp
	g++ files/Parser.cpp c_wrapper.cpp -std=c++11 -g -o wrapper