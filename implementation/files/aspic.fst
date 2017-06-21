model main{

	var tx, x, y;

	states state_1, state_2, state_3, state_4, state_5, state_6, state_7, state_8;

	transition t_1_0 := {
		from	 := state_1;
		to	:= state_3;
		guard	:= true;
		action	:= ;
	};

	transition t_3_0 := {
		from	:= state_3;
		to	:= state_4;
		guard	:= -1tx<=0 && -1x+1y<0;
		action	:= ;
	};

	transition t_3_1 := {
		from	:= state_3;
		to	:= state_5;
		guard	:= 1tx<0 || 1x-1y<=0;
		action	:= ;
	};

	transition t_4_0 := {
		from	:= state_4;
		to	:= state_6;
		guard	:= -1x+1y<=0 && -1tx<=0;
		action	:= ;
	};

	transition t_4_1 := {
		from	:= state_4;
		to	:= state_2;
		guard	:= 1x-1y<0 || 1tx<0;
		action	:= ;
	};

	transition t_5_0 := {
		from	:= state_5;
		to	:= state_2;
		guard	:= true;
		action	:= ;
	};

	transition t_6_0 := {
		from	:= state_6;
		to	:= state_7;
		guard	:= true;
		action	:= ;
	};

	transition t_6_1 := {
		from	:= state_6;
		to	:= state_8;
		guard	:= true;
		action	:= ;
	};

	transition t_7_0 := {
		from	:= state_7;
		to	:= state_4;
		guard	:= true;
		action	:= x' = -1-1tx+1x;
	};

	transition t_8_0 := {
		from	:= state_8;
		to	:= state_4;
		guard	:= true;
		action	:= y' = 1+1tx+1y;
	};

}

strategy main_s{

	Region init := {state = state_1 && true};

}
// Result of Analysis  
//invariant state_1 := true ;
//invariant state_2 := true ;
//invariant state_3 := true ;
//invariant state_4 := tx>=0 ;
//invariant state_5 := true ;
//invariant state_6 := x>=y && tx>=0 ;
//invariant state_7 := x>=y && tx>=0 ;
//invariant state_8 := x>=y && tx>=0 ;
