int aaron12() {
	int x,y,z;

	while (x>=y) {
		if (nondet()) {
			x=x+1;
			y=y+x;


		} else {
			x=x-z;
			y=y+(z*z); // Breakage point
			z=z-1;

		}


	}
	return 0;



}
