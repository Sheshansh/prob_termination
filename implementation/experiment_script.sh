for file in examples/ForExperiments/*
do
	echo "$file" >> Output
	echo ", " >> Output
	wc -l "$file" >> Output
	echo ", " >> Output
	./a.out < "$file" >> Output
	
done