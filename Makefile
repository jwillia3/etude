test: ml
	./ml test.ml

ml: ml.c
	$(CC) -oml -g -Wall -Wno-dangling-else -Wno-parentheses ml.c
