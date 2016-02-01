CFLAGS	= -g
#CFLAGS	= -g -pg
#CFLAGS	= -O3 -fomit-frame-pointer

all:	ool math.so process.so

ool: ool.c parse.c ool.h
	gcc $(CFLAGS) -Wl,-export-dynamic -o ool ool.c parse.c -ldl

math.so: math.c ool.h
	gcc -c $(CFLAGS) -fPIC math.c
	gcc -shared -o math.so math.o -lm

process.so: process.c ool.h
	gcc -c $(CFLAGS) -fPIC process.c
	gcc -shared -o process.so process.o

test:
	gcc ool.c parse.c process.c -ldl

.PHONY:	clean

clean:
	rm -f ool *.o *.so
