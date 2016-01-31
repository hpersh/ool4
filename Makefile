CFLAGS	= -g
#CFLAGS	= -g -pg
#CFLAGS	= -O3 -fomit-frame-pointer

all:	ool process.so

ool: ool.c parse.c ool.h
	gcc $(CFLAGS) -Wl,-export-dynamic -o ool ool.c parse.c -ldl

process.so: process.c ool.h
	gcc -c $(CFLAGS) -fPIC process.c
	gcc -shared -o process.so process.o

test:
	gcc ool.c parse.c process.c -ldl

.PHONY:	clean

clean:
	rm -f ool *.o *.so
