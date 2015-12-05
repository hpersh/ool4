CFLAGS	= -g -pg
#CFLAGS	= -O3 -fomit-frame-pointer

all:	ool

ool: ool.c parse.c ool.h
	gcc $(CFLAGS) -o ool ool.c parse.c

.PHONY:	clean

clean:
	rm -f ool *.o *.so
