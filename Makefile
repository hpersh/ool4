CFLAGS_DEBUG	= -g
CFLAGS_PROFILE	= -pg -O3 -DNDEBUG
CFLAGS_OPT	= -O3 -fomit-frame-pointer -DNDEBUG

CFLAGS	= $(CFLAGS_OPT)

all:	ool math.so process.so socket.so net.so

ool: ool.c parse.c ool.h
	gcc $(CFLAGS) -Wl,-export-dynamic -o ool ool.c parse.c -ldl

math.so: math.c ool.h
	gcc -c $(CFLAGS) -fPIC math.c
	gcc -shared -o math.so math.o -lm

process.so: process.c ool.h
	gcc -c $(CFLAGS) -fPIC process.c
	gcc -shared -o process.so process.o

socket.so: socket.c ool.h
	gcc -c $(CFLAGS) -fPIC socket.c
	gcc -shared -o socket.so socket.o

net.so: net.c ool.h
	gcc -c $(CFLAGS) -fPIC net.c
	gcc -shared -o net.so net.o

test:
	gcc ool.c parse.c net.c -ldl

.PHONY:	clean

clean:
	rm -f ool *.o *.so *~
