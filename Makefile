CC_CLANG	= clang -Wall -Wno-logical-op-parentheses
CC_GCC		= gcc -Wall -Wno-parentheses

CFLAGS_DEBUG	= -g
CFLAGS_PROFILE	= -pg -O3 -DNDEBUG
CFLAGS_OPT	= -O3 -fomit-frame-pointer -DNDEBUG

CC_DEBUG	= $(CC_GCC) $(CFLAGS_DEBUG)
CC_OPT		= $(CC_CLANG) $(CFLAGS_OPT)

CC	= $(CC_DEBUG)

all:	ool math.so process.so socket.so net.so

ool: ool.c parse.c ool.h
	$(CC) $(CFLAGS) -Wl,-export-dynamic -o ool ool.c parse.c -ldl

math.so: math.c ool.h
	$(CC) -c $(CFLAGS) -fPIC math.c
	$(CC) -shared -o math.so math.o -lm

process.so: process.c ool.h
	$(CC) -c $(CFLAGS) -fPIC process.c
	$(CC) -shared -o process.so process.o

socket.so: socket.c ool.h
	$(CC) -c $(CFLAGS) -fPIC socket.c
	$(CC) -shared -o socket.so socket.o

net.so: net.c ool.h
	$(CC) -c $(CFLAGS) -fPIC net.c
	$(CC) -shared -o net.so net.o

test:
	$(CC) ool.c parse.c net.c -ldl

.PHONY:	clean

clean:
	rm -f ool *.o *.so *~
