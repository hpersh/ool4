CC_CLANG	= clang
CC_GCC		= gcc

#CFLAGS_ALL	= -Wall -Wno-logical-op-parentheses
CFLAGS_SHARED	= -fPIC
CFLAGS_DEBUG	= -g
CFLAGS_PROFILE	= -pg -O3 -DNDEBUG
CFLAGS_OPT	= -O3 -fomit-frame-pointer -DNDEBUG

CC	= $(CC_GCC)
CFLAGS	= $(CFLAGS_ALL) $(CFLAGS_DEBUG)

all:	ool math.so process.so socket.so net.so

ool: ool.c parse.c ool.h
	$(CC) $(CFLAGS) -Wl,-export-dynamic -o ool ool.c parse.c -ldl

math.so: math.c ool.h
	$(CC) -c $(CFLAGS) $(CFLAGS_SHARED) math.c
	$(CC) -shared -o math.so math.o -lm

%.so: %.c ool.h
	$(CC) -c $(CFLAGS) $(CFLAGS_SHARED) $<
	$(CC) -shared -o $@ $*.o

test:
	$(CC) ool.c parse.c net.c -ldl

.PHONY:	clean

clean:
	rm -f ool *.o *.so *~
