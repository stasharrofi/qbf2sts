CC	= g++
CFLAGS	= -O3 -std=c++11
#CFLAGS	= -O0 -std=c++11
LFLAGS	= -static
OBJS	= main.o core.o layeredqbf.o qbfprogram.o stsmodule.o utils.o io.o
DEPS	= core.h io.h layeredqbf.h qbfprogram.h stsmodule.h utils.h

qbf2sts:	$(OBJS)
		$(CC) $(CFLAGS) $^ $(LFLAGS) -o $@
%.o:		%.cc $(DEPS)
		$(CC) $(CFLAGS) -c -o $@ $<
clean:
		rm qbf2sts *.o
