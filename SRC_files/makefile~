# Examples/makefile
# James S. Plank
# 
# JERASURE - Library for Erasure Coding
# Copright (C) 2007 James S. Plank
# 
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2.1 of the License, or (at your option) any later version.
# 
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
# 
# James S. Plank
# Department of Computer Science
# University of Tennessee
# Knoxville, TN 37996
# plank@cs.utk.edu

# $Revision: 1.2 $
# $Date: 2008/08/19 17:41:40 $

CC = gcc
CFLAGS = -g -I$(HOME)/include

ALL =	decoder \
	encoder\
	SRC\
	SRC_repair\
	SRC_decoder
all: $(ALL)

clean:
	rm -f core *.o $(ALL) a.out cauchy.h cauchy.c liberation.h liberation.c reed_sol.c reed_sol.h\
              jerasure.c jerasure.h galois.c galois.h

.SUFFIXES: .c .o
.c.o:
	$(CC) $(CFLAGS) -c $*.c

liberation.h: ../liberation.h
	rm -f liberation.h ; cp ../liberation.h . ; chmod 0444 liberation.h

liberation.c: ../liberation.c
	rm -f liberation.c ; cp ../liberation.c . ; chmod 0444 liberation.c

cauchy.h: ../cauchy.h
	rm -f cauchy.h ; cp ../cauchy.h . ; chmod 0444 cauchy.h

cauchy.c: ../cauchy.c
	rm -f cauchy.c ; cp ../cauchy.c . ; chmod 0444 cauchy.c

reed_sol.h: ../reed_sol.h
	rm -f reed_sol.h ; cp ../reed_sol.h . ; chmod 0444 reed_sol.h

reed_sol.c: ../reed_sol.c
	rm -f reed_sol.c ; cp ../reed_sol.c . ; chmod 0444 reed_sol.c

jerasure.h: ../jerasure.h
	rm -f jerasure.h ; cp ../jerasure.h . ; chmod 0444 jerasure.h

jerasure.c: ../jerasure.c
	rm -f jerasure.c ; cp ../jerasure.c . ; chmod 0444 jerasure.c

galois.h: ../galois.h
	rm -f galois.h ; cp ../galois.h . ; chmod 0444 galois.h

galois.c: ../galois.c
	rm -f galois.c ; cp ../galois.c . ; chmod 0444 galois.c

galois.o: galois.h 
jerasure.o: jerasure.h galois.h


decoder.o: galois.h liberation.h jerasure.h reed_sol.h cauchy.h
decoder: decoder.o galois.o jerasure.o liberation.o reed_sol.o cauchy.o
	$(CC) $(CFLAGS) -o decoder decoder.o liberation.o jerasure.o galois.o reed_sol.o cauchy.o
	
encoder.o: galois.h liberation.h jerasure.h reed_sol.h cauchy.h
encoder: encoder.o galois.o jerasure.o liberation.o reed_sol.o cauchy.o
	$(CC) $(CFLAGS) -o encoder encoder.o liberation.o jerasure.o galois.o reed_sol.o cauchy.o
	

SRC.o: galois.h liberation.h jerasure.h reed_sol.h cauchy.h
SRC: SRC.o galois.o jerasure.o liberation.o reed_sol.o cauchy.o
	$(CC) $(CFLAGS) -o SRC SRC.o liberation.o jerasure.o galois.o reed_sol.o cauchy.o

SRC_repair.o: galois.h liberation.h jerasure.h reed_sol.h cauchy.h
SRC_repair: SRC_repair.o galois.o jerasure.o liberation.o reed_sol.o cauchy.o
	$(CC) $(CFLAGS) -o SRC_repair SRC_repair.o liberation.o jerasure.o galois.o reed_sol.o cauchy.o
	
SRC_decoder.o: galois.h liberation.h jerasure.h reed_sol.h cauchy.h
SRC_decoder: SRC_decoder.o galois.o jerasure.o liberation.o reed_sol.o cauchy.o
	$(CC) $(CFLAGS) -o SRC_decoder SRC_decoder.o liberation.o jerasure.o galois.o reed_sol.o cauchy.o
		
