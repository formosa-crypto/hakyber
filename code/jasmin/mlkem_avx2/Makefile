# -*- Makefile -*-


-include ../../Makefile.conf

CC     ?= /usr/bin/gcc
GFLAGS ?=
CFLAGS := -Wall -Wextra -g -Ofast -fomit-frame-pointer
JFLAGS := ${JADDFLAGS}
OS     := $(shell uname -s)

.SECONDARY: jpoly.s jpolyvec.s jfips202.s jindcpa.s jindcpa.o jkem.s

default: test speed

test: test/test_poly_compress \
      test/test_poly_decompress \
      test/test_poly_tobytes \
      test/test_poly_frombytes \
      test/test_poly_tomsg \
      test/test_poly_frommsg \
      test/test_poly_add2 \
      test/test_poly_sub \
      test/test_poly_ntt \
      test/test_poly_invntt \
      test/test_poly_basemul \
      test/test_poly_frommont \
      test/test_poly_reduce \
      test/test_poly_csubq \
      test/test_poly_getnoise \
      test/test_polyvec_compress\
      test/test_polyvec_decompress\
      test/test_polyvec_tobytes \
      test/test_polyvec_frombytes \
      test/test_polyvec_add2 \
      test/test_polyvec_ntt \
      test/test_polyvec_invntt \
      test/test_polyvec_pointwise_acc \
      test/test_polyvec_reduce\
      test/test_polyvec_csubq \
      test/test_fips202 \
	    test/test_indcpa \
	    test/test_kem

speed: test/speed_indcpa \
       test/speed_mlkem

HEADERS = params.h poly.h fips202.h ntt.h indcpa.h kem.h \

JHEADERS = params.jinc \
           reduce.jinc \
           fips202_common.jinc \
           fips202.jinc \
           fips202_4x.jinc \
           keccakf1600.jinc \
           consts.jinc \
           shuffle.jinc \
           indcpa.jinc \
           verify.jinc

POLYHEADERS = poly.jinc \
							consts.jinc \

POLYVECHEADERS = polyvec.jinc \
                 gen_matrix.jinc \

INCS    = fq.inc shuffle.inc
SOURCES = poly.c polyvec.c cbd.c fips202.c ntt.c reduce.c symmetric-fips202.c indcpa.c kem.c consts.c shuffle.S fq.S\

test/test_indcpa: test/test_indcpa.c $(HEADERS) $(SOURCES) $(INCS) jindcpa.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jindcpa.o $<

test/test_kem: test/test_kem.c $(HEADERS) $(SOURCES) $(INCS) jkem.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jkem.o ~/Desktop/Repos/jasmin/compiler/syscall/jasmin_syscall.o $<

test/speed_indcpa: test/speed_indcpa.c $(HEADERS) $(SOURCES) $(INCS) jindcpa.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jindcpa.o $<

test/speed_mlkem: test/speed_mlkem.c $(HEADERS) $(SOURCES) $(INCS) jspeed.s
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jspeed.s $<

test/test_fips202: test/test_fips202.c $(HEADERS) fips202.c jfips202.s
	$(CC) $(CFLAGS) -o $@ fips202.c jfips202.s $<

test/test_gen_matrix: test/test_gen_matrix.c $(HEADERS) gen_matrix.s
	$(CC) $(CFLAGS) -o $@ gen_matrix.s $<

test/test_poly_%: test/test_poly_%.c $(HEADERS) $(SOURCES) $(INCS) jpoly.s 
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jpoly.s $<

test/test_polyvec_%: test/test_polyvec_%.c $(HEADERS) $(SOURCES) $(INCS) jpolyvec.s
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jpolyvec.s $<

%.s: %.jazz
	$(JASMINC) -o $@ $(JFLAGS) $^

.PHONY: ct sct clean

ct:
	$(JASMINC) -checkCT -infer jkem.jazz

sct:
	$(JASMINC) -checkSCT jkem.jazz

clean:
	-rm -f *.o
	-rm -f gen_matrix.s
	-rm -f jindcpa.s
	-rm -f jkem.s
	-rm -f jfips202.s
	-rm -f jpoly.s
	-rm -f jpolyvec.s
	-rm -f jspeed.s
	-rm -f test/test_poly_compress
	-rm -f test/test_poly_decompress
	-rm -f test/test_poly_tobytes
	-rm -f test/test_poly_frombytes
	-rm -f test/test_poly_tomsg
	-rm -f test/test_poly_frommsg
	-rm -f test/test_poly_add2
	-rm -f test/test_poly_sub
	-rm -f test/test_poly_ntt
	-rm -f test/test_poly_invntt
	-rm -f test/test_poly_basemul
	-rm -f test/test_poly_frommont
	-rm -f test/test_poly_reduce
	-rm -f test/test_poly_csubq
	-rm -f test/test_poly_getnoise
	-rm -f test/test_polyvec_compress
	-rm -f test/test_polyvec_decompress
	-rm -f test/test_polyvec_tobytes
	-rm -f test/test_polyvec_frombytes
	-rm -f test/test_polyvec_add2
	-rm -f test/test_polyvec_ntt
	-rm -f test/test_polyvec_invntt
	-rm -f test/test_polyvec_pointwise_acc
	-rm -f test/test_polyvec_reduce
	-rm -f test/test_polyvec_csubq
	-rm -f test/test_fips202
	-rm -f test/test_gen_matrix
	-rm -f test/test_indcpa
	-rm -f test/test_kem
	-rm -f test/speed_indcpa
	-rm -f test/speed_mlkem
ifeq ($(OS),Darwin)
	-rm -r -f test/*.dSYM
endif
