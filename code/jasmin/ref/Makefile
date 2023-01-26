CC?=/usr/bin/gcc
CFLAGS=-Wall -Wextra -g -O3 -fomit-frame-pointer
JASMIN?=jasminc
JFLAGS=-lea ${JADDFLAGS}
OS = $(shell uname -s)

.SECONDARY: jpoly.s jpolyvec.s jfips203.s jindcpa.s jkem.s

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

speed: test/speed_indcpa

HEADERS = params.h poly.h fips202.h kem.h


JHEADERS = params.jinc \
				   reduce.jinc \
           fips202.jinc \
					 kem.jinc \
					 verify.jinc

POLYHEADERS = poly.jinc \
							zetas.jinc \

POLYVECHEADERS = polyvec.jinc \
                 gen_matrix.jinc \

SOURCES = poly.c polyvec.c cbd.c fips202.c ntt.c reduce.c symmetric-fips202.c indcpa.c kem.c \

test/test_indcpa: test/test_indcpa.c $(HEADERS) $(SOURCES) jindcpa.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jindcpa.o $<

test/test_kem: test/test_kem.c $(HEADERS) $(SOURCES) $(INCS) jkem.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jkem.o $<

test/speed_indcpa: test/speed_indcpa.c $(HEADERS) $(SOURCES) jindcpa.o
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jindcpa.o $<

test/test_fips202: test/test_fips202.c $(HEADERS) $(SOURCES) jfips202.s
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jfips202.s $<

test/test_poly_%: test/test_poly_%.c $(HEADERS) $(SOURCES) jpoly.s
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jpoly.s $<

test/test_polyvec_%: test/test_polyvec_%.c $(HEADERS) $(SOURCES) jpolyvec.s
	$(CC) $(CFLAGS) -o $@ $(SOURCES) jpolyvec.s $<

%.s: %.jazz
	$(JASMIN) -o $@ $(JFLAGS) $^ 


.PHONY: clean ct

ct:
	$(JASMIN) -checkCT -infer jkem.jazz

clean:
	-rm -f *.s
	-rm -f jindcpa.o
	-rm -f jkem.o
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
	-rm -f test/test_indcpa
	-rm -f test/test_kem
	-rm -f test/speed_indcpa
ifeq ($(OS),Darwin)
	-rm -rf test/*.dSYM
endif
