.PHONY: libkyber768_avx2v.a clean

libkyber768_avx2v.a: jkem.s
	$(CC) $(CFLAGS) -c jkem.s
	$(AR) -r $@ jkem.o

jkem.s: jkem.jazz
	jasminc -nowarning -lea $< -o $@

clean:
	rm -f *.s *.o *.a
