.PHONY: libkyber768_avx2.a clean

libkyber768_avx2.a: jkem.s
	$(CC) $(CFLAGS) -c jkem.s
	$(AR) -r $@ jkem.o

.PHONY: jkem.s
jkem.s: jkem.jazz
	jasminc -nowarning -lea $< -o $@

clean:
	rm -f *.s *.o *.a
