CC=ccomp

all: hmac ctr

test: all
	./hmac
	./ctr

clean:
	rm -f *.o
	rm -f hmac ctr

hmac: hmac_drbg.c hmac_drbg.h md.c md.h sha1.c sha1.h md_wrap.c
	$(CC) hmac_drbg.c md.c sha1.c md_wrap.c -o hmac


ctr: ctr_drbg.c ctr_drbg.h aes.c aes.h
	$(CC) ctr_drbg.c aes.c -o ctr
