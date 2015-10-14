CC=ccomp

all: hmac ctr

test: all
	./hmac
	./ctr

clean:
	rm -f *.o
	rm -f hmac ctr vst_hmac

hmac: hmac_drbg.c hmac_drbg.h md.c md.h sha1.c sha1.h md_wrap.c
	$(CC) hmac_drbg.c md.c sha1.c md_wrap.c -o hmac


ctr: ctr_drbg.c ctr_drbg.h aes.c aes.h
	$(CC) ctr_drbg.c aes.c -o ctr

vst_hmac: hmac_drbg.c hmac_drbg.h md.h mocked_md.c sha.c sha.h hmac_NK.c hmac.h hmac_NK.c
	$(CC) hmac_drbg.c mocked_md.c sha.c hmac_NK.c -o vst_hmac
