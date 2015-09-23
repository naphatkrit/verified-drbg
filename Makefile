CC=clang

all: hmac

test: all
	./hmac

clean:
	rm *.o
	rm hmac

hmac: hmac_drbg.c hmac_drbg.h md.c md.h sha1.c sha1.h
	$(CC) hmac_drbg.c md.c sha1.c -o hmac
