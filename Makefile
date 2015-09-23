CC=ccomp

all: hmac

clean:
	rm *.o
	rm hmac

hmac: hmac_drbg.c hmac_drbg.h md.c md.h
	$(CC) hmac_drbg.c md.c -o hmac
