#include <stddef.h>
#include "sha.h"

typedef struct hmac_ctx_st
	{
	  //	EVP_MD *md; We fix this to be sha256

        SHA256_CTX md_ctx; //SHA structure for current hmac application -
         //is used for calculation of "short key", and later holds the
         //inner sha structure, to avoid overwriting i_ctx
        //unsigned char md_ctx[32]; holds short-key

        SHA256_CTX i_ctx; //the SHA structure for the inner sha application
        //unsigned char i_ctx[HMAC_MAX_MD_CBLOCK];

	SHA256_CTX o_ctx; //the SHA structure for the outer sha application
        //unsigned char o_ctx[HMAC_MAX_MD_CBLOCK];

	//unsigned int key_length;
	//unsigned char key[HMAC_MAX_MD_CBLOCK];
    } HMAC_CTX;

/****From hmac.h, and specialized to use of sha256 *************/
#define HMAC_MAX_MD_CBLOCK	64 //i.e. SHA256_BLOCK_SIZE

void HMAC_Init(HMAC_CTX *ctx, unsigned char *key, int len);

void HMAC_Update(HMAC_CTX *ctx, const void *data, size_t len);

void HMAC_Final(HMAC_CTX *ctx, unsigned char *md);

void HMAC_cleanup(HMAC_CTX *ctx);

unsigned char *HMAC(
                    unsigned char *key, int key_len,
                    unsigned char *d, int n,
                    unsigned char *md);

unsigned char *HMAC2(
                    unsigned char *key, int key_len,
                    unsigned char *d, int n,
                    unsigned char *md);
