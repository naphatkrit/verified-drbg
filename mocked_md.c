#include <stdlib.h>
#include "md.h"
#include "hmac_NK.c"

struct mbedtls_md_info_t {};

static const mbedtls_md_info_t mocked_sha256_info;

const mbedtls_md_info_t *mbedtls_md_info_from_string( const char *md_name ) {
    return &mocked_sha256_info;
}

const mbedtls_md_info_t *mbedtls_md_info_from_type( mbedtls_md_type_t md_type ) {
    return &mocked_sha256_info;
}

unsigned char mbedtls_md_get_size( const mbedtls_md_info_t *md_info ) {
    return SHA256_DIGEST_LENGTH;
}

int mbedtls_md_setup( mbedtls_md_context_t *ctx, const mbedtls_md_info_t *md_info, int hmac ) {
    HMAC_CTX * sha_ctx = (HMAC_CTX *) malloc(sizeof(HMAC_CTX));
    if (sha_ctx == NULL) {
        return MBEDTLS_ERR_MD_ALLOC_FAILED;
    }
    ctx->hmac_ctx = sha_ctx;
    return 0;
}

int mbedtls_md_hmac_starts( mbedtls_md_context_t *ctx, const unsigned char *key, size_t keylen ) {
    HMAC_Init(ctx->hmac_ctx, (unsigned char*) key, keylen);
    return 0;
}

int mbedtls_md_hmac_reset( mbedtls_md_context_t *ctx ) {
    unsigned char buf[SHA256_DIGEST_LENGTH]; //ie 32
    HMAC_Final(ctx->hmac_ctx, buf);
    return 0;
}

int mbedtls_md_hmac_update( mbedtls_md_context_t *ctx, const unsigned char *input, size_t ilen ) {
    HMAC_Update(ctx->hmac_ctx, input, ilen);
    return 0;
}

int mbedtls_md_hmac_finish( mbedtls_md_context_t *ctx, unsigned char *output) {
    HMAC_Final(ctx->hmac_ctx, output);
    return 0;
}

void mbedtls_md_free( mbedtls_md_context_t *ctx ) {
    HMAC_cleanup(ctx->hmac_ctx);
    free(ctx->hmac_ctx);
}
