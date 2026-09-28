/* wolfSSL through its EVP layer: aes-256-ecb (no padding), aes-256-ctr, aes-256-cbc (PKCS #7). */
#include "io.h"
#include <wolfssl/options.h>
#include <wolfssl/openssl/evp.h>

int main(void) {
    static char buf[1 << 16];
    unsigned char key[32], iv[16], in[4096], out[4200];
    row r;
    while (next(&r, buf, sizeof buf)) {
        unhex(r.key, key);
        size_t n = unhex(r.in, in);
        int has_iv = strlen(r.iv) == 32;
        if (has_iv) unhex(r.iv, iv);
        const WOLFSSL_EVP_CIPHER *c = !strcmp(r.suite, "block") ? wolfSSL_EVP_aes_256_ecb()
                                    : !strcmp(r.suite, "ctr") ? wolfSSL_EVP_aes_256_ctr() : wolfSSL_EVP_aes_256_cbc();
        int enc = !strcmp(r.suite, "ctr") || (!strcmp(r.suite, "block") && strcmp(r.op, "decrypt"));
        WOLFSSL_EVP_CIPHER_CTX *ctx = wolfSSL_EVP_CIPHER_CTX_new();
        int ok = wolfSSL_EVP_CipherInit(ctx, c, key, has_iv ? iv : NULL, enc);
        if (ok && !strcmp(r.suite, "block")) wolfSSL_EVP_CIPHER_CTX_set_padding(ctx, 0);
        int l1 = 0, l2 = 0;
        if (ok) ok = wolfSSL_EVP_CipherUpdate(ctx, out, &l1, in, (int)n);
        if (ok) ok = wolfSSL_EVP_CipherFinal(ctx, out + l1, &l2);
        if (ok == 1) put(r.suite, r.id, out, (size_t)(l1 + l2)); else err(r.suite, r.id, "evp", ok);
        wolfSSL_EVP_CIPHER_CTX_free(ctx);
    }
    return 0;
}
