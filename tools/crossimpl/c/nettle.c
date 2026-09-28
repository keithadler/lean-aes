/* Nettle, GnuTLS's crypto library: aes256 and ctr_crypt. Nettle has no PKCS #7 unpadding, so cbc is n/a. */
#include "io.h"
#include <nettle/aes.h>
#include <nettle/ctr.h>

int main(void) {
    static char buf[1 << 16];
    unsigned char key[32], iv[16], in[4096], out[4200];
    row r;
    while (next(&r, buf, sizeof buf)) {
        unhex(r.key, key);
        size_t n = unhex(r.in, in);
        if (!strcmp(r.suite, "block")) {
            struct aes256_ctx ctx;
            if (!strcmp(r.op, "decrypt")) { aes256_set_decrypt_key(&ctx, key); aes256_decrypt(&ctx, n, out, in); }
            else { aes256_set_encrypt_key(&ctx, key); aes256_encrypt(&ctx, n, out, in); }
            put(r.suite, r.id, out, n);
        } else if (!strcmp(r.suite, "ctr")) {
            struct aes256_ctx ctx;
            unhex(r.iv, iv);
            aes256_set_encrypt_key(&ctx, key);
            ctr_crypt(&ctx, (nettle_cipher_func *)aes256_encrypt, 16, iv, n, out, in);
            put(r.suite, r.id, out, n);
        } else {
            printf("%s\t%s\tNA\n", r.suite, r.id);
        }
    }
    return 0;
}
