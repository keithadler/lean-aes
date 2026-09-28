/* mbedTLS 4 through its PSA Crypto API: ECB without padding, CTR, and CBC with PKCS #7. */
#include "io.h"
#include <psa/crypto.h>

static psa_status_t cipher(psa_algorithm_t alg, int decrypt, const unsigned char *key, const unsigned char *iv,
                           const unsigned char *in, size_t n, unsigned char *out, size_t *outlen) {
    psa_key_attributes_t a = PSA_KEY_ATTRIBUTES_INIT;
    psa_set_key_type(&a, PSA_KEY_TYPE_AES);
    psa_set_key_bits(&a, 256);
    psa_set_key_algorithm(&a, alg);
    psa_set_key_usage_flags(&a, PSA_KEY_USAGE_ENCRYPT | PSA_KEY_USAGE_DECRYPT);
    psa_key_id_t k;
    psa_status_t s = psa_import_key(&a, key, 32, &k);
    if (s) return s;
    psa_cipher_operation_t op = PSA_CIPHER_OPERATION_INIT;
    s = decrypt ? psa_cipher_decrypt_setup(&op, k, alg) : psa_cipher_encrypt_setup(&op, k, alg);
    if (!s && iv) s = psa_cipher_set_iv(&op, iv, 16);
    size_t a1 = 0, a2 = 0;
    if (!s) s = psa_cipher_update(&op, in, n, out, n + 32, &a1);
    if (!s) s = psa_cipher_finish(&op, out + a1, n + 32 - a1, &a2);
    psa_cipher_abort(&op);
    psa_destroy_key(k);
    *outlen = a1 + a2;
    return s;
}

int main(void) {
    psa_crypto_init();
    static char buf[1 << 16];
    unsigned char key[32], iv[16], in[4096], out[4200];
    row r;
    while (next(&r, buf, sizeof buf)) {
        unhex(r.key, key);
        size_t n = unhex(r.in, in), outlen = 0;
        int has_iv = strlen(r.iv) == 32;
        if (has_iv) unhex(r.iv, iv);
        psa_status_t s;
        if (!strcmp(r.suite, "block")) s = cipher(PSA_ALG_ECB_NO_PADDING, !strcmp(r.op, "decrypt"), key, NULL, in, n, out, &outlen);
        else if (!strcmp(r.suite, "ctr")) s = cipher(PSA_ALG_CTR, 0, key, iv, in, n, out, &outlen);
        else s = cipher(PSA_ALG_CBC_PKCS7, 1, key, iv, in, n, out, &outlen);
        if (s) err(r.suite, r.id, "psa", (int)s); else put(r.suite, r.id, out, outlen);
    }
    return 0;
}
