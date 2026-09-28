/* Tab-separated cases on stdin: suite, id, op, key, iv, input (hex). One "suite\tid\tresult" line out. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static size_t unhex(const char *h, unsigned char *out) {
    size_t n = strlen(h) / 2;
    for (size_t i = 0; i < n; i++) sscanf(h + 2 * i, "%2hhx", &out[i]);
    return n;
}

static void put(const char *suite, const char *id, const unsigned char *b, size_t n) {
    printf("%s\t%s\t", suite, id);
    for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
    printf("\n");
    fflush(stdout);
}

static void err(const char *suite, const char *id, const char *msg, int code) {
    printf("%s\t%s\tERR:%s %d\n", suite, id, msg, code);
    fflush(stdout);
}

typedef struct { char *suite, *id, *op, *key, *iv, *in; } row;

static int next(row *r, char *buf, size_t size) {
    if (!fgets(buf, size, stdin)) return 0;
    buf[strcspn(buf, "\n")] = 0;
    char *f[6] = {0}, *p = buf;
    for (int i = 0; i < 6; i++) { f[i] = p; p = strchr(p, '\t'); if (!p) break; *p++ = 0; }
    r->suite = f[0]; r->id = f[1]; r->op = f[2]; r->key = f[3]; r->iv = f[4]; r->in = f[5];
    return 1;
}
