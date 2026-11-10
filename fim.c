/*
 * fim.c - File Integrity Monitoring System
 *
 * Build:   gcc -Wall -Wextra -O2 -o fim fim.c
 * Usage:   ./fim init <dir> [baseline]   create baseline of every regular file under <dir>
 *          ./fim check <dir> [baseline]  compare current state to baseline
 *          ./fim selftest                verify SHA-256 against known test vectors
 *
 * Exit codes (check): 0 = no changes, 1 = changes detected, 2 = error
 * Baseline format:    <sha256-hex>\t<absolute-path>\n   (one file per line)
 *
 * Self-contained: includes its own SHA-256, so no OpenSSL dependency. POSIX only (nftw).
 */
#define _XOPEN_SOURCE 700
#include <ftw.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

/* ---------------------------- SHA-256 ---------------------------- */

typedef struct {
    uint32_t state[8];
    uint64_t bitlen;
    uint8_t  data[64];
    size_t   datalen;
} Sha256;

static const uint32_t K[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void sha256_transform(Sha256 *c, const uint8_t *p)
{
    uint32_t w[64], a, b, d, e, f, g, h, cc, t1, t2;
    int i;

    for (i = 0; i < 16; i++)
        w[i] = (uint32_t)p[i*4] << 24 | (uint32_t)p[i*4+1] << 16 |
               (uint32_t)p[i*4+2] << 8 | (uint32_t)p[i*4+3];
    for (; i < 64; i++) {
        uint32_t s0 = ROTR(w[i-15], 7) ^ ROTR(w[i-15], 18) ^ (w[i-15] >> 3);
        uint32_t s1 = ROTR(w[i-2], 17) ^ ROTR(w[i-2], 19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }

    a = c->state[0]; b = c->state[1]; cc = c->state[2]; d = c->state[3];
    e = c->state[4]; f = c->state[5]; g = c->state[6]; h = c->state[7];

    for (i = 0; i < 64; i++) {
        uint32_t S1 = ROTR(e, 6) ^ ROTR(e, 11) ^ ROTR(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t S0 = ROTR(a, 2) ^ ROTR(a, 13) ^ ROTR(a, 22);
        uint32_t maj = (a & b) ^ (a & cc) ^ (b & cc);
        t1 = h + S1 + ch + K[i] + w[i];
        t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = cc; cc = b; b = a; a = t1 + t2;
    }

    c->state[0] += a; c->state[1] += b; c->state[2] += cc; c->state[3] += d;
    c->state[4] += e; c->state[5] += f; c->state[6] += g; c->state[7] += h;
}

static void sha256_init(Sha256 *c)
{
    static const uint32_t init[8] = {
        0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
        0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19
    };
    memcpy(c->state, init, sizeof init);
    c->bitlen = 0;
    c->datalen = 0;
}

static void sha256_update(Sha256 *c, const uint8_t *data, size_t len)
{
    for (size_t i = 0; i < len; i++) {
        c->data[c->datalen++] = data[i];
        if (c->datalen == 64) {
            sha256_transform(c, c->data);
            c->bitlen += 512;
            c->datalen = 0;
        }
    }
}

static void sha256_final(Sha256 *c, uint8_t out[32])
{
    size_t i = c->datalen;

    c->bitlen += (uint64_t)c->datalen * 8;
    c->data[i++] = 0x80;
    if (i > 56) {
        while (i < 64) c->data[i++] = 0;
        sha256_transform(c, c->data);
        i = 0;
    }
    while (i < 56) c->data[i++] = 0;
    for (int j = 0; j < 8; j++)
        c->data[63 - j] = (uint8_t)(c->bitlen >> (j * 8));
    sha256_transform(c, c->data);

    for (i = 0; i < 8; i++) {
        out[i*4]   = (uint8_t)(c->state[i] >> 24);
        out[i*4+1] = (uint8_t)(c->state[i] >> 16);
        out[i*4+2] = (uint8_t)(c->state[i] >> 8);
        out[i*4+3] = (uint8_t)(c->state[i]);
    }
}

static void to_hex(const uint8_t d[32], char hex[65])
{
    static const char *digits = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        hex[i*2]   = digits[d[i] >> 4];
        hex[i*2+1] = digits[d[i] & 0x0f];
    }
    hex[64] = '\0';
}

/* Hash a file in 64 KiB chunks (works for binary files of any size). 0 = ok, -1 = error. */
static int hash_file(const char *path, char hex[65])
{
    FILE *f = fopen(path, "rb");
    if (!f) return -1;

    Sha256 ctx;
    uint8_t buf[65536], digest[32];
    size_t n;

    sha256_init(&ctx);
    while ((n = fread(buf, 1, sizeof buf, f)) > 0)
        sha256_update(&ctx, buf, n);
    int err = ferror(f);
    fclose(f);
    if (err) return -1;

    sha256_final(&ctx, digest);
    to_hex(digest, hex);
    return 0;
}

static int selftest(void)
{
    struct { const char *msg, *expect; } tv[] = {
        { "",    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" },
        { "abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" },
    };
    int fails = 0;
    for (size_t i = 0; i < sizeof tv / sizeof tv[0]; i++) {
        Sha256 c; uint8_t d[32]; char hex[65];
        sha256_init(&c);
        sha256_update(&c, (const uint8_t *)tv[i].msg, strlen(tv[i].msg));
        sha256_final(&c, d);
        to_hex(d, hex);
        int ok = strcmp(hex, tv[i].expect) == 0;
        printf("[%s] SHA-256(\"%s\")\n", ok ? "PASS" : "FAIL", tv[i].msg);
        fails += !ok;
    }
    return fails ? 2 : 0;
}

/* ------------------------- Baseline store ------------------------- */

typedef struct {
    char *path;
    char  hash[65];
    int   seen;
} Entry;

static Entry  *entries;
static size_t  n_entries, cap_entries;

static int add_entry(const char *path, const char *hash)
{
    if (n_entries == cap_entries) {
        size_t ncap = cap_entries ? cap_entries * 2 : 256;
        Entry *tmp = realloc(entries, ncap * sizeof *tmp);
        if (!tmp) return -1;
        entries = tmp;
        cap_entries = ncap;
    }
    Entry *e = &entries[n_entries];
    e->path = strdup(path);
    if (!e->path) return -1;
    memcpy(e->hash, hash, 65);
    e->seen = 0;
    n_entries++;
    return 0;
}

static int cmp_entry(const void *a, const void *b)
{
    return strcmp(((const Entry *)a)->path, ((const Entry *)b)->path);
}

static int load_baseline(const char *file)
{
    FILE *f = fopen(file, "r");
    if (!f) { perror(file); return -1; }

    char line[PATH_MAX + 128];
    size_t lineno = 0;
    while (fgets(line, sizeof line, f)) {
        lineno++;
        line[strcspn(line, "\r\n")] = '\0';
        if (line[0] == '\0') continue;
        if (strlen(line) < 66 || line[64] != '\t') {
            fprintf(stderr, "%s:%zu: malformed baseline line\n", file, lineno);
            fclose(f);
            return -1;
        }
        line[64] = '\0';
        if (add_entry(line + 65, line) != 0) { fclose(f); return -1; }
    }
    fclose(f);
    qsort(entries, n_entries, sizeof *entries, cmp_entry);
    return 0;
}

/* ----------------------------- Walking ---------------------------- */

enum { MODE_INIT, MODE_CHECK };

static int     g_mode;
static FILE   *g_out;                 /* baseline being written (init) */
static dev_t   g_skip_dev;            /* baseline file itself: never hash it */
static ino_t   g_skip_ino;
static size_t  g_added, g_modified, g_unreadable, g_files;

static int visit(const char *path, const struct stat *sb, int type, struct FTW *ftw)
{
    (void)ftw;
    if (type != FTW_F) return 0;                       /* regular files only; symlinks skipped (FTW_PHYS) */
    if (sb->st_dev == g_skip_dev && sb->st_ino == g_skip_ino) return 0;

    char hex[65];
    if (hash_file(path, hex) != 0) {
        fprintf(stderr, "[WARN] cannot read: %s\n", path);
        g_unreadable++;
        return 0;
    }
    g_files++;

    if (g_mode == MODE_INIT) {
        fprintf(g_out, "%s\t%s\n", hex, path);
        return 0;
    }

    Entry key = { .path = (char *)path };
    Entry *e = bsearch(&key, entries, n_entries, sizeof *entries, cmp_entry);
    if (!e) {
        printf("[ADDED]    %s\n", path);
        g_added++;
    } else {
        e->seen = 1;
        if (strcmp(e->hash, hex) != 0) {
            printf("[MODIFIED] %s\n", path);
            g_modified++;
        }
    }
    return 0;
}

static void usage(const char *prog)
{
    fprintf(stderr, "Usage: %s init  <dir> [baseline]\n"
                    "       %s check <dir> [baseline]\n"
                    "       %s selftest\n", prog, prog, prog);
}

int main(int argc, char **argv)
{
    if (argc >= 2 && strcmp(argv[1], "selftest") == 0) return selftest();
    if (argc < 3) { usage(argv[0]); return 2; }

    const char *cmd = argv[1];
    const char *baseline = argc > 3 ? argv[3] : "baseline.txt";
    char root[PATH_MAX];

    if (strcmp(cmd, "init") == 0)       g_mode = MODE_INIT;
    else if (strcmp(cmd, "check") == 0) g_mode = MODE_CHECK;
    else { usage(argv[0]); return 2; }

    if (!realpath(argv[2], root)) { perror(argv[2]); return 2; }

    struct stat st;
    if (g_mode == MODE_INIT) {
        g_out = fopen(baseline, "w");
        if (!g_out) { perror(baseline); return 2; }
        if (fstat(fileno(g_out), &st) == 0) { g_skip_dev = st.st_dev; g_skip_ino = st.st_ino; }
    } else {
        if (load_baseline(baseline) != 0) return 2;
        if (stat(baseline, &st) == 0) { g_skip_dev = st.st_dev; g_skip_ino = st.st_ino; }
    }

    if (nftw(root, visit, 32, FTW_PHYS) != 0) {
        perror("nftw");
        return 2;
    }

    if (g_mode == MODE_INIT) {
        if (fclose(g_out) != 0) { perror(baseline); return 2; }
        printf("Baseline created: %zu files hashed -> %s (%zu unreadable)\n",
               g_files, baseline, g_unreadable);
        return 0;
    }

    size_t deleted = 0;
    for (size_t i = 0; i < n_entries; i++) {
        if (!entries[i].seen) {
            printf("[DELETED]  %s\n", entries[i].path);
            deleted++;
        }
    }
    printf("\nScanned %zu files: %zu modified, %zu added, %zu deleted, %zu unreadable\n",
           g_files, g_modified, g_added, deleted, g_unreadable);

    int changes = g_modified || g_added || deleted;
    if (!changes) puts("OK: integrity verified.");
    return changes ? 1 : 0;
}
