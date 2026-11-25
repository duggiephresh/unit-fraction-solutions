// beamc.c -- residue-only beam descent for the coprime #307 variant. FixedQ, P-side growth only.
//   cc -O2 -I/opt/homebrew/include -L/opt/homebrew/lib -o beamc beamc.c -lgmp -lpthread -lm
//   ./beamc W THREADS MAXLEVELS prefix
// State (P,Q): D = M(P)M(Q) - A(P)A(Q), E = A(Q)M(P). Adding s to P gives D' = s*D - E, so any D' > 0 with
// D' = -E (mod D) defines an integer s = (E + D')/D. Elements are never formed; a state is the list of its
// deviations D_0..D_i, and E_i mod m is recomputed from E_{j+1} = E_j*(E_j + D_{j+1})/D_j.
// A step is valid when gcd(D', E) = 1 (s coprime to P and to A(Q)) and s mod M(Q) is a unit (s coprime to Q).
// Every chain this program outputs is re-checked by an independent exact verifier (verify.py).
#include <stdio.h>
#include <gmp.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Odd Znam: Q = {1}, so Dev = M(P) - A(P) and E = M(P). Every new element must be odd: the only tracked
// prime is 2.
#define NQ 1
static const unsigned long QP[NQ] = {2};
static const int PE[NQ] = {6000};                      // 2-adic precision carried for E
#define MQ 2UL                                          // unit modulus: s must be odd
#define DEVM 1UL                                        // Dev = DEVM*M(P) - AQ*A(P)
#define AQ 1UL                                          // E = AQ*M(P)
#define NL 8                                            // limbs stored per deviation (512 bits)
#define MAXLEV 4000
#define MAXSP 128

typedef struct { mpz_t r, Eq; uint16_t ex[NQ]; uint8_t v[NQ]; uint32_t cm; } State;
typedef struct { double val; uint32_t i; uint32_t k; } Item;
typedef struct { uint32_t i, k; int ok; mpz_t D, r, Eq; uint16_t ex[NQ]; uint8_t v[NQ]; uint32_t cm; } Cand;

static size_t W; static int NT;
static mpz_t E0, modp0;
static unsigned long sp[MAXSP]; static int nsp;          // primes that D' must avoid (seed primes and AQ)
static int P0[MAXSP], nP0;
static uint8_t unitMQ[MQ];
static mp_limb_t *LD[MAXLEV]; static uint32_t *LP[MAXLEV];
static State *cur; static size_t ncur; static int lev;   // cur = states of level lev-1 while building level lev
static uint16_t *dm, *rm; static double *lx, *uu;
static Cand *cand; static size_t ncand, cand_done;
static long rejA, rejB, rejO;

static void die(const char *m) { fprintf(stderr, "FATAL: %s\n", m); exit(1); }

static void store_limbs(mp_limb_t *dst, const mpz_t x) {
  size_t n = mpz_size(x); if (n > NL) die("deviation too large for NL limbs");
  for (size_t i = 0; i < NL; i++) dst[i] = i < n ? mpz_getlimbn(x, i) : 0;
}
static void view(mpz_t v, const mp_limb_t *p) { mp_size_t n = NL; while (n > 0 && p[n - 1] == 0) n--; mpz_roinit_n(v, p, n); }

// ---- heap -------------------------------------------------------------------------------------------------
static Item *heap; static size_t hn;
static void hpush(Item it) { size_t c = hn++; while (c) { size_t p = (c - 1) / 2; if (heap[p].val <= it.val) break; heap[c] = heap[p]; c = p; } heap[c] = it; }
static Item hpop(void) { Item top = heap[0], last = heap[--hn]; size_t c = 0; for (;;) { size_t l = 2 * c + 1; if (l >= hn) break; if (l + 1 < hn && heap[l + 1].val < heap[l].val) l++; if (heap[l].val >= last.val) break; heap[c] = heap[l]; c = l; } heap[c] = last; return top; }

static uint32_t next_k(uint32_t i, uint32_t k) {         // smallest offset >= k passing the cheap tests
  const uint16_t *d = dm + (size_t)i * nsp, *r = rm + (size_t)i * nsp; uint32_t cm = cur[i].cm;
  for (;; k++) {
    if (!unitMQ[(cm + k) % MQ]) continue;
    int ok = 1;
    for (int j = 0; j < nsp; j++) { unsigned long l = sp[j]; if ((r[j] + (unsigned long)(k % l) * d[j]) % l == 0) { ok = 0; break; } }
    if (ok) return k;
  }
}

// ---- 64-bit helpers for the rare "shared prime" pass -----------------------------------------------------
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }
static int inv64(uint64_t a, uint64_t m, uint64_t *out) {  // a^{-1} mod m, 0 if not invertible
  __int128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { __int128 q = r / nr, x = t - q * nt; t = nt; nt = x; x = r - q * nr; r = nr; nr = x; }
  if (r != 1) return 0; if (t < 0) t += m; *out = (uint64_t)t; return 1;
}
// E_{n} mod w, where hist[0..n] are the deviations of the parent (n = lev-1). Returns 0 on overflow.
static int robust_small(mpz_t *hist, int n, uint64_t w, uint64_t *out) {
  uint64_t *g = malloc(sizeof(uint64_t) * (n + 1)); u128 R = w; mpz_t x; mpz_init(x);
  for (int j = 0; j < n; j++) {
    uint64_t gj = 1, c = gcd64(mpz_fdiv_ui(hist[j], w), w);
    if (c > 1) { mpz_set(x, hist[j]); while (c > 1) { mpz_divexact_ui(x, x, c); gj *= c; R *= c; if (R >> 62) { free(g); mpz_clear(x); return 0; } c = gcd64(mpz_fdiv_ui(x, w), w); } }
    g[j] = gj;
  }
  uint64_t Rc = (uint64_t)R, N = mpz_fdiv_ui(E0, Rc), dl = 1 % Rc;
  for (int j = 0; j < n; j++) {
    uint64_t dj1 = mpz_fdiv_ui(hist[j + 1], Rc);
    uint64_t t = (uint64_t)(((u128)dj1 * dl + N) % Rc);          // N + D_{j+1}*dl
    uint64_t dj;
    if (g[j] > 1) {
      if (t % g[j]) die("robust pass: inexact division");
      t /= g[j]; Rc /= g[j]; N %= Rc; dl %= Rc; t %= Rc;
      mpz_divexact_ui(x, hist[j], g[j]); dj = mpz_fdiv_ui(x, Rc);
    } else dj = mpz_fdiv_ui(hist[j], Rc);
    N = mulmod(N, t, Rc); dl = mulmod(mulmod(dl, dl, Rc), dj, Rc);
  }
  free(g); mpz_clear(x);
  uint64_t iv; if (!inv64(dl % w, w, &iv)) die("robust pass: denominator not invertible");
  *out = mulmod(N % w, iv, w); return 1;
}

// ---- worker ------------------------------------------------------------------------------------------------
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static void *worker(void *arg) {
  (void)arg;
  int n = lev - 1;                                       // parent's last index in its history
  mpz_t *hist = malloc(sizeof(mpz_t) * (n + 2));
  mpz_t modp, modc, g, inv, Dn, gn, D2, N, dl, t, t2, c, e1, X, sq, m2, e2, T, u, wz, tmp;
  mpz_inits(modp, modc, g, inv, Dn, gn, D2, N, dl, t, t2, c, e1, X, sq, m2, e2, T, u, wz, tmp, NULL);
  long la = 0, lb = 0, lo = 0;
  for (;;) {
    pthread_mutex_lock(&mu);
    size_t a = cand_done; if (a >= ncand) { pthread_mutex_unlock(&mu); break; }
    size_t b = a + 1; while (b < ncand && cand[b].i == cand[a].i) b++;
    while (b < ncand && b - a < 64) { size_t e = b + 1; while (e < ncand && cand[e].i == cand[b].i) e++; b = e; }
    cand_done = b; pthread_mutex_unlock(&mu);
    uint32_t pi = UINT32_MAX;
    mpz_srcptr D = NULL; State *st = NULL;
    for (size_t ci = a; ci < b; ci++) {
      Cand *cd = &cand[ci];
      if (cd->i != pi) {                                 // new parent: history views and q-adic data
        pi = cd->i; st = &cur[pi];
        uint32_t idx = pi;
        for (int j = n; j >= 0; j--) { view(hist[j], LD[j] + (size_t)idx * NL); idx = LP[j][idx]; }
        D = hist[n];
        mpz_set_ui(modp, 1); mpz_set_ui(g, 1);
        for (int q = 0; q < NQ; q++) { mpz_ui_pow_ui(tmp, QP[q], st->ex[q]); mpz_mul(modp, modp, tmp); mpz_ui_pow_ui(tmp, QP[q], st->v[q]); mpz_mul(g, g, tmp); }
        mpz_divexact(modc, modp, g); mpz_divexact(tmp, D, g);
        if (!mpz_invert(inv, tmp, modp)) die("q-adic inverse");
      }
      cd->ok = 0;
      mpz_mul_ui(Dn, D, cd->k); mpz_add(Dn, Dn, st->r);  // D' = r + k*D
      if (mpz_size(Dn) > NL) { lo++; continue; }
      mpz_set(D2, Dn); mpz_set_ui(gn, 1);
      int precok = 1;
      for (int q = 0; q < NQ; q++) {
        int v = 0; while (mpz_divisible_ui_p(D2, QP[q])) { mpz_divexact_ui(D2, D2, QP[q]); mpz_mul_ui(gn, gn, QP[q]); v++; }
        cd->v[q] = (uint8_t)v; int e = (int)st->ex[q] - (int)st->v[q]; if (e < v + 4 || v > 200) precok = 0; cd->ex[q] = (uint16_t)(e > 0 ? e : 0);
      }
      if (!precok) { lo++; continue; }
      if (mpz_cmp_ui(D2, 1) > 0) {
        mpz_mod(N, E0, D2); mpz_set_ui(dl, 1);
        for (int j = 0; j < n; j++) {                    // E_j = N/dl (mod D2)
          mpz_mul(t, hist[j + 1], dl); mpz_add(t, t, N); mpz_mul(t, t, N); mpz_mod(N, t, D2);
          mpz_mul(t2, dl, dl); mpz_mul(t2, t2, hist[j]); mpz_mod(dl, t2, D2);
        }
        mpz_mul(t, dl, dl); mpz_mul(t, t, D); mpz_mod(t, t, D2);       // denominator of E' = E^2/D
        mpz_gcd(c, t, D2);
        if (mpz_cmp_ui(c, 1) == 0) {
          mpz_gcd(c, N, D2); if (mpz_cmp_ui(c, 1) != 0) { la++; continue; }
          mpz_invert(t, t, D2); mpz_mul(e1, N, N); mpz_mul(e1, e1, t); mpz_mod(e1, e1, D2);
        } else {                                         // an ancestor deviation shares a prime with D'
          mpz_set(u, D2); mpz_set_ui(wz, 1);
          while (mpz_cmp_ui(c, 1) > 0) { mpz_divexact(u, u, c); mpz_mul(wz, wz, c); mpz_gcd(c, u, wz); }
          if (mpz_sizeinbase(wz, 2) > 40) { lb++; continue; }
          uint64_t w = mpz_get_ui(wz), Ew, iv;
          if (!robust_small(hist, n, w, &Ew)) { lb++; continue; }
          if (gcd64(Ew, w) != 1) { la++; continue; }
          if (!inv64(mpz_fdiv_ui(D, w), w, &iv)) die("D not invertible mod shared part");
          uint64_t e1w = mulmod(mulmod(Ew, Ew, w), iv, w);
          if (mpz_cmp_ui(u, 1) > 0) {
            mpz_mod(tmp, N, u); mpz_gcd(c, tmp, u); if (mpz_cmp_ui(c, 1) != 0) { la++; continue; }
            mpz_mod(t, t, u); if (!mpz_invert(t, t, u)) die("inverse mod u");
            mpz_mul(e1, tmp, tmp); mpz_mul(e1, e1, t); mpz_mod(e1, e1, u);
            // CRT: e1 mod u, e1w mod w
            mpz_set_ui(tmp, w); if (!mpz_invert(t2, u, tmp)) die("crt uw");
            mpz_ui_sub(t, e1w, e1); mpz_mul(t, t, t2); mpz_mod_ui(t, t, w); mpz_mul(t, t, u); mpz_add(e1, e1, t);
          } else mpz_set_ui(e1, e1w);
        }
      } else mpz_set_ui(e1, 0);
      // q-adic part
      mpz_add(X, st->Eq, Dn); mpz_mod(X, X, modp);
      if (!mpz_divisible_p(X, g)) die("q-adic exactness failed");
      mpz_divexact(X, X, g); mpz_mul(sq, X, inv); mpz_mod(sq, sq, modc);
      unsigned long s_mq = mpz_fdiv_ui(sq, MQ);
      if (s_mq != (st->cm + cd->k) % MQ || !unitMQ[s_mq]) die("s mod MQ mismatch");
      mpz_mod(tmp, st->Eq, modc); mpz_mul(cd->Eq, tmp, sq); mpz_mod(cd->Eq, cd->Eq, modc);
      mpz_mul_ui(m2, gn, MQ); mpz_mod(e2, cd->Eq, m2);
      if (mpz_cmp_ui(D2, 1) > 0) {                       // T = E' mod MQ*D'
        if (!mpz_invert(t, D2, m2)) die("crt");
        mpz_sub(T, e2, e1); mpz_mul(T, T, t); mpz_mod(T, T, m2); mpz_mul(T, T, D2); mpz_add(T, T, e1);
      } else mpz_set(T, e2);
      mpz_neg(cd->r, T); mpz_mod(cd->r, cd->r, Dn);
      mpz_add(t, T, cd->r); mpz_mul_ui(t2, Dn, MQ); mpz_mod(t, t, t2);
      if (!mpz_divisible_p(t, Dn)) die("c_min exactness failed");
      mpz_divexact(t, t, Dn); cd->cm = (uint32_t)mpz_fdiv_ui(t, MQ);
      mpz_set(cd->D, Dn); cd->ok = 1;
    }
  }
  pthread_mutex_lock(&mu); rejA += la; rejB += lb; rejO += lo; pthread_mutex_unlock(&mu);
  mpz_clears(modp, modc, g, inv, Dn, gn, D2, N, dl, t, t2, c, e1, X, sq, m2, e2, T, u, wz, tmp, NULL);
  free(hist); return NULL;
}

static void *residues(void *arg) {                        // small residues of D and r for the cheap tests
  size_t tid = (size_t)arg; mpz_t D;
  for (size_t i = tid; i < ncur; i += NT) {
    view(D, LD[lev - 1] + i * NL);
    for (int j = 0; j < nsp; j++) { dm[i * nsp + j] = (uint16_t)mpz_fdiv_ui(D, sp[j]); rm[i * nsp + j] = (uint16_t)mpz_fdiv_ui(cur[i].r, sp[j]); }
    long e1, e2; double a = mpz_get_d_2exp(&e1, D), b = mpz_get_d_2exp(&e2, cur[i].r);
    lx[i] = log(a) + e1 * M_LN2; uu[i] = (b / a) * pow(2.0, (double)(e2 - e1));
  }
  return NULL;
}

static int cmp_cand_parent(const void *a, const void *b) { const Cand *x = a, *y = b; return x->i < y->i ? -1 : x->i > y->i ? 1 : (x->k < y->k ? -1 : x->k > y->k); }
static Cand **ord;
static int cmp_ord(const void *a, const void *b) { return mpz_cmp((*(Cand *const *)a)->D, (*(Cand *const *)b)->D); }

static void write_chain(const char *fn, uint32_t idx, int last) {
  FILE *f = fopen(fn, "w"); if (!f) return;
  fprintf(f, "Q 1\nP0");
  for (int j = 0; j < nP0; j++) fprintf(f, " %d", P0[j]);
  fprintf(f, "\n");
  uint32_t *path = malloc(sizeof(uint32_t) * (last + 1));
  for (int j = last; j >= 0; j--) { path[j] = idx; idx = LP[j][idx]; }
  mpz_t v;
  for (int j = 0; j <= last; j++) { view(v, LD[j] + (size_t)path[j] * NL); gmp_fprintf(f, "%Zd\n", v); }
  free(path); fclose(f);
}

int main(int argc, char **argv) {
  if (argc < 5) die("usage: beamc W THREADS MAXLEVELS prefix");
  W = strtoul(argv[1], 0, 10); NT = atoi(argv[2]); int maxlev = atoi(argv[3]); const char *prefix = argv[4];
  if (maxlev >= MAXLEV) maxlev = MAXLEV - 1;
  for (unsigned long x = 0; x < MQ; x++) { int u = 1; for (int q = 0; q < NQ; q++) if (x % QP[q] == 0) u = 0; unitMQ[x] = (uint8_t)u; }
  // seed: consecutive primes >= 5 not in Q and not dividing A(Q), while the deviation stays positive
  mpz_t M, A, D0, M2, A2, t; mpz_inits(M, A, D0, M2, A2, t, E0, modp0, NULL); mpz_set_ui(M, 1); mpz_set_ui(A, 0);
  for (int p = 3; p < 2000; p++) {
    int pr = 1; for (int d = 2; d * d <= p; d++) if (p % d == 0) { pr = 0; break; }
    if (!pr) continue; int skip = (AQ > 1 && AQ % p == 0); for (int q = 0; q < NQ; q++) if ((unsigned long)p == QP[q]) skip = 1;
    if (skip) continue;
    mpz_mul_ui(M2, M, p); mpz_mul_ui(A2, A, p); mpz_add(A2, A2, M);
    mpz_mul_ui(t, M2, DEVM); mpz_submul_ui(t, A2, AQ);
    if (mpz_sgn(t) > 0) { mpz_set(M, M2); mpz_set(A, A2); P0[nP0++] = p; sp[nsp++] = p; } else break;
  }
  if (AQ > 1) sp[nsp++] = AQ;
  mpz_mul_ui(D0, M, DEVM); mpz_submul_ui(D0, A, AQ); mpz_mul_ui(E0, M, AQ);
  mpz_set_ui(modp0, 1); for (int q = 0; q < NQ; q++) { mpz_ui_pow_ui(t, QP[q], PE[q]); mpz_mul(modp0, modp0, t); }
  gmp_printf("seed: odd Znam (Q = {1}), |P0| = %d primes %d..%d, D0 has %zu digits, E0 has %zu digits\n", nP0, P0[0], P0[nP0 - 1], mpz_sizeinbase(D0, 10), mpz_sizeinbase(E0, 10));
  size_t CM = W + W / 2 + 1024;
  cur = calloc(W, sizeof(State)); for (size_t i = 0; i < W; i++) mpz_inits(cur[i].r, cur[i].Eq, NULL);
  cand = calloc(CM, sizeof(Cand)); for (size_t i = 0; i < CM; i++) mpz_inits(cand[i].D, cand[i].r, cand[i].Eq, NULL);
  ord = malloc(sizeof(Cand *) * CM); heap = malloc(sizeof(Item) * (W + 16));
  dm = malloc(sizeof(uint16_t) * W * MAXSP); rm = malloc(sizeof(uint16_t) * W * MAXSP); lx = malloc(sizeof(double) * W); uu = malloc(sizeof(double) * W);
  // root
  LD[0] = calloc(NL, sizeof(mp_limb_t)); LP[0] = calloc(1, sizeof(uint32_t)); store_limbs(LD[0], D0);
  mpz_neg(cur[0].r, E0); mpz_mod(cur[0].r, cur[0].r, D0);
  mpz_add(t, E0, cur[0].r); mpz_divexact(t, t, D0); cur[0].cm = (uint32_t)mpz_fdiv_ui(t, MQ);
  mpz_mod(cur[0].Eq, E0, modp0);
  mpz_set(t, D0);
  for (int q = 0; q < NQ; q++) { int v = 0; while (mpz_divisible_ui_p(t, QP[q])) { mpz_divexact_ui(t, t, QP[q]); v++; } cur[0].v[q] = (uint8_t)v; cur[0].ex[q] = (uint16_t)PE[q]; }
  ncur = 1;
  pthread_t *th = malloc(sizeof(pthread_t) * NT); time_t t0 = time(NULL);
  char fn[512];
  int startlev = 1;
  if (argc > 5) {                                         // resume: replay the chain in argv[5]
    FILE *f = fopen(argv[5], "r"); if (!f) die("cannot open resume file");
    size_t cap = 1 << 22; char *line = malloc(cap); mpz_t Dn, kk, Dc; mpz_inits(Dn, kk, Dc, NULL);
    if (!fgets(line, cap, f) || !fgets(line, cap, f) || !fgets(line, cap, f)) die("bad resume file");
    mpz_set_str(Dn, line, 10); if (mpz_cmp(Dn, D0) != 0) die("resume file has a different seed");
    mpz_set(Dc, D0);
    static State *nx2 = NULL; nx2 = calloc(1, sizeof(State)); mpz_inits(nx2[0].r, nx2[0].Eq, NULL);
    while (fgets(line, cap, f)) {
      if (line[0] < '0' || line[0] > '9') continue;
      mpz_set_str(Dn, line, 10);
      mpz_sub(kk, Dn, cur[0].r); if (!mpz_divisible_p(kk, Dc)) die("resume: chain step not in the class");
      mpz_divexact(kk, kk, Dc); if (!mpz_fits_ulong_p(kk) || mpz_get_ui(kk) > 4000000000UL) die("resume: offset too large");
      lev = startlev; cand[0].i = 0; cand[0].k = (uint32_t)mpz_get_ui(kk); cand[0].ok = 0; ncand = 1; cand_done = 0;
      worker(NULL);
      if (!cand[0].ok || mpz_cmp(cand[0].D, Dn) != 0) die("resume: replayed step rejected");
      LD[lev] = malloc(sizeof(mp_limb_t) * NL); LP[lev] = malloc(sizeof(uint32_t)); store_limbs(LD[lev], Dn); LP[lev][0] = 0;
      mpz_swap(cur[0].r, cand[0].r); mpz_swap(cur[0].Eq, cand[0].Eq); memcpy(cur[0].ex, cand[0].ex, sizeof cand[0].ex);
      memcpy(cur[0].v, cand[0].v, sizeof cand[0].v); cur[0].cm = cand[0].cm; mpz_set(Dc, Dn); startlev++;
    }
    fclose(f); ncur = 1; rejA = rejB = rejO = 0;
    gmp_printf("resumed at level %d, D has %zu digits\n", startlev - 1, mpz_sizeinbase(Dc, 10)); fflush(stdout);
  }
  for (lev = startlev; lev <= maxlev; lev++) {
    time_t tl = time(NULL);
    for (size_t k = 0; k < (size_t)NT; k++) pthread_create(&th[k], 0, residues, (void *)k);
    for (int k = 0; k < NT; k++) pthread_join(th[k], 0);
    hn = 0;
    for (size_t i = 0; i < ncur; i++) { uint32_t k = next_k((uint32_t)i, 0); Item it = {lx[i] + log(k + uu[i]), (uint32_t)i, k}; hpush(it); }
    size_t nacc = 0, used = 0; rejA = rejB = rejO = 0;
    while (nacc < W) {
      size_t want = (W - nacc) + (W - nacc) / 8 + 64; if (used + want > CM) want = CM - used;
      if (want == 0) break;
      size_t base = used;
      for (size_t j = 0; j < want; j++) { Item it = hpop(); cand[used].i = it.i; cand[used].k = it.k; cand[used].ok = 0; used++; it.k = next_k(it.i, it.k + 1); it.val = lx[it.i] + log(it.k + uu[it.i]); hpush(it); }
      // evaluate cand[base..used) grouped by parent
      Cand *save = cand; size_t savn = ncand;
      cand = save + base; ncand = used - base; cand_done = 0;
      qsort(cand, ncand, sizeof(Cand), cmp_cand_parent);
      for (int k = 0; k < NT; k++) pthread_create(&th[k], 0, worker, 0);
      for (int k = 0; k < NT; k++) pthread_join(th[k], 0);
      for (size_t j = 0; j < ncand; j++) if (cand[j].ok) nacc++;
      cand = save; ncand = savn;
    }
    size_t m = 0; for (size_t j = 0; j < used; j++) if (cand[j].ok) ord[m++] = &cand[j];
    qsort(ord, m, sizeof(Cand *), cmp_ord);
    if (m > W) m = W;
    LD[lev] = malloc(sizeof(mp_limb_t) * NL * m); LP[lev] = malloc(sizeof(uint32_t) * m);
    if (!LD[lev] || !LP[lev]) die("out of memory");
    for (size_t j = 0; j < m; j++) {
      Cand *cd = ord[j]; store_limbs(LD[lev] + j * NL, cd->D); LP[lev][j] = cd->i;
    }
    // install new beam (swap big numbers out of the candidate slots)
    static State *nxt = NULL; if (!nxt) { nxt = calloc(W, sizeof(State)); for (size_t i = 0; i < W; i++) mpz_inits(nxt[i].r, nxt[i].Eq, NULL); }
    for (size_t j = 0; j < m; j++) { Cand *cd = ord[j]; mpz_swap(nxt[j].r, cd->r); mpz_swap(nxt[j].Eq, cd->Eq); memcpy(nxt[j].ex, cd->ex, sizeof cd->ex); memcpy(nxt[j].v, cd->v, sizeof cd->v); nxt[j].cm = cd->cm; }
    State *sw = cur; cur = nxt; nxt = sw; ncur = m;
    double b = mpz_sizeinbase(ord[0]->D, 2) * 0.30103, md = mpz_sizeinbase(ord[m / 2]->D, 2) * 0.30103, wr = mpz_sizeinbase(ord[m - 1]->D, 2) * 0.30103;
    printf("level %d: best ~10^%.1f, median ~10^%.1f, worst ~10^%.1f, states %zu, rejected: shared-with-E %ld, big-shared %ld, other %ld, %lds (total %lds)\n",
           lev, b, md, wr, m, rejA, rejB, rejO, (long)(time(NULL) - tl), (long)(time(NULL) - t0));
    fflush(stdout);
    if (mpz_cmp_ui(ord[0]->D, 1) == 0) {
      snprintf(fn, sizeof fn, "%s_solution.txt", prefix); write_chain(fn, 0, lev);
      printf("REACHED D = 1 at level %d; chain written to %s\n", lev, fn); fflush(stdout); return 0;
    }
    if (lev % 25 == 0) { snprintf(fn, sizeof fn, "%s_ckpt.txt", prefix); write_chain(fn, 0, lev); }
  }
  snprintf(fn, sizeof fn, "%s_ckpt.txt", prefix); write_chain(fn, 0, maxlev);
  printf("stopped at level limit\n"); return 0;
}
