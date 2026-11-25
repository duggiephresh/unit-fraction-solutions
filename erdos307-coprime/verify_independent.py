#!/usr/bin/env python3
"""Independent verifier for a FixedQ chain (text format written by beamc). Exact integer arithmetic only:
no modular inverses, no CRT, no p-adic bookkeeping; it shares no code with the search programs.

Input file: line 1 "Q q1 q2 ...", line 2 "P0 p1 p2 ...", then the deviations D_0, D_1, ..., D_n (one per line).

Claim checked. Q and P0 are sets of distinct primes, disjoint, and no prime of P0 divides A(Q).
D_0 = M(Q)M(P0) - A(Q)A(P0) > 0.  With E_0 = A(Q) M(P0), define
    s_j = (E_j + D_{j+1}) / D_j,      E_{j+1} = E_j * s_j        (j = 0..n-1).
For every j, knowing E_j only modulo R_j = M(Q) * D_j * D_{j+1} * ... * D_n, the script checks
  (1) D_j divides E_j + D_{j+1}                 (s_j is an integer);
  (2) gcd(D_{j+1}, E_j) = 1                      (s_j is coprime to every element of P_j and to A(Q));
  (3) gcd(s_j mod M(Q), M(Q)) = 1                (s_j is coprime to Q);
  (4) s_j > 1                                    (from a rigorous lower bound on E_j).
Then P_{j+1} = P_j + {s_j}, Q is pairwise coprime with deviation exactly D_{j+1}, because
Dev(P + {s}, Q) = s * Dev(P, Q) - A(Q) M(P).
The first EXPL levels are also rebuilt with true integers (real gcds, deviation from its definition).
usage: verify2.py chain.txt [EXPL=10]
"""
import sys
import time
from math import gcd, prod

sys.set_int_max_str_digits(0)
lines = open(sys.argv[1]).read().split("\n")
EXPL = int(sys.argv[2]) if len(sys.argv) > 2 else 10
Q = [int(x) for x in lines[0].split()[1:]]
P0 = [int(x) for x in lines[1].split()[1:]]
chain = [int(x) for x in lines[2:] if x.strip()]
t0 = time.time()


def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))


MQ = prod(Q)
AQ = sum(MQ // q for q in Q)
assert all(is_prime(x) for x in Q + P0) and len(set(Q + P0)) == len(Q) + len(P0), "seed must be distinct primes"
M0 = prod(P0)
A0 = sum(M0 // p for p in P0)
assert gcd(M0, AQ) == 1, "P0 must be coprime to A(Q)"
assert chain[0] == MQ * M0 - AQ * A0 > 0, "seed deviation"
assert all(x > 0 for x in chain)
E0 = AQ * M0
n = len(chain) - 1

# explicit check of the first levels with true integers
M, A, D = M0, A0, chain[0]
for j in range(min(EXPL, n)):
    E = AQ * M
    assert (E + chain[j + 1]) % D == 0
    s = (E + chain[j + 1]) // D
    assert s > 1 and gcd(s, MQ * M) == 1, f"explicit level {j}: s not coprime"
    M, A = M * s, A * s + M
    D = MQ * M - AQ * A
    assert D == chain[j + 1], f"explicit level {j}: deviation mismatch"
print(f"explicit check: first {min(EXPL, n)} levels rebuilt with true integers (largest element has "
      f"{int(s.bit_length() * 0.30103) if n else 0} digits): OK", flush=True)

R = MQ * prod(chain)
e = E0 % R
lowbits = E0.bit_length() - 1                 # E_j >= 2**lowbits
sbits = 0
for j in range(n):
    Dj, Dn = chain[j], chain[j + 1]
    X = (e + Dn) % R
    assert X % Dj == 0, f"level {j}: s is not an integer"                         # (1)
    assert gcd(e % Dn, Dn) == 1, f"level {j}: gcd(D', E) != 1"                    # (2)
    R //= Dj
    s = X // Dj                               # s_j modulo R_{j+1}; MQ divides R_{j+1}
    assert gcd(s % MQ, MQ) == 1, f"level {j}: s shares a factor with M(Q)"        # (3)
    sbits = lowbits - Dj.bit_length()         # s_j > E_j / D_j >= 2**sbits
    assert sbits >= 1, f"level {j}: cannot certify s > 1"                         # (4)
    lowbits += sbits
    e = (e % R) * s % R
    if (j + 1) % 100 == 0:
        print(f"  {j + 1} / {n} levels ({time.time() - t0:.0f}s)", flush=True)
print(f"VERIFIED: {n} elements added to a seed of {len(P0)} primes, Q = {Q}; checks (1)-(4) hold at every level.")
print(f"final deviation: {chain[-1] if chain[-1] < 10 ** 40 else 'about 10^%d' % (len(str(chain[-1])) - 1)}")
print(f"last element exceeds 2^{sbits}" + (f" (more than 10^{int(sbits * 0.30103)})" if sbits else ""))
if chain[-1] == 1:
    print("Final deviation is 1. Closing lemma: x = A(Q)M(P) + M(Q)^2 joins P and y = A(P)M(Q) + M(P)^2 joins Q;")
    print("then (sum 1/p)(sum 1/q) = 1 exactly, and P+{x}, Q+{y} is pairwise coprime.")
    # Sanity check of the final identity A(P')A(Q') = M(P')M(Q') modulo three large primes (not part of the proof:
    # the proof is the closing lemma). Residues of the elements are obtained by the same exact-division pass.
    for ell in (2 ** 61 - 1, 2 ** 89 - 1, 2 ** 127 - 1):
        Rl = ell * prod(chain)
        el, Ml, Al = E0 % Rl, M0 % Rl, A0 % Rl
        for j in range(n):
            Xl = (el + chain[j + 1]) % Rl
            Rl //= chain[j]
            sl = Xl // chain[j]
            el, Ml, Al = (el % Rl) * sl % Rl, (Ml * sl) % Rl, (Al * sl + Ml) % Rl      # A <- A*s + M(old)
        Ml, Al = Ml % ell, Al % ell
        assert (MQ * Ml - AQ * Al) % ell == 1, "deviation of the final state is not 1 modulo the test prime"
        x = (AQ * Ml + MQ * MQ) % ell
        y = (Al * MQ + Ml * Ml) % ell
        lhs = (Al * x + Ml) * (AQ * y + MQ) % ell
        rhs = (Ml * x) * (MQ * y) % ell
        assert lhs == rhs, "final identity fails modulo a test prime"
    print("sanity: A(P')A(Q') = M(P')M(Q') holds modulo 2^61-1, 2^89-1 and 2^127-1")
print(f"time {time.time() - t0:.0f}s")
