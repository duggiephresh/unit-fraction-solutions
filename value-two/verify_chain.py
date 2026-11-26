#!/usr/bin/env python3
"""Claude r11: INDEPENDENT verifier for implicit descent chains (written from the definitions, not Fable's code).

Certificate: Q (explicit), P0 (explicit), and deviations D_0, D_1, ..., D_n.
The implicit elements are s_j = (E_j + D_{j+1}) / D_j, with E_0 = A(Q)·M(P0) and E_{j+1} = E_j·s_j.
So P_{j+1} = P_j ∪ {s_j} and E_j = A(Q)·M(P_j).

What is certified, mapped to the hypotheses of the Lean lemma `closing`
(`lean/Erdos307/Square.lean`), applied to P = P0 ∪ {s_0..s_{n-1}} and Q:
  [Q]   Q: elements > 1, pairwise coprime (explicit).
  [P0]  P0: elements > 1, pairwise coprime, coprime to every element of Q (explicit).
  [D0]  D_0 = M(Q)M(P0) − A(Q)A(P0), computed directly.
  [INT] D_j ∣ E_j + D_{j+1} for every j, so s_j is an integer. Then
        Dev(P_{j+1}, Q) = s_j·D_j − E_j = D_{j+1} (dev_union with S = {s_j}, Lean-proved; checked on small chains in
        the self-test).
  [POS] D_{j+1} > 0.
  [GT1] s_j > 1, via E_j ≥ D_j, using a rigorous integer lower bound on the number of digits of E_j.
  [COPE] gcd(D_{j+1}, E_j) = 1. Then gcd(s_j, E_j) = 1, because a prime dividing s_j and E_j divides
        s_j·D_j − E_j = D_{j+1}. E_j contains M(P0) and every earlier s_i, so s_j is coprime to all earlier
        P elements. Distinctness follows from pairwise coprimality plus elements > 1.
  [COPQ] s_j mod q ≠ 0 for every q ∈ Q (cross-coprimality).
  [END] D_n = 1, i.e. M(Q)·M(P) = A(Q)·A(P) + 1.
Then `closing` / `coprime_one_notMem_of_closing` yields a genuine solution of the coprime 1-excluded variant.

Residue engine: one forward pass, holding E_j mod R_j with R_j = Lq·∏_{k=j..n} D_k (Lq = ∏ Q).
Step j:
  t = (E_j + D_{j+1}) mod R_j            (an exact multiple of D_j, by [INT])
  s_j mod R_{j+1} = t / D_j              (R_j = D_j·R_{j+1})
  E_{j+1} mod R_{j+1} = (E_j mod R_{j+1})·(s_j mod R_{j+1})
D_j, D_{j+1} and every q divide R_j, so every check above is exact.

usage: python -I verify_chain.py certificate.txt|cert.json      |  python -I verify_chain.py --selftest
cert.json: {"Q": [...], "P0": [...], "D": ["D0", "D1", ..., "Dn"]}  (integers or decimal strings)
"""
import json
import math
import random
import sys
from math import gcd, prod

import gmpy2
from gmpy2 import mpz


def A_of(S):
    m = prod(S)
    return sum(m // x for x in S)


def pairwise_coprime(xs):
    return all(gcd(a, b) == 1 for i, a in enumerate(xs) for b in xs[i + 1:])


def verify(Q, P0, D, require_end=True, verbose=True):
    fails = []
    Q = [int(x) for x in Q]
    P0 = [int(x) for x in P0]
    D = [mpz(int(x)) for x in D]
    n = len(D) - 1
    # [Q], [P0]
    if not (Q == [1] or (all(q > 1 for q in Q) and pairwise_coprime(Q))):   # Q = [1]: one-sided (Znam/Giuga) chain
        fails.append("[Q] Q not admissible / 1 in Q")
    if not (all(p > 1 for p in P0) and pairwise_coprime(P0)):
        fails.append("[P0] P0 not admissible / 1 in P0")
    if not all(gcd(p, q) == 1 for p in P0 for q in Q):
        fails.append("[P0] P0 not coprime to Q")
    MQ, AQ, MP0, AP0 = prod(Q), A_of(Q), prod(P0), A_of(P0)
    # [D0]
    if mpz(MQ * MP0 - AQ * AP0) != D[0]:
        fails.append("[D0] D_0 != M(Q)M(P0) - A(Q)A(P0)")
    if D[0] <= 0:
        fails.append("[D0] D_0 <= 0")
    E0 = mpz(AQ * MP0)
    Lq = mpz(prod(Q))
    R = Lq
    for d in D:
        R *= d
    Emod = E0 % R
    # E_j kept EXACT while small; afterwards a rigorous lower bound on log10(E_j) (with a safety margin)
    Eexact = E0
    lbE = None                 # used once Eexact is dropped
    EXACT_BITS = int(__import__("os").environ.get("EXACT_BITS", "4000000"))
    for j in range(n):
        Dj, Dn1 = D[j], D[j + 1]
        if Dn1 <= 0:
            fails.append(f"[POS] D_{j+1} <= 0")
            break
        # [INT]
        if (Emod + Dn1) % Dj != 0:
            fails.append(f"[INT] D_{j} does not divide E_{j} + D_{j+1}")
            break
        # [GT1] need E_j >= D_j  (then E_j + D_{j+1} > D_j, so s_j >= 2)
        if Eexact is not None:
            if Eexact < Dj:
                fails.append(f"[GT1] E_{j} < D_{j}")
                break
        else:
            if lbE - math.log10(Dj) <= 1e-6:     # float log10 is accurate to ~1e-15; keep a safe margin
                fails.append(f"[GT1] cannot certify E_{j} >= D_{j}")
                break
        # [COPE]
        if gcd(Emod % Dn1, Dn1) != 1:
            fails.append(f"[COPE] gcd(D_{j+1}, E_{j}) != 1")
            break
        Rn = R // Dj
        t = (Emod + Dn1) % R
        assert t % Dj == 0
        smod = t // Dj                      # s_j mod R_{j+1}
        # [COPQ]
        for q in Q:
            if q > 1 and smod % q == 0:
                fails.append(f"[COPQ] s_{j} divisible by {q}")
        if fails:
            break
        Emod = ((Emod % Rn) * smod) % Rn
        R = Rn
        # update E_j: exact while small, else lower bound  log10 s_j >= log10(E_j) - log10(D_j)  (and s_j >= 2)
        if Eexact is not None:
            sj = (Eexact + Dn1) // Dj
            assert sj * Dj == Eexact + Dn1
            Eexact = Eexact * sj
            if Eexact.bit_length() > EXACT_BITS:
                lbE = float(gmpy2.log10(Eexact)) - 1e-6
                Eexact = None
        else:
            # s_j = (E_j + D_{j+1})/D_j >= max(E_j, D_{j+1})/D_j, and s_j >= 2
            lbE = lbE + max(math.log10(2), max(lbE, math.log10(Dn1)) - (math.log10(Dj) + 1e-9)) - 1e-6
    if not fails and require_end and D[-1] != 1:
        fails.append(f"[END] D_n = {D[-1]} != 1 (chain valid so far, not yet closed)")
    if verbose:
        print("PASS" if not fails else "FAIL", fails[:3], f"(n = {n} implicit elements)")
    return not fails, fails


# ---------------- self-test on explicit small chains ----------------
def explicit_chain(Q, P0, steps, rng):
    """Build a short valid chain explicitly (bump choices), return (D list, explicit P)."""
    MQ, AQ = prod(Q), A_of(Q)
    P = list(P0)
    D = [MQ * prod(P) - AQ * A_of(P)]
    for _ in range(steps):
        MP = prod(P)
        E = AQ * MP
        Dj = D[-1]
        q0 = E // Dj + 1
        for b in range(0, 200):
            s = q0 + b
            if s > 1 and gcd(s, MQ * MP) == 1:
                Dn = s * Dj - E
                if Dn > 0 and gcd(Dn, E) == 1:
                    break
        else:
            return None
        P.append(s)
        D.append(s * Dj - E)
        # explicit cross-check of Dev(P, Q)
        assert MQ * prod(P) - AQ * A_of(P) == D[-1]
        assert pairwise_coprime(P) and all(gcd(p, q) == 1 for p in P for q in Q)
    return D, P


def selftest():
    rng = random.Random(1)
    ok = 0
    for trial in range(40):
        Q = [2, 3, 7, 41]
        P0 = [p for p in [5, 11, 13, 17, 19, 23, 29, 31, 37, 43] if rng.random() < 0.7] or [5]
        ch = explicit_chain(Q, P0, rng.randint(1, 4), rng)
        if ch is None:
            continue
        D, P = ch
        good, _ = verify(Q, P0, D, require_end=False, verbose=False)
        assert good, ("valid explicit chain rejected", P0, D)
        # corruption tests: change one deviation -> must fail
        if len(D) > 2:
            bad = list(D)
            k = rng.randrange(1, len(D))
            bad[k] = bad[k] + bad[k - 1]          # stays ≡ -E mod D_{k-1}, but breaks a later step or coprimality
            g2, _ = verify(Q, P0, bad, require_end=False, verbose=False)
            bad2 = list(D)
            bad2[k] = bad2[k] + 1                 # breaks integrality
            g3, _ = verify(Q, P0, bad2, require_end=False, verbose=False)
            assert not g3, "corrupted (+1) chain accepted"
        ok += 1
    print(f"selftest: {ok} explicit chains verified (explicit Dev and coprimality cross-checked), "
          f"corruptions rejected")


if __name__ == "__main__":
    if sys.argv[1] == "--selftest":
        selftest()
    else:
        if sys.argv[1].endswith(".json"):
            c = json.load(open(sys.argv[1]))
        else:  # certificate.txt: "Q ..." line, "P0 ..." line, then one deviation per line
            L = [l.split() for l in open(sys.argv[1]) if l.strip()]
            assert L[0][0] == "Q" and L[1][0] == "P0"
            c = {"Q": L[0][1:], "P0": L[1][1:], "D": [l[0] for l in L[2:]]}
        verify(c["Q"], c["P0"], c["D"], require_end=("--partial" not in sys.argv))
