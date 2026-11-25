#!/usr/bin/env python3
"""Claude r11: CLOSING SEARCH. Finish an implicit descent chain to D = 1 with one or two more elements.

State: chain (Q, P0, D_0..D_n) as in verify_chain.py. Write D = D_n and E = E_n (implicit; E_0 = A(Q)·M(P0),
E_{j+1} = E_j·(E_j + D_{j+1})/D_j).
  1-element finish: r0 := (−E) mod D = 1. Then s = (E+1)/D and the new deviation is 1.
  2-element finish: G ≡ −E (mod D), G > 0, with G | E² + D. Then s = (E+G)/D gives deviation G, and
                    x = (E·s + 1)/G gives deviation x·G − E·s = 1.
                    (Proof: s ≡ E·D⁻¹ mod G, so E·s + 1 ≡ D⁻¹(E² + D) mod G. Note gcd(D, G) = gcd(D, E) = 1.)
Candidates: G = r0 + a·D, a = 0..A. Heuristic hit chance ≈ Σ 1/G ≈ H_A / D per state, so small a dominates.
Validity (beyond the divisibility): gcd(G, E) = 1, and s, x ≢ 0 mod every q ∈ Q. The extended chain
[..., G, 1] is then RE-VERIFIED from scratch by verify_chain.verify (all `closing` hypotheses, end D = 1).

Residues: one forward pass computes E mod (Lq·Gprod·D_n), with Gprod = ∏ of a batch of candidates, using the
same engine as verify_chain (modulus R_j = Lq·Gprod·∏_{k≥j} D_k).
usage: python -I closing_search.py chain.txt|chain.json [A] [batch]
"""
import json
import os
import sys
import time
from math import gcd, prod

import gmpy2
from gmpy2 import mpz

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "erdos307-coprime"))
import verify_chain as V


def load_chain(path):
    if path.endswith(".json"):
        c = json.load(open(path))
        return [int(x) for x in c["Q"]], [int(x) for x in c["P0"]], [mpz(int(x)) for x in c["D"]]
    L = [l for l in open(path).read().split("\n") if l.strip()]
    Q = list(map(int, L[0].split()[1:]))
    P0 = list(map(int, L[1].split()[1:]))
    D = [mpz(int(x)) for x in L[2:]]
    return Q, P0, D


def E_mod(Q, P0, D, extra):
    """E_n mod (Lq·extra·D_n) by the forward residue pass."""
    Lq = mpz(prod(Q))
    E0 = mpz(V.A_of(Q) * prod(P0))
    n = len(D) - 1
    R = Lq * mpz(extra)
    for d in D:
        R *= d
    Em = E0 % R
    for j in range(n):
        Dj, Dn1 = D[j], D[j + 1]
        Rn = R // Dj
        t = (Em + Dn1) % R
        assert t % Dj == 0, "chain not integral"
        sm = t // Dj
        Em = ((Em % Rn) * sm) % Rn
        R = Rn
    return Em, R          # R = Lq·extra·D_n


def closing_search(Q, P0, D, A=10000, batch=2000, verbose=True):
    Dn = D[-1]
    Lq = prod(Q)
    t0 = time.time()
    # r0 from E mod D_n (extra = 1)
    Em1, _ = E_mod(Q, P0, D, 1)
    r0 = int((-Em1) % Dn)
    # 1-element finish
    if r0 == 1:
        ext = list(D) + [mpz(1)]
        ok, f = V.verify(Q, P0, ext, require_end=True, verbose=False)
        if ok:
            return ext, "1-element"
    for start in range(0, A + 1, batch):
        Gs = [r0 + a * int(Dn) for a in range(start, min(A + 1, start + batch)) if r0 + a * int(Dn) > 1]
        if not Gs:
            continue
        Gprod = prod(Gs)
        Em, R = E_mod(Q, P0, D, Gprod)
        for G in Gs:
            e = int(Em % G)
            if (e * e + int(Dn)) % G:
                continue
            if gcd(G, e) != 1:
                continue
            # s, x mod q (need E mod q·G·D_n; R contains Lq·Gprod·D_n)
            mq = Lq * G * int(Dn)
            Eq = int(Em % mq)
            s_mod = ((Eq + G) % mq) // int(Dn)          # s mod (Lq·G)
            good = True
            for q in Q:
                sq = s_mod % q
                xq_num = (Eq % (q * G) * (s_mod % (q * G)) + 1) % (q * G)
                if sq == 0 or xq_num % G != 0 or (xq_num // G) % q == 0:
                    good = False
                    break
            if not good:
                continue
            ext = list(D) + [mpz(G), mpz(1)]
            ok, f = V.verify(Q, P0, ext, require_end=True, verbose=False)
            if verbose:
                print(f"  candidate G = {G} (a = {(G - r0) // int(Dn)}): full re-verification "
                      f"{'PASS' if ok else 'FAIL ' + str(f[:1])}", flush=True)
            if ok:
                return ext, "2-element"
    if verbose:
        print(f"  no closing with a <= {A} (D has {len(str(Dn))} digits, {time.time() - t0:.1f}s)", flush=True)
    return None, None


def selftest():
    """Build small explicit chains, then check that every closing found is a genuine solution (explicitly)."""
    import random
    from fractions import Fraction
    rng = random.Random(3)
    found = 0
    tried = 0
    for trial in range(300):
        Q = [2, 3, 7, 41]
        P0 = [p for p in [5, 11, 13, 17, 19, 23, 29, 31, 37, 43] if rng.random() < 0.5] or [5]
        ch = V.explicit_chain(Q, P0, rng.randint(0, 2), rng)
        if ch is None:
            continue
        D, P = ch
        tried += 1
        ext, kind = closing_search(Q, P0, [mpz(d) for d in D], A=3000, batch=500, verbose=False)
        if ext is None:
            continue
        # rebuild the explicit elements and check Dev = 1 directly, then the closing lemma's solution
        MQ, AQ = prod(Q), V.A_of(Q)
        Pe = list(P0)
        E = AQ * prod(Pe)
        for j in range(len(ext) - 1):
            s = (E + int(ext[j + 1])) // int(ext[j])
            assert s * int(ext[j]) == E + int(ext[j + 1])
            Pe.append(s)
            E *= s
        assert MQ * prod(Pe) - AQ * V.A_of(Pe) == 1, "Dev != 1"
        assert V.pairwise_coprime(Pe) and all(gcd(p, q) == 1 for p in Pe for q in Q) and 1 not in Pe
        MP, AP = prod(Pe), V.A_of(Pe)
        xP = MQ ** 2 + AQ * MP          # closing elements from the Lean `closing` lemma
        yQ = MQ * AP + MP ** 2
        PP, QQ = Pe + [xP], Q + [yQ]
        assert sum(Fraction(1, a) for a in PP) * sum(Fraction(1, b) for b in QQ) == 1
        assert V.pairwise_coprime(PP) and V.pairwise_coprime(QQ) and 1 not in PP + QQ
        found += 1
    print(f"selftest: {tried} small explicit states searched, {found} closings found; every one rebuilt "
          f"explicitly gives Dev = 1 AND, after the closing lemma's two elements, an exact coprime 1-free solution")


if __name__ == "__main__":
    if sys.argv[1] == "--selftest":
        selftest()
    else:
        Q, P0, D = load_chain(sys.argv[1])
        A = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
        B = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
        print(f"state: {len(D) - 1} implicit elements, D has {len(str(D[-1]))} digits")
        ext, kind = closing_search(Q, P0, D, A, B)
        if ext is not None:
            out = sys.argv[1] + ".closed.json"
            json.dump({"Q": Q, "P0": P0, "D": [str(x) for x in ext]}, open(out, "w"))
            print(f"*** CLOSED ({kind}); extended chain written to {out}; independently re-verified PASS")
