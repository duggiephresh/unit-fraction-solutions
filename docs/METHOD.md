# Method: residue-steered implicit descent

## Setup

For a finite set S of positive integers, write M(S) = ∏_{s∈S} s and A(S) = Σ_{s∈S} M(S)/s, so that Σ 1/s = A(S)/M(S).

Erdős #307 asks for (Σ_P 1/p)(Σ_Q 1/q) = 1, i.e. A(P)A(Q) = M(P)M(Q). Fix Q and build P one element at a time,
tracking the **deviation**

    D = Dev(P, Q) = M(Q)M(P) − A(Q)A(P),        E = A(Q)M(P).

Znám's problem is the one-sided case Q = {1}. There D = M(P) − A(P), and D = 1 is exactly Σ 1/x + 1/∏x = 1. That is
the "improper" Znám condition, and it is proper when the last step starts from D > 1.

## One step

Pick a new deviation D′ with D′ ≡ −E (mod D) and set

    s = (E + D′)/D,    P ← P ∪ {s},    E ← E·s.

A direct computation gives Dev(P ∪ {s}, Q) = s·D − E = D′. If gcd(D′, E) = 1, then s is coprime to everything
already in P and Q, because any prime dividing both s and E divides s·D − E = D′. This is the same step as Brenton–Hill's
"sequence of remainders" (see PRIOR_ART.md). With D′ = 1 at every step it is a Sylvester-type chain.

## What is different here

1. **Steering.** D′ can be any number in the right residue class that passes the coprimality test. We keep a beam of
   the best states (scored by log D′ with look-ahead) and push D down over hundreds of steps until D = 1. The run
   that solved #307 took 913 steps. The Znám run took 16.
2. **Implicit state.** s grows doubly exponentially, so we never compute it. A state is just the list
   D₀, D₁, …, Dₙ. To check step j we need E_j modulo a few numbers. Since E_{j+1} = E_j (E_j + D_{j+1}) / D_j, and
   the division by D_j is exact, we carry E_j modulo m·∏_{k≥j} D_k, divide out D_j at each step, and keep exact
   residues of E modulo every later deviation and every q ∈ Q.
3. **Residue certification.** Every hypothesis is checked from those residues:
   - integrality: D_j | E_j + D_{j+1};
   - coprimality: gcd(D_{j+1}, E_j) = 1;
   - each new element coprime to each q ∈ Q;
   - s > 1 and distinctness, via a lower bound on E;
   - for Znám, oddness of every element.
4. **Closing.** When D = 1, the closing lemma adds x = A(Q)M(P) + M(Q)² to P and y = A(P)M(Q) + M(P)² to Q. This gives
   an exact solution with both sides pairwise coprime and 1 excluded.
5. **Formal check.** `lean/Erdos307/ImplicitChain.lean` defines a computable checker `stepCheck` on the deviation
   list and proves it sound by induction along the chain: if it returns true, the solution exists.
   `CoprimeSolution.lean` runs it on the certificate with `decide +kernel`. Lean's kernel never sees the huge
   elements, only the residue arithmetic.

## Why the Znám solution could be written out

From the seed {3, 5, 7, 11, 13, 17, 19, 23}, the descent reached D = 1 in 16 steps, while the elements were still small
enough to compute (the largest has 62,037 digits), so all 24 numbers are printed in full.
`lean/Erdos307/OddZnam.lean` checks the definition directly on those numbers.

## Searching

The search programs are `search/beamc.c` (#307) and `search/beamz.c` (Znám). `search/closing_search.py` is an
alternative two-element closing search used for diagnostics. They are research code: they found the certificates,
but the verifiers and the Lean proof never trust them.
