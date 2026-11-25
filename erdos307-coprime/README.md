# Coprime, 1-excluded variant of Erdős #307: certificate

## `certificate.txt`
- Line 1: `Q 2 3 7 41`, the starting Q.
- Line 2: `P0 5 11 13 …`, the starting P: the primes from 5 to 271 that are not in Q (54 primes).
- Then 914 lines: the deviations D₀, D₁, …, D₉₁₃, with D₉₁₃ = 1.

Step j adds the element sⱼ = (Eⱼ + Dⱼ₊₁)/Dⱼ to P, where E₀ = A(Q)·M(P₀) and Eⱼ₊₁ = Eⱼ·sⱼ (see `../docs/METHOD.md`).
After 913 steps the deviation is 1. The closing lemma then adds one element to P and one to Q:

    x = A(Q)M(P) + M(Q)²,   y = A(P)M(Q) + M(P)².

The result is the solution: |P| = 968, |Q| = 5, both pairwise coprime, 1 in neither, and
(Σ_P 1/p)(Σ_Q 1/q) = 1.

## Verifiers

Two verifiers were written independently. Either one certifies the whole result, and the Lean proof
(`../lean/Erdos307/CoprimeSolution.lean`) certifies it again.

- `verify_chain.py certificate.txt` (needs `gmpy2`) checks every hypothesis of the closing lemma from residues. Run
  `--selftest` first: it checks the verifier against small explicit chains and confirms that corrupted chains are
  rejected.
- `verify_independent.py certificate.txt` (pure Python) is a separate implementation. It also checks the final
  identity modulo several large primes.

Both finish in under a minute on a laptop.
