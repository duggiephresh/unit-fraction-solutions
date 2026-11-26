# Value-2 results: Brenton–Hill n₀ = 2, and Giuga Problems 7 and 8

## `certificate.txt`
- **Line 1:** `Q 1`. This is a one-sided chain.
- **Line 2:** the seed {30, 7, 11, 13, …, 271}, 56 numbers.
- **Then:** 831 deviations d₀, …, d₈₃₀, with d₈₃₀ = 1.

Step j adds sⱼ = (Eⱼ + dⱼ₊₁)/dⱼ, where E₀ = ∏ seed and Eⱼ₊₁ = Eⱼ·sⱼ. After 830 steps the set P (886 numbers,
containing 30) is pairwise coprime and satisfies Σ1/x + 1/∏x = 1. Most elements are far too large to write down.

## Three results from one chain
Write N = ∏P.
1. **Replace 30 by 2, 3, 5.** Since 1/2 + 1/3 + 1/5 = 1 + 1/30, this gives 888 pairwise-coprime integers ≥ 2 with
   Σ1/x + 1/∏x = **2**. That answers Brenton–Hill (1988), equation (2) with n₀ = 2.
2. **Add N − 1 to that set.** The result is a Giuga sequence of value **2**, Σ1/x − 1/∏x = 2: Borwein et al. (1996),
   Problem 7.
3. **Add N − 1 to P itself.** The result is a Giuga sequence of value 1 with the same product N(N − 1) as (2): two
   distinct Giuga sequences with the same product, Problem 8.

## Checks
- `verify_chain.py certificate.txt` (needs `gmpy2`) certifies every step from residues: integrality, coprimality,
  growth, and the final deviation 1. Run `--selftest` first.
- Lean: `../lean/Erdos307/ValueTwo.lean` proves the residue checker's soundness (keeping the seed) and derives
  statements 1–3. `ValueTwoSolution.lean` runs the checker on this certificate with `decide +kernel`. Standard axioms
  only.

The chain was found by a residue-only beam descent (width 262,144, 40 minutes on a laptop).
