# Six open unit-fraction questions, answered with machine-checked certificates

Six results found on 25 November 2026. Each comes with a certificate you can check yourself and a Lean 4 proof checked by Lean's kernel, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`.

| # | Result | Size |
|---|---|---|
| 1 | A solution of the **coprime, 1-excluded variant of Erdős Problem #307** | 973 integers (implicit) |
| 2 | An **odd solution of Znám's problem** | 24 integers (explicit) |
| 3 | An **odd Giuga sequence** | 26 integers (explicit) |
| 4 | A solution of **Brenton–Hill's equation with n₀ = 2** | 888 integers (implicit) |
| 5 | A **Giuga sequence of value 2** | 889 integers (implicit) |
| 6 | **Two distinct Giuga sequences with the same product** | 887 and 889 integers (implicit) |

None of these touches the prime versions (Erdős #307 for primes, odd primary pseudoperfect numbers, odd Giuga numbers, Giuga's conjecture). All of those remain open.

Please treat these as **new claims awaiting independent review**. Corrections, and prior art we missed, are very welcome: open an issue.

## The questions, and where they were posed

1. **Erdős #307, coprime variant.** Find finite sets P, Q of integers > 1, each pairwise coprime, with 1 ∉ P ∪ Q and (Σ 1/p)(Σ 1/q) = 1. It is listed as research open, with "no examples known", in google-deepmind/formal-conjectures (`erdos_307.variants.coprime_one_notMem`) and on erdosproblems.com/307.
2. **Odd Znám.** Find odd integers > 1, each a proper divisor of (product of the others) + 1. Brenton–Joo (1995) wrote that "no solution … is known with each nᵢ odd". Brenton–Hill (1988) showed that one needs at least 12 terms. Wikipedia, 2005–2026, says "It is unknown whether there are any solutions to Znám's problem using only odd numbers".
3. **Odd Giuga sequence.** Find odd integers with Σ 1/x − 1/∏x a positive integer. This is Borwein–Borwein–Borwein–Girgensohn, *Amer. Math. Monthly* 103 (1996), Problem 3. Brenton–Joo (1995) also note that none was known.
4. **Brenton–Hill, n₀ = 2.** Find pairwise-coprime integers ≥ 2 with Σ 1/x + 1/∏x = 2. Brenton–Hill (1988) write that "no solution to (2) is known for n₀ > 1"; Brenton–Vasiliu (2002) call it "an unsolved problem".
5. **Giuga value 2.** BBBG (1996), Problem 7: "Are there Giuga sequences with a sum minus product value higher than 1?"
6. **Same product.** BBBG (1996), Problem 8: "Are there two distinct Giuga sequences whose elements have the same product?"

## Check it yourself

| Result | Command | Needs |
|---|---|---|
| Odd Znám | `python3 odd-znam/check.py` | plain Python |
| Odd Giuga | `python3 odd-giuga/check.py` | plain Python |
| Erdős #307 | `python3 erdos307-coprime/verify_chain.py erdos307-coprime/certificate.txt` | `pip install gmpy2` |
| Erdős #307 (second verifier) | `python3 erdos307-coprime/verify_independent.py erdos307-coprime/certificate.txt` | plain Python |
| Results 4–6 | `python3 value-two/verify_chain.py value-two/certificate.txt` | `gmpy2` |

The explicit results (2, 3) are checked straight from the definition; the largest numbers have 62,037 and 351,997 digits. The implicit results (1, 4–6) have elements far too large to write down. Each is given by a list of small numbers (the *deviations*), and every property is certified from residues. See `erdos307-coprime/README.md` and `value-two/README.md`.

**Lean, all six:**

```
cd lean
lake exe cache get
lake build
```

| Result | Lean theorem |
|---|---|
| 1 | `Erdos307.coprime_one_notMem_solved` |
| 2 | `ZnamOdd.odd_znam_solution` |
| 3 | `GiugaOdd.odd_giuga_sequence` |
| 4 | `Erdos307.ValueTwoSolution.brentonHill_value_two` |
| 5 | `Erdos307.ValueTwoSolution.giuga_value_two` |
| 6 | `Erdos307.ValueTwoSolution.giuga_same_product` |

Results 1 and 2 are registered in the [Palomar](https://palomar-registry.org/) registry as [PALOMAR-2026-11-26-000045](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000045), independently re-verified with three separate proof kernels. Results 3–6 are registered as [PALOMAR-2026-11-27-000035](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-27-000035).

## How it was found

All six come from one method, a **residue-steered implicit descent** (details in `docs/METHOD.md`):

- **Steering.** Grow a set of pairwise-coprime integers one element at a time. Each step replaces the current *deviation* D (how far the reciprocal sum is from the target, scaled) with a freely chosen D′ ≡ −E (mod D). A wide beam search steers D to the target: +1 for Znám-type, −1 for Giuga-type.
- **Implicit state.** The elements grow doubly exponentially, so they are never written down. A state is just its list of deviations, and integrality, coprimality and oddness are certified from residues.
- **Formal check.** A Lean checker, proved sound by induction along the chain, is run on each certificate by the kernel.
- **The value-2 trick.** Since 1/2 + 1/3 + 1/5 = 1 + 1/30, swapping 30 for {2, 3, 5} raises the value by exactly 1 and keeps the product. So one 830-step chain gives results 4, 5 and 6.

The single step goes back to Brenton & Hill (1988), Brenton & Bruner (1994) and Brenton & Joo (1995). What we believe is new is the long, search-steered descent through arbitrary deviations, its implicit representation and residue certification, and the formal check. See `docs/PRIOR_ART.md`.

## Repository layout

```
erdos307-coprime/   result 1: certificate (914 deviations), two verifiers
odd-znam/           result 2: the 24 numbers, check.py, check.gp
odd-giuga/          result 3: the 26 numbers, check.py
value-two/          results 4-6: certificate (831 deviations), verifier
lean/               Lean 4 + Mathlib: all six theorems and the support library
search/             the search programs (beam descents in C, closing search in Python)
docs/               METHOD.md, PRIOR_ART.md
```

## Credits and AI use

**How this was produced.** The mathematics here (methods, searches, proofs, verifiers and drafting) was produced by AI agents (Claude, Anthropic). Doug Phillips ran the project: he set the goals, directed the work, and is responsible for publishing it and for corrections. He did not independently verify the mathematics. In [CRediT](https://credit.niso.org/) terms his roles are Project administration, Resources, and Conceptualization in the sense of setting the research goals. Following the Leiden Declaration, AI systems are not listed as authors.

**Verification and review.** Correctness of the stated theorems rests on Lean kernel checks, independently re-verified by the Palomar registry with three separate kernels, and on independent verifier programs. **No human mathematician has yet reviewed this work.** Expert review and corrections are very welcome.

In more detail:

- **Claude (Anthropic):** the reductions and the Lean library, the residue checkers and their soundness proofs, the verifiers, and the Giuga and value-2 adaptations.
- **A second Claude session:** the residue-only beam searches that found the certificates (`search/`), and an independent verifier.
- **Gemini (Google):** earlier rounds of the surrounding project (lower bounds and obstruction results), not included here.

Correctness does not rest on trusting any model: the explicit results are checked by short scripts anyone can read, and all six are checked by Lean's kernel.

## License and citation

Code (`*.py`, `*.c`, `*.gp`, `*.lean`) is under the Apache License 2.0 (`LICENSE`). Data and documentation (`*.txt`, `*.md`) are under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). To cite, see `CITATION.cff`.
