# Six open unit-fraction questions, answered with machine-checked certificates

This repository contains six results found on 25 November 2026, each with a certificate that you can check yourself
and a Lean 4 proof checked by Lean's kernel. Only the standard axioms are used (`propext`, `Classical.choice`,
`Quot.sound`). There is no `sorry` and no `native_decide`.

| Result | Status before | Lean theorem |
|---|---|---|
| **An odd solution of Znám's problem.** 24 odd integers, each a proper divisor of the product of the others plus 1. | No all-odd solution was known (Brenton–Joo 1995). Brenton–Hill (1988) proved that one needs at least 12 terms. Wikipedia, 2005–2026: "It is unknown whether there are any solutions to Znám's problem using only odd numbers". | `ZnamOdd.odd_znam_solution` |
| **A solution of the coprime, 1-excluded variant of Erdős Problem #307.** Finite sets P, Q of integers > 1, each pairwise coprime, 1 ∉ P ∪ Q, with (Σ_{p∈P} 1/p)(Σ_{q∈Q} 1/q) = 1. | Listed as research open, "no examples known", in google-deepmind/formal-conjectures (`erdos_307.variants.coprime_one_notMem`). | `Erdos307.coprime_one_notMem_solved` |
| **An odd Giuga sequence.** 26 odd integers with Σ1/x − 1/∏x = 1; each divides (product of the others) − 1. | Borwein–Borwein–Borwein–Girgensohn, Amer. Math. Monthly 103 (1996), Problem 3: "Find a Giuga sequence which consists of odd factors … only". Brenton–Joo (1995): "no solution … is known with each nᵢ odd". | `GiugaOdd.odd_giuga_sequence` |
| **Brenton–Hill's equation with n₀ = 2.** 888 pairwise-coprime integers ≥ 2 with Σ1/x + 1/∏x = 2. | Brenton–Hill (1988): "no solution to (2) is known for n₀ > 1". Brenton–Vasiliu (2002): "an unsolved problem". | `Erdos307.ValueTwoSolution.brentonHill_value_two` |
| **A Giuga sequence of value 2.** Σ1/x − 1/∏x = 2. | BBBG (1996), Problem 7: "Are there Giuga sequences with a sum minus product value higher than 1?" | `Erdos307.ValueTwoSolution.giuga_value_two` |
| **Two distinct Giuga sequences with the same product.** | BBBG (1996), Problem 8. | `Erdos307.ValueTwoSolution.giuga_same_product` |

The last three come from one implicit chain of 830 steps; see `value-two/README.md`.

None of these results touches the prime versions: Erdős #307 for primes, odd primary pseudoperfect numbers, odd
Giuga numbers, and Giuga's conjecture. All remain open. Please treat these as **new claims awaiting independent review**. Corrections and prior art we missed are very
welcome (open an issue).

## Check it yourself

**Odd Znám, in seconds, with plain Python** (no dependencies):

```
python3 odd-znam/check.py
```

This reads the 24 numbers in `odd-znam/odd_znam_solution.txt` (the largest has 62,037 digits) and checks, directly from
the definition, that each is odd, greater than 1, divides (product of the others) + 1, and is not equal to it. A PARI/GP
version is in `odd-znam/check.gp`.

**Erdős #307 coprime variant.** This solution has 973 elements, most of them far too large to write down; the largest
has more than 5.9·10²⁸¹ digits. It is given implicitly by a list of 914 small numbers (the *deviations*), and every
required property is certified from residues. See `erdos307-coprime/README.md`.

```
pip install gmpy2
python3 erdos307-coprime/verify_chain.py --selftest
python3 erdos307-coprime/verify_chain.py erdos307-coprime/certificate.txt
python3 erdos307-coprime/verify_independent.py erdos307-coprime/certificate.txt
```

**Odd Giuga sequence, plain Python:** `python3 odd-giuga/check.py`. It checks the 26 numbers (the largest has 351,997
digits) directly from the definition.

**Value-2 results:** `python3 value-two/verify_chain.py value-two/certificate.txt`. It certifies the 830-step chain
from residues (`gmpy2` needed).

**Lean (all six results):**

```
cd lean
lake exe cache get
lake build
# then, in a Lean file:  #print axioms ZnamOdd.odd_znam_solution
#                        #print axioms Erdos307.coprime_one_notMem_solved
#                        #print axioms GiugaOdd.odd_giuga_sequence
#                        #print axioms Erdos307.ValueTwoSolution.giuga_same_product   (and the other two)
```

## How it was found

Both results come from one method, a **residue-steered implicit descent**, described in `docs/METHOD.md`. In short:

- Grow a set of pairwise coprime integers one element at a time. Each step replaces the current "deviation" D (how far
  the reciprocal sum is from the target, scaled) with a freely chosen new deviation D′ ≡ −E (mod D). A wide beam
  search steers D down to 1.
- The elements grow doubly exponentially, so they are never written down. A state is stored as its list of small
  deviations, and every condition (integrality, coprimality, oddness) is certified from residues.
- For Znám's problem the descent closed in 16 steps from the seed of odd primes {3, 5, 7, 11, 13, 17, 19, 23}, small enough to write the
  solution out in full. For Erdős #307 it took 913 steps from the seed Q = {2, 3, 7, 41}, P₀ = primes 5..271. A Lean
  "closing lemma" then adds one element to each side.
- The Lean proof of the #307 result proves a residue checker sound, by induction along the chain, and lets the kernel
  run it on the certificate.

The single step, and the "remainder" bookkeeping it uses, go back to Brenton & Hill (1988), Brenton & Bruner (1994)
and Brenton & Joo (1995). What we believe is new is the long, search-steered descent through arbitrary deviations, its
implicit representation and residue certification, and the formal check. See `docs/PRIOR_ART.md`.

## Repository layout

```
odd-znam/            the 24 numbers, check.py, check.gp
erdos307-coprime/    certificate.txt (914 deviations), two independent verifiers, README
odd-giuga/           the 26 numbers, check.py
value-two/           certificate.txt (831 deviations), verifier, README
lean/                Lean 4 + Mathlib project: both theorems and the support library
search/              the search programs (beam descents in C, closing search in Python)
docs/                METHOD.md, PRIOR_ART.md
```

## Credits and AI use

Directed by Doug Phillips. The work was done with AI systems, and we disclose that plainly:
- **Claude (Anthropic):**
  - the reductions and Lean library (forcing, closing lemma, descent framework);
  - the residue checker and its soundness proof;
  - the independent verifier `verify_chain.py` and the closing search;
  - the explicit verification of the Znám solution.
- **A second Claude session:** the residue-only beam search that found both certificates (`search/beamc.c`,
  `search/beamz.c`), and the independent verifier `verify_independent.py`.
- **Gemini (Google):** earlier rounds of the surrounding project (lower bounds, obstruction results), not included
  here.

Correctness does not rest on trusting any model. The Znám solution is checked by a short script anyone can read; the
#307 result is checked by Lean's kernel.

## License

Code (`*.py`, `*.c`, `*.gp`, `*.lean`) is under the Apache License 2.0 (`LICENSE`). Data and documentation
(`*.txt` certificates, `*.md`) are under CC BY 4.0 (https://creativecommons.org/licenses/by/4.0/).

## Citation

See `CITATION.cff`.
