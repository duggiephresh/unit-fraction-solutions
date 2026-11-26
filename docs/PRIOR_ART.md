# Prior art (literature search, November 2026)

We would be glad to hear of anything we missed. Please open an issue.

## The method

**The state and the single step are classical.**
- **Brenton & Hill**, *On the Diophantine equation 1 = Σ1/nᵢ + 1/∏nᵢ and a class of homologically trivial complex
  surface singularities*, Pacific J. Math. 133 (1988) 41–67:
  - the "sequence of remainders", which is our deviation D;
  - completion from a remainder in a few steps;
  - congruence constraints on remainders;
  - exhaustive small tree searches;
  - Problem 3, on greedy remainder rules.
- **Brenton & Bruner**, *On recursive solutions of a unit fraction equation*, J. Austral. Math. Soc. 57 (1994)
  341–356:
  - Sylvester chains (D = 1 at every step) tracked modulo primes, which proves that very long solutions exist without
    writing them out;
  - short tails with D ≠ 1.
- **Brenton & Joo**, *On the system of congruences ∏_{j≠i} nⱼ ≡ 1 mod nᵢ*, Fibonacci Quart. 33 (1995): the same step,
  with residue arguments.
- **H. Wang** (arXiv:2605.21518, 2026): the same transition ("ports"), with a composition law.

**What we did not find:**
- long, search-steered descents through arbitrary deviations D ≠ 1 (hundreds of steps);
- a state stored only as its deviation list, with residues rebuilt modulo m·∏D_k;
- per-step residue certification of integrality, coprimality and side conditions across such chains;
- a formal certificate, checked by a checker proved sound, for objects too large to write down.

Proof by reflection and `decide +kernel` on explicit witnesses are standard. We did not find them used for implicit
witnesses.

**Not consulted:**
- Butske, Jaje & Mayernik (Math. Comp. 69, 2000);
- Brenton & Vasiliu (2002);
- Girgensohn (1996);
- Chinese-language work of Sun (1983), Cao–Liu–Zhang (1987) and Sun–Cao (1988).

## Odd solution of Znám's problem

- **Brenton & Hill 1988:** an all-odd solution needs at least 12 terms, and the number of terms is ≡ 0 (mod 4). Ours
  has 24 terms, which satisfies both. (Their open question 2 asks something different: whether every starting set can be completed using odd
  integers.)
- **Brenton & Joo**, "On the system of congruences ∏_{j≠i} nⱼ ≡ 1 mod nᵢ", Fibonacci Quart. 33 (1995) 258–;
  submitted November 1993. They write: "no solution to (1) or (2) is known with each nᵢ odd". Here (2) is the
  Znám-type system ∏_{j≠i} nⱼ ≡ −1 mod nᵢ, and (1) is the Giuga-type system ∏_{j≠i} nⱼ ≡ 1 mod nᵢ. So the remark
  covers both our odd Znám solution and the odd Giuga sequence (read in the Dalhousie scan, 2026-11-25).
- **Known lists** (Brenton–Vasiliu for k = 5–8; MathWorld; OEIS A075441, A075461, A054377): every listed solution
  contains an even term.
- **Wikipedia, "Znám's problem":** says it is unknown whether any all-odd solution exists, in every revision from 2005
  to 2026.

## Coprime 1-excluded variant of Erdős #307

- **google-deepmind/formal-conjectures** `ErdosProblems/307.lean`: `erdos_307.variants.coprime_one_notMem` is marked
  research open, "no examples known". The 1-allowed variant was solved earlier, with {1,5} and {2,3}.
- **V. Bonfioli** (github ElVec1o/erdos307): lower bounds for this variant, at least 60 elements and min(∏P, ∏Q) >
  3.5·10⁵⁷. Our solution (973 elements, 5 in Q) is consistent with them.
- **erdosproblems.com/307 and its forum:** we found no 1-free example reported there.

## Odd Giuga sequence
- **Borwein–Borwein–Borwein–Girgensohn**, Amer. Math. Monthly 103 (1996):
  - Problem 3;
  - "We have found no Giuga sequence which consists of odd factors";
  - for all-odd sequences, m ≡ v + 1 (mod 4);
  - m ≤ 10 ruled out by computer; m = 14 "too many initial segments".

  Ours: m = 26, v = 1.
- **Brenton–Joo (1995):** "no solution to (1) or (2) is known with each nᵢ odd". Their system (1) is the
  Giuga-sequence condition.
- **J. R. Hobart**, MSc thesis, UNBC (2005): "No such sequence has been found".
- Later Giuga work (Grau–Oller-Marcén 2011–12; Svinin 2026) and OEIS treat odd Giuga NUMBERS (primes) as open and say
  nothing on sequences. Our sequence uses composites and does not touch Giuga's conjecture.

## Value-2 results
- **Brenton–Hill (1988),** p. 41: "no solution to (2) is known for n₀ > 1". Prop. 6: at least 59 terms are needed.
- **Brenton–Vasiliu,** Math. Mag. 75 (2002): "Can r > 1 ever occur? This is an unsolved problem." This was read from a
  poor scan; check the printed page.
- **BBBG (1996), Problems 7 and 8.** Problem 9's remark sketches the same-product, higher-value idea. Hobart (2005)
  lists both as open (#10, #11).

**Not reached:**
- Borwein–Wong (1997);
- Butske–Jaje–Mayernik (2000);
- a MathSciNet citation search.
