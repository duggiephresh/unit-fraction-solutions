# Written on the Wall II, conjecture 189: two families that rule out natural proof routes

**Conjecture 189 (Graffiti.pc):** if G is connected with n > 1 and every vertex v has distEven(v) ≤ 1 + σ(G), then G
has a Hamiltonian path. Here distEven(v) is the number of vertices at even distance from v (v included), and σ is the
second-smallest degree. The conjecture is **open**.

**Known partial results** (not ours): Easwar & Johari, arXiv:2609.11719 (diameter ≤ 2; n ≤ 2σ + 2; n = 2σ + 3 when
2-connected; every graph that is not 2-connected). A large set of Lean-checked cases by
[vjdad4m/maths](https://github.com/vjdad4m/maths): σ = 3, all of σ = 4, κ ≥ σ − 1 for every σ, and triangle-free
2-connected graphs for every σ.

The remaining open region is roughly: 2-connected, containing a triangle, 2 ≤ κ ≤ σ − 2, diameter 3–5, n ≥ 2σ + 4.

## The two families
**Neither is a counterexample to #189:** every member checked has a Hamiltonian path. Each refutes a lemma that a
uniform proof might naturally aim for. Run `python3 verify_families.py` (needs networkx) to recheck every claim below.

1. **F_L (L ≥ 16): minimum cuts with three components.** This is the clique blow-up of the 8-vertex base `G?qtfo`, with
   classes A, B, D, P, Q, x, y, Z of sizes L−12, 4, 2, 6, 6, 1, 1, L−4, and base edges A–D, A–x, A–y, A–Z, B–D, B–Z,
   D–Z, P–x, P–y, P–Z, Q–x, Q–y, Q–Z.
   - It satisfies (H) with equality, has n = 2σ + 4, diameter 3, triangles, and κ = σ − 2.
   - The minimum cut S = x ∪ y ∪ Z leaves **three** components.
   - So "in the open region every minimum cut leaves exactly two components" is **false** for σ ≥ 15. (Exhaustive
     searches up to σ = 12 found no such cut, which is why it looks true at small σ.)
2. **E_m (m ≥ 3): both classical traceability certificates fail.** This is the blow-up of the 6-cycle with classes
   V0..V5 of sizes 2, m, m, m, m−1, m, where V0 and V2 are independent sets and the rest are cliques.
   - It satisfies (H) with equality, has n = 5m + 1, σ = 2m, diameter 3, triangles, κ = m + 1 and α = m + 3.
   - Chvátal–Erdős (κ ≥ α − 1) fails, and the largest degree sum over non-adjacent pairs is n − 2, so the
     Bondy–Chvátal (n−1)-closure cannot add a single edge.
   - So "(H) implies a complete closure or κ ≥ α − 1" is **false** for every even σ ≥ 6.
   - It is still traceable: V4, then V3 and V2 alternating, then V1, one vertex of V0, V5, the other vertex of V0.

## Other observations (evidence, not proofs)
- Across about 36 million (H)-graphs in the open region from exhaustive clique blow-up searches (bases with 5–8
  classes, σ = 5–12), and annealing up to 47 vertices, no counterexample to #189 was found.
- Every graph where the closure failed had radius 3. Every radius-2 graph tested had a complete closure (33,674 of
  33,674). A vertex of eccentricity 2 provably becomes universal in the (n−1)-closure.

## How this was produced
By AI agents (Claude, Anthropic) in a research project run by Doug Phillips. Every claim above is rechecked by
`verify_families.py`. No human mathematician has reviewed it yet.
