import Erdos307.Square

/-!
# Erdős #307, coprime variant: existence conditional on a descent hypothesis

Write `Dev P Q = M(Q)·M(P) − A(Q)·A(P)` (an integer). By the closing lemma (`Square.lean`), an
admissible, cross-coprime pair with `Dev = 1` and no `1` closes to a solution of the open variant
`erdos_307.variants.coprime_one_notMem`.

`DescentHyp` says: every such "good" state with `Dev > 1` extends, by appending two new pairwise
coprime elements `x, y > 1` (coprime to everything present) to `P`, to a state with
`0 < Dev′ < Dev`. Gemini's two-element hyperbola descent (sprint lens R3-E) predicts such
extensions, even with `Dev′ < Dev / 2`, with an expected count that grows at every step; proving it
is an open thin-strip equidistribution problem.

Proved here (standard axioms):
- the descent machinery: `dev_insert2` (step formula), `dev_mul_dev_insert2` (the strip identity
  `Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²`, `E = A(Q)·M(P)`), `good_extend` (good states are
  closed under coprime extension), and `closes_of_dev_one`;
- `coprime_one_notMem_of_descent` and `coprime_one_notMem_of_descentBelow` (descent ⇒ the open variant).

**Honest status of the hypotheses (2026-11-24).**
- `DescentHyp` is FALSE (`not_descentHyp`, proved), so the first theorem is vacuous.
- `DescentHypBelow K` restricts to near-solution states. It is not known to be false, but it is
  universal over infinitely many states, while the halving heuristic gives each state a failure
  chance of about q0^(−c²/2) > 0. Ford-type exceptional sets make the universal form *heuristically
  false*. The heuristic supports only "some descent path survives" (a branching-process statement),
  which no ∀-state hypothesis captures.
- `DescentHypDeep M₀` (Gemini's refinement; the main result `coprime_one_notMem_of_descentDeep`)
  addresses both problems:
  - it adds `Coprime (M P) (A Q)`, which removes the local obstruction `dvd_dev_of_dvd`;
  - it requires `Dev² ≤ M(P)M(Q)`, so the halving start point is `q₀ ≥ √M`;
  - it allows **arbitrary finite** extensions `S`.

  Heuristically (Gemini, reported; not re-checked by Claude) the number of descending extensions
  per state grows fast enough that a union bound over all deep states converges, so the universal
  hypothesis is *plausible* under a Poisson model. Ford-type correlations are not ruled out.
  **It is a conjecture, not a theorem.**
- A deep seed exists: `scripts/deep_seed.py` builds one, with 69 elements, log₁₀ Dev = 115.5 and
  log₁₀ M(P)M(Q) = 4595.4. It is verified with exact integers in Python, not yet in Lean.
- Net: a genuine conditional reduction of the open variant to `DescentHypDeep`, a natural
  thin-strip / equidistribution conjecture, with the vacuous versions proved false and the local
  obstruction explicit.
-/

namespace Erdos307

open Finset

/-- The closing-lemma deviation `M(Q)·M(P) − A(Q)·A(P)`. -/
def Dev (P Q : Finset ℕ) : ℤ := (M Q : ℤ) * M P - (A Q : ℤ) * A P

/-- A state from which the closing lemma / descent can proceed. -/
def Good (P Q : Finset ℕ) : Prop :=
  Admissible P ∧ Admissible Q ∧ (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) ∧ P.Nonempty ∧
    Q.Nonempty ∧ 1 ∉ P ∪ Q ∧ 0 < Dev P Q

/-- **Descent hypothesis.** Every good state with `Dev > 1` admits a two-element extension of `P`
by new coprime elements that strictly lowers the (still positive) deviation. -/
def DescentHyp : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

lemma M_insert {S : Finset ℕ} {x : ℕ} (hxS : x ∉ S) : M (insert x S) = x * M S := by
  unfold M
  rw [Finset.prod_insert hxS]

lemma A_insert {S : Finset ℕ} {x : ℕ} (hS : ∀ a ∈ S, 0 < a) (hx : 0 < x) (hxS : x ∉ S) :
    A (insert x S) = x * A S + M S := by
  have hpos : ∀ a ∈ insert x S, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hx
    · exact hS a h
  have e := sum_inv_eq hpos
  rw [Finset.sum_insert hxS, sum_inv_eq hS, M_insert hxS] at e
  have hMS : (M S : ℚ) ≠ 0 := by exact_mod_cast (M_pos hS).ne'
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have key : (A (insert x S) : ℚ) = x * A S + M S := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- The deviation after appending two new elements to `P`. -/
lemma dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev (insert x (insert y P)) Q =
      (x : ℤ) * y * Dev P Q - ((A Q : ℤ) * M P) * ((x : ℤ) + y) := by
  have hyP' : ∀ a ∈ insert y P, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hy
    · exact hP a h
  have hxyP : x ∉ insert y P := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, hxP⟩
  unfold Dev
  rw [A_insert hyP' hx hxyP, M_insert hxyP, A_insert hP hy hyP, M_insert hyP]
  push_cast
  ring

/-- The thin-strip identity behind the halving mechanism:
`Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²` with `E = A(Q)·M(P)`. -/
lemma dev_mul_dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x)
    (hy : 0 < y) (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev P Q * Dev (insert x (insert y P)) Q =
      (Dev P Q * x - (A Q : ℤ) * M P) * (Dev P Q * y - (A Q : ℤ) * M P) -
        ((A Q : ℤ) * M P) ^ 2 := by
  rw [dev_insert2 hP hx hy hxy hxP hyP]
  ring

lemma not_mem_of_coprime_M {S : Finset ℕ} {x : ℕ} (hx1 : 1 < x) (h : Nat.Coprime x (M S)) :
    x ∉ S := by
  intro hx
  have := Nat.Coprime.eq_one_of_dvd h (Finset.dvd_prod_of_mem (fun a => a) hx)
  omega

lemma coprime_of_mem_of_coprime_M {S : Finset ℕ} {x a : ℕ} (ha : a ∈ S)
    (h : Nat.Coprime x (M S)) : Nat.Coprime x a :=
  Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun b => b) ha) h

/-- A two-element extension of a good state by new coprime elements is good again. -/
lemma good_extend {P Q : Finset ℕ} {x y : ℕ} (hG : Good P Q) (hx1 : 1 < x) (hy1 : 1 < y)
    (hxy : x ≠ y) (hxM : Nat.Coprime x (M P * M Q)) (hyM : Nat.Coprime y (M P * M Q))
    (hcxy : Nat.Coprime x y) (hpos : 0 < Dev (insert x (insert y P)) Q) :
    Good (insert x (insert y P)) Q := by
  obtain ⟨hP, hQ, hc, hPne, hQne, h1, -⟩ := hG
  have hxP : Nat.Coprime x (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM
  have hxQ : Nat.Coprime x (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hxM
  have hyP : Nat.Coprime y (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM
  have hyQ : Nat.Coprime y (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hyM
  refine ⟨⟨?_, ?_⟩, hQ, ?_, ⟨x, Finset.mem_insert_self _ _⟩, hQne, ?_, hpos⟩
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert, Finset.coe_insert, Set.pairwise_insert, Set.pairwise_insert]
    refine ⟨⟨hP.2, fun b hb _ => ?_⟩, fun b hb hne => ?_⟩
    · have c := coprime_of_mem_of_coprime_M hb hyP
      exact ⟨c, c.symm⟩
    · rcases hb with rfl | hb
      · exact ⟨hcxy, hcxy.symm⟩
      · have c := coprime_of_mem_of_coprime_M hb hxP
        exact ⟨c, c.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hxQ
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hyQ
    · exact hc a ha b hb
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · omega
      rcases Finset.mem_insert.1 h with e | h
      · omega
      · exact h1 (Finset.mem_union_left _ h)
    · exact h1 (Finset.mem_union_right _ h)

/-- The open variant, exactly as stated in formal-conjectures (`coprime_one_notMem`). -/
def CoprimeOneNotMem : Prop :=
  ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
    (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

lemma closes_of_dev_one {P Q : Finset ℕ} (hG : Good P Q) (h1 : Dev P Q = 1) :
    CoprimeOneNotMem := by
  obtain ⟨hP, hQ, hc, hPne, hQne, hone, -⟩ := hG
  have hD : M Q * M P = A Q * A P + 1 := by
    unfold Dev at h1
    have : ((M Q * M P : ℕ) : ℤ) = ((A Q * A P + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  exact coprime_one_notMem_of_closing hP hQ hc hQne hPne hone hD

/-- The starting state `({2}, {3})`, with `Dev = 3·2 − 1·1 = 5`. -/
lemma good_two_three : Good {2} {3} := by
  refine ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ?_, by simp, by simp, by simp, ?_⟩
  · intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    decide
  · simp [Dev, M, A]

/-- **Main theorem.** The descent hypothesis implies the open coprime / 1-excluded variant of
Erdős #307. -/
theorem coprime_one_notMem_of_descent (H : DescentHyp) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hnat.symm
        omega
  exact key _ {2} {3} good_two_three (Int.toNat_of_nonneg good_two_three.2.2.2.2.2.2.le).symm

/-- **Sanity check: the unrestricted `DescentHyp` is FALSE**, so `coprime_one_notMem_of_descent`
is vacuous. At `({2}, {3})` (`Dev = 5`), new elements must be coprime to 6, so they are ≥ 5 and
`Dev′ = 5xy − 2(x + y) ≥ 105`. The halving mechanism only operates near a solution; see
`DescentHypBelow`. -/
theorem not_descentHyp : ¬ DescentHyp := by
  intro H
  have hgt : 1 < Dev {2} {3} := by simp [Dev, M, A]
  obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, -, -, hlt⟩ := H {2} {3} good_two_three hgt
  have hxP : x ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hx1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
  have hyP : y ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hy1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
  rw [dev_insert2 (by simp) (by omega) (by omega) hxy hxP hyP] at hlt
  have h5 : Dev {2} {3} = 5 := by simp [Dev, M, A]
  have hA : (A {3} : ℤ) * M {2} = 2 := by simp [M, A]
  rw [h5, hA] at hlt
  have hx2 : (2 : ℤ) ≤ x := by exact_mod_cast hx1
  have hy2 : (2 : ℤ) ≤ y := by exact_mod_cast hy1
  nlinarith

/-- **Near-solution descent hypothesis.** Restricted to good states with deviation ratio
`Dev / (M(P)·M(Q)) ≤ 1/K`, a class closed under the descent step (`Dev′ < Dev` while the
products grow). This is where Gemini's halving mechanism lives. -/
def DescentHypBelow (K : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

/-- **Conditional existence (non-vacuous form).** If some good state lies in the near-solution
class `Dev·K ≤ M(P)M(Q)`, and every state of that class descends, then the open coprime variant
of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentBelow (K : ℕ) (H : DescentHypBelow K)
    (P0 Q0 : Finset ℕ) (hG0 : Good P0 Q0) (hK0 : Dev P0 Q0 * K ≤ (M P0 : ℤ) * M Q0) :
    CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
      Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hK hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt hK
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        -- the class is closed: Dev′·K < Dev·K ≤ M(P)M(Q) ≤ M(P′)M(Q)
        have hxP : x ∉ P := not_mem_of_coprime_M hx1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
        have hyP : y ∉ P := not_mem_of_coprime_M hy1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
        have hxyP : x ∉ insert y P := by
          simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hxP⟩
        have hM' : M (insert x (insert y P)) = x * (y * M P) := by
          rw [M_insert hxyP, M_insert hyP]
        have hMP : 0 < M P := M_pos hG.1.1
        have hMQ : 0 < M Q := M_pos hG.2.1.1
        have hgrow : (M P : ℤ) * M Q ≤ (M (insert x (insert y P)) : ℤ) * M Q := by
          rw [hM']
          have h1 : (M P : ℤ) ≤ (x : ℤ) * (y * M P) := by
            have : (1 : ℤ) ≤ (x : ℤ) * y := by
              have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx1.le
              have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy1.le
              nlinarith
            have hm : (0 : ℤ) ≤ M P := by exact_mod_cast hMP.le
            nlinarith
          push_cast
          exact mul_le_mul_of_nonneg_right h1 (by exact_mod_cast hMQ.le)
        have hK' : Dev (insert x (insert y P)) Q * K ≤
            (M (insert x (insert y P)) : ℤ) * M Q := by
          have hk : (0 : ℤ) ≤ K := by exact_mod_cast Nat.zero_le K
          nlinarith
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hK' hnat.symm
        omega
  exact key _ P0 Q0 hG0 hK0 (Int.toNat_of_nonneg hG0.2.2.2.2.2.2.le).symm

/-! ## The `Deep` class (Gemini's refinement) and arbitrary finite extensions -/

/-- **Local obstruction (Gemini, 2026-11-24).** If a prime `p` divides both `M(P)` and `A(Q)`, it
divides `Dev` for every extension of `P`, so one-sided descent can never reach `Dev = 1`. `Deep`
therefore requires `Coprime (M P) (A Q)`. -/
lemma dvd_dev_of_dvd {P Q : Finset ℕ} {p : ℕ} (hP : p ∣ M P) (hQ : p ∣ A Q) :
    (p : ℤ) ∣ Dev P Q := by
  unfold Dev
  exact dvd_sub (Dvd.dvd.mul_left (by exact_mod_cast hP) _)
    (Dvd.dvd.mul_right (by exact_mod_cast hQ) _)

/-- Deep near-solution states: good, `σ(Q) ≥ 1`, no local obstruction, large, and
`Dev² ≤ M(P)M(Q)`, so the halving start point `q₀ ≥ √M`. Closed under descent. -/
def Deep (M₀ : ℕ) (P Q : Finset ℕ) : Prop :=
  Good P Q ∧ M Q ≤ A Q ∧ Nat.Coprime (M P) (A Q) ∧ M₀ ≤ M P * M Q ∧
    Dev P Q ^ 2 ≤ (M P : ℤ) * M Q

/-- **Deep descent hypothesis.** Every deep state with `Dev > 1` admits a finite extension `S` of
`P` by new elements, pairwise coprime and coprime to `M(P)·M(Q)·A(Q)`, that lowers the
(positive) deviation. Gemini's two- and three-element halving pairs are special cases.
Heuristic support (Gemini, reported, not checked by Claude): with arbitrary finite `S`, the expected
number of descending extensions grows fast enough that a union bound over all deep states
converges (Poisson model); Ford-type correlations are not ruled out. -/
def DescentHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

lemma deep_extend {M₀ : ℕ} {P Q S : Finset ℕ} (hD : Deep M₀ P Q)
    (hS : ∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q))
    (hSc : (S : Set ℕ).Pairwise Nat.Coprime) (hpos : 0 < Dev (P ∪ S) Q)
    (hlt : Dev (P ∪ S) Q < Dev P Q) : Deep M₀ (P ∪ S) Q := by
  obtain ⟨⟨hP, hQ, hc, hPne, hQne, h1, hDpos⟩, hMQ, hcop, hM0, hsq⟩ := hD
  have hsP : ∀ s ∈ S, Nat.Coprime s (M P) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M Q * A Q) (by ring)) (hS s hs).2
  have hsQ : ∀ s ∈ S, Nat.Coprime s (M Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M P * A Q) (by ring)) (hS s hs).2
  have hsA : ∀ s ∈ S, Nat.Coprime s (A Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (hS s hs).2
  have hdisj : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro a haP haS
    have := Nat.Coprime.eq_one_of_dvd (hsP a haS) (Finset.dvd_prod_of_mem (fun b => b) haP)
    have := (hS a haS).1
    omega
  have hMU : M (P ∪ S) = M P * M S := Finset.prod_union hdisj
  have hMS : 0 < M S := Finset.prod_pos fun s hs => by have := (hS s hs).1; omega
  have hMP : 0 < M P := M_pos hP.1
  have hMQpos : 0 < M Q := M_pos hQ.1
  have hgrow : M P * M Q ≤ M (P ∪ S) * M Q := by
    rw [hMU]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hMS)
  refine ⟨⟨⟨fun a ha => ?_, ?_⟩, hQ, ?_, ?_, hQne, ?_, hpos⟩, hMQ, ?_, ?_, ?_⟩
  · rcases Finset.mem_union.1 ha with h | h
    · exact hP.1 a h
    · have := (hS a h).1; omega
  · intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hP.2 ha hb hab
    · exact (coprime_of_mem_of_coprime_M ha (hsP b hb)).symm
    · exact coprime_of_mem_of_coprime_M hb (hsP a ha)
    · exact hSc ha hb hab
  · intro a ha b hb
    rcases Finset.mem_union.1 ha with h | h
    · exact hc a h b hb
    · exact coprime_of_mem_of_coprime_M hb (hsQ a h)
  · obtain ⟨a, ha⟩ := hPne; exact ⟨a, Finset.mem_union_left _ ha⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact h1 (Finset.mem_union_left _ h)
      · have := (hS 1 h).1; omega
    · exact h1 (Finset.mem_union_right _ h)
  · rw [hMU]
    exact Nat.Coprime.mul_left hcop (Nat.Coprime.prod_left fun s hs => hsA s hs)
  · exact le_trans hM0 hgrow
  · have h0 : (0 : ℤ) < Dev (P ∪ S) Q := hpos
    have hsq' : Dev (P ∪ S) Q ^ 2 < Dev P Q ^ 2 := by nlinarith
    have : ((M P * M Q : ℕ) : ℤ) ≤ ((M (P ∪ S) * M Q : ℕ) : ℤ) := by exact_mod_cast hgrow
    push_cast at this
    linarith

/-- **Conditional existence (Deep form).** If the deep descent hypothesis holds at level `M₀`, and
some deep state exists at that level, the open coprime / 1-excluded variant of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentDeep (M₀ : ℕ) (H : DescentHypDeep M₀)
    (P0 Q0 : Finset ℕ) (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Deep M₀ P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hD hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hD.1 (by rw [hn, hn1]; norm_num)
      · have hDp := hD.1.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hDp ⊢; omega
        obtain ⟨S, hS, hSc, hpos, hlt⟩ := H P Q hD hgt
        have hD' := deep_extend hD hS hSc hpos hlt
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (P ∪ S) Q).toNat ?_ _ Q hD' hnat.symm
        omega
  exact key _ P0 Q0 h0 (Int.toNat_of_nonneg h0.1.2.2.2.2.2.2.le).symm

/-! ## Egyptian-fraction reformulation -/

/-- **Extension formula.** For a disjoint positive extension `S` of `P`:
`Dev(P ∪ S, Q) = M(S)·Dev(P, Q) − E·A(S)` with `E = A(Q)·M(P)`. So descent is the statement
`σ(S) ∈ (t − t/M(S), t)` with `t = Dev/E`: an Egyptian underapproximation of `t` with relative
error below `1/∏S` (`σ(S) = t` exactly would be a solution of #307). -/
lemma dev_union {P Q S : Finset ℕ} (hP : ∀ a ∈ P, 0 < a) (hS : ∀ s ∈ S, 0 < s)
    (hd : Disjoint P S) :
    Dev (P ∪ S) Q = (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S := by
  unfold Dev
  rw [A_union hP hS hd, M_union hd]
  push_cast
  ring

/-- The descent hypothesis in Egyptian-fraction form (same conclusion, stated through
`M(S)·Dev − E·A(S)`); it implies `DescentHypDeep`. -/
def EgyptHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧
      0 < (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S ∧
      (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S < Dev P Q

theorem descentHypDeep_of_egypt {M₀ : ℕ} (H : EgyptHypDeep M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  obtain ⟨S, hS, hSc, h1, h2⟩ := H P Q hD hgt
  refine ⟨S, hS, hSc, ?_, ?_⟩ <;>
  · have hdisj : Disjoint P S := by
      rw [Finset.disjoint_left]
      intro a haP haS
      have hc : Nat.Coprime a (M P) := Nat.Coprime.coprime_dvd_right
        (Dvd.intro (M Q * A Q) (by ring)) (hS a haS).2
      have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) haP)
      have := (hS a haS).1
      omega
    rwa [dev_union hD.1.1.1 (fun s hs => by have := (hS s hs).1; omega) hdisj]

/-! ## A proved special case: the greedy element -/

/-- In a deep state, `Dev` and `E = A(Q)·M(P)` share no prime factor. -/
lemma not_dvd_dev_and_E {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) {p : ℕ} (hp : p.Prime)
    (h1 : (p : ℤ) ∣ Dev P Q) (h2 : p ∣ A Q * M P) : False := by
  obtain ⟨⟨hP, hQ, -, -, -, -, -⟩, -, hcop, -, -⟩ := hD
  have cAP := coprime_A_M hP
  have cAQ := coprime_A_M hQ
  have bad : ∀ {a b : ℕ}, Nat.Coprime a b → p ∣ a → p ∣ b → False := fun hab ha hb => by
    have : p ∣ Nat.gcd _ _ := Nat.dvd_gcd ha hb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  unfold Dev at h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with hA | hM
  · -- p ∣ A Q ⇒ p ∣ M Q · M P
    have : (p : ℤ) ∣ (M Q : ℤ) * M P := by
      have hAA : (p : ℤ) ∣ (A Q : ℤ) * A P := Dvd.dvd.mul_right (by exact_mod_cast hA) _
      have := dvd_add h1 hAA
      simpa using this
    have : p ∣ M Q * M P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad cAQ hA h
    · exact bad hcop h hA
  · -- p ∣ M P ⇒ p ∣ A Q · A P
    have : (p : ℤ) ∣ (A Q : ℤ) * A P := by
      have hMM : (p : ℤ) ∣ (M Q : ℤ) * M P := Dvd.dvd.mul_left (by exact_mod_cast hM) _
      have := dvd_sub hMM h1
      simpa using this
    have : p ∣ A Q * A P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad hcop hM h
    · exact bad cAP h hM

/-- **Greedy descent (proved).** In a deep state with `Dev > 1`, if the greedy element
`s = ⌊E/Dev⌋ + 1` (`E = A(Q)·M(P)`) is `> 1` and coprime to `M(P)·M(Q)·A(Q)`, then `S = {s}`
descends: `Dev′ = Dev − (E mod Dev) ∈ (0, Dev)`. -/
theorem greedy_descends {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) (hgt : 1 < Dev P Q)
    (hs1 : 1 < A Q * M P / (Dev P Q).toNat + 1)
    (hsc : Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q := by
  obtain ⟨d, hdD⟩ : ∃ d : ℕ, (d : ℤ) = Dev P Q := ⟨(Dev P Q).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdt : (Dev P Q).toNat = d := by rw [← hdD]; simp
  rw [hdt] at hs1 hsc
  have hd1 : 1 < d := by omega
  -- d does not divide E = A(Q)·M(P) (coprime, d > 1)
  have hmod : A Q * M P % d ≠ 0 := by
    intro h0
    have hdvd : d ∣ A Q * M P := Nat.dvd_of_mod_eq_zero h0
    have hp := Nat.minFac_prime (show d ≠ 1 by omega)
    exact not_dvd_dev_and_E hD hp (by rw [← hdD]; exact_mod_cast Nat.minFac_dvd d)
      ((Nat.minFac_dvd d).trans hdvd)
  have hlt : A Q * M P % d < d := Nat.mod_lt _ (by omega)
  have hdiv := Nat.div_add_mod (A Q * M P) d
  have hsP : A Q * M P / d + 1 ∉ P := by
    intro hm
    have hc : Nat.Coprime (A Q * M P / d + 1) (M P) := Nat.Coprime.coprime_dvd_right
      (Dvd.intro (M Q * A Q) (by ring)) hsc
    have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) hm)
    omega
  have hdisj : Disjoint P {A Q * M P / d + 1} := Finset.disjoint_singleton_right.2 hsP
  have hform := dev_union (Q := Q) hD.1.1.1
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; omega) hdisj
  have hMs : M {A Q * M P / d + 1} = A Q * M P / d + 1 := by simp [M]
  have hAs : A {A Q * M P / d + 1} = 1 := by simp [A, M]
  rw [hMs, hAs] at hform
  have key : Dev (P ∪ {A Q * M P / d + 1}) Q = (d : ℤ) - ((A Q * M P % d : ℕ) : ℤ) := by
    rw [hform, ← hdD]
    have h' : ((A Q * M P : ℕ) : ℤ) =
        (d : ℤ) * ((A Q * M P / d : ℕ) : ℤ) + ((A Q * M P % d : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    push_cast at h' ⊢
    linear_combination (-1 : ℤ) * h'
  have hr : 0 < A Q * M P % d := Nat.pos_of_ne_zero hmod
  refine ⟨{A Q * M P / d + 1}, ?_, by simp, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.1 ht]
    exact ⟨hs1, hsc⟩
  · rw [key]; omega
  · rw [key, ← hdD]; omega

/-- So the hypothesis only needs assuming at **hard** states, where the greedy element is not
admissible. -/
def EgyptHypHard (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ¬ (1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

theorem descentHypDeep_of_hard {M₀ : ℕ} (H : EgyptHypHard M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  by_cases hg : 1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)
  · exact greedy_descends hD hgt hg.1 hg.2
  · exact H P Q hD hgt hg

/-- **Headline.** The open coprime / 1-excluded variant of Erdős #307 follows from the descent
hypothesis at *hard* deep states only (those whose greedy element is not admissible), given one
deep seed. Easy states are handled unconditionally by `greedy_descends`. -/
theorem coprime_one_notMem_of_hard (M₀ : ℕ) (H : EgyptHypHard M₀) (P0 Q0 : Finset ℕ)
    (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem :=
  coprime_one_notMem_of_descentDeep M₀ (descentHypDeep_of_hard H) P0 Q0 h0

/-- Gemini's halving form (`Dev′ < Dev/2`) is a special case of the descent hypothesis. -/
theorem descentHyp_of_halving
    (H : ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
      ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
        Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
        0 < Dev (insert x (insert y P)) Q ∧ 2 * Dev (insert x (insert y P)) Q < Dev P Q) :
    DescentHyp := by
  intro P Q hG hgt
  obtain ⟨x, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H P Q hG hgt
  exact ⟨x, y, h1, h2, h3, h4, h5, h6, h7, by linarith⟩

end Erdos307
