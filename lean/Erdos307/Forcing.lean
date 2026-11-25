import Mathlib

/-!
# Erdős Problem #307 — the forcing reduction

For a finite pairwise-coprime set `S` of positive integers put
`M S = ∏_{a ∈ S} a` and `A S = ∑_{a ∈ S} M S / a`.

* `coprime_A_M` / `gcd_A_M` : `gcd (A S) (M S) = 1`.
* `sum_inv_eq`, `sum_inv_num`, `sum_inv_den` : `∑ 1/a = A S / M S`, in lowest terms.
* `forcing` : `(∑_P 1/a) (∑_Q 1/b) = 1 ↔ A P = M Q ∧ A Q = M P`.
* `disjoint_of_solution` : with `1 ∉ P ∪ Q`, any solution has `P ∩ Q = ∅`.
* `prime_solution` : for sets of primes, `A P` is squarefree and `Q = (A P).primeFactors`.
* `two_cycle` : for sets of primes, a solution is exactly a 2-cycle `M P ↦ M Q ↦ M P`
  of the squarefree arithmetic derivative `sqfDeriv n = ∑_{p ∣ n} n / p`.
* `erdos_307_iff`, `coprime_one_notMem_iff` : the two open formal-conjectures statements
  (`docs/statement_307.md`) restated through the forcing reduction.
-/

namespace Erdos307

open Finset

/-- `M S = ∏_{a ∈ S} a`. -/
def M (S : Finset ℕ) : ℕ := ∏ a ∈ S, a

/-- `A S = ∑_{a ∈ S} M S / a`. -/
def A (S : Finset ℕ) : ℕ := ∑ a ∈ S, M S / a

/-- A finite set of positive, pairwise-coprime naturals. -/
def Admissible (S : Finset ℕ) : Prop :=
  (∀ a ∈ S, 0 < a) ∧ (S : Set ℕ).Pairwise Nat.Coprime

variable {S P Q : Finset ℕ}

lemma M_pos (h : ∀ a ∈ S, 0 < a) : 0 < M S := Finset.prod_pos h

lemma M_div_eq {a : ℕ} (ha : a ∈ S) (hpos : 0 < a) : M S / a = ∏ b ∈ S.erase a, b := by
  unfold M
  rw [← Finset.mul_prod_erase S (fun b => b) ha]
  exact Nat.mul_div_cancel_left _ hpos

lemma A_eq (h : ∀ a ∈ S, 0 < a) : A S = ∑ a ∈ S, ∏ b ∈ S.erase a, b := by
  unfold A
  exact Finset.sum_congr rfl fun a ha => M_div_eq ha (h a ha)

/-- `A S` is coprime to every element of `S`. -/
lemma coprime_A_mem (hS : Admissible S) {a : ℕ} (ha : a ∈ S) : Nat.Coprime (A S) a := by
  rw [A_eq hS.1, ← Finset.add_sum_erase S _ ha]
  have hdvd : a ∣ ∑ c ∈ S.erase a, ∏ b ∈ S.erase c, b := by
    refine Finset.dvd_sum fun c hc => ?_
    exact Finset.dvd_prod_of_mem (fun b => b)
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hc).symm, ha⟩)
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.coprime_add_mul_left_left]
  exact Nat.Coprime.prod_left fun b hb =>
    hS.2 (Finset.mem_of_mem_erase hb) ha (Finset.ne_of_mem_erase hb)

/-- **Lowest terms:** `A S` and `M S` are coprime. -/
theorem coprime_A_M (hS : Admissible S) : Nat.Coprime (A S) (M S) :=
  Nat.Coprime.prod_right fun _ ha => coprime_A_mem hS ha

theorem gcd_A_M (hS : Admissible S) : Nat.gcd (A S) (M S) = 1 := coprime_A_M hS

/-- `∑_{a ∈ S} 1/a = A S / M S` (positivity suffices). -/
theorem sum_inv_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, (a : ℚ)⁻¹) = (A S : ℚ) / (M S : ℚ) := by
  rw [A_eq hpos, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hM : (M S : ℚ) = (a : ℚ) * ∏ b ∈ S.erase a, (b : ℚ) := by
    unfold M
    rw [Nat.cast_prod, Finset.mul_prod_erase S (fun b : ℕ => (b : ℚ)) ha]
  rw [hM, Nat.cast_prod]
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
  have hP0 : ∏ b ∈ S.erase a, (b : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => by
      exact_mod_cast (hpos b (Finset.mem_of_mem_erase hb)).ne'
  field_simp

theorem sum_one_div_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, 1 / (a : ℚ)) = (A S : ℚ) / (M S : ℚ) := by
  simpa only [one_div] using sum_inv_eq hpos

/-- The reduced numerator of `∑ 1/a` is `A S`. -/
theorem sum_inv_num (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).num = A S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.num_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  simpa using this

/-- The reduced denominator of `∑ 1/a` is `M S`. -/
theorem sum_inv_den (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).den = M S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.den_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  exact_mod_cast (by simpa using this)

/-- **Forcing theorem.** -/
theorem forcing (hP : Admissible P) (hQ : Admissible Q) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔ A P = M Q ∧ A Q = M P := by
  rw [sum_inv_eq hP.1, sum_inv_eq hQ.1]
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP.1).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ.1).ne'
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hMP hMQ)]
  norm_cast
  constructor
  · intro h
    have cP := coprime_A_M hP
    have cQ := coprime_A_M hQ
    have h1 : A P ∣ M Q := cP.dvd_of_dvd_mul_left ⟨A Q, h.symm⟩
    have h2 : M Q ∣ A P := cQ.symm.dvd_of_dvd_mul_right (h ▸ dvd_mul_left (M Q) (M P))
    have e1 : A P = M Q := Nat.dvd_antisymm h1 h2
    refine ⟨e1, ?_⟩
    rw [e1, mul_comm (M P)] at h
    exact Nat.eq_of_mul_eq_mul_left (M_pos hQ.1) h
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_comm]

/-- Same statement in the `1 = …` orientation and `⁻¹` notation used by formal-conjectures. -/
theorem forcing' (hP : Admissible P) (hQ : Admissible Q) :
    1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) ↔ A P = M Q ∧ A Q = M P := by
  rw [eq_comm]; exact forcing hP hQ

/-- With `1 ∉ P ∪ Q`, a solution has `P` and `Q` disjoint. -/
theorem disjoint_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  have e := ((forcing hP hQ).1 heq).1
  have hx1 : x ∣ A P := e ▸ Finset.dvd_prod_of_mem (fun b => b) hxQ
  have hx2 : x ∣ M P := Finset.dvd_prod_of_mem (fun b => b) hxP
  have : x ∣ 1 := gcd_A_M hP ▸ Nat.dvd_gcd hx1 hx2
  exact h1 (Finset.mem_union_left _ (Nat.dvd_one.1 this ▸ hxP))

theorem inter_eq_empty_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : P ∩ Q = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.1 (disjoint_of_solution hP hQ h1 heq)

/-! ## Sets of primes -/

lemma admissible_of_primes (h : ∀ p ∈ S, p.Prime) : Admissible S :=
  ⟨fun p hp => (h p hp).pos, fun p hp q hq hpq => (Nat.coprime_primes (h p hp) (h q hq)).2 hpq⟩

lemma squarefree_M_of_primes (h : ∀ p ∈ S, p.Prime) : Squarefree (M S) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (h p hp) (h q hq)).2 hpq)
    fun p hp => (h p hp).prime.squarefree

lemma primeFactors_M (h : ∀ p ∈ S, p.Prime) : (M S).primeFactors = S :=
  Nat.primeFactors_prod h

/-- For prime sets: `A P` is squarefree, `Q = (A P).primeFactors`, `P = (A Q).primeFactors`,
and `P ∩ Q = ∅`. -/
theorem prime_solution (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    Squarefree (A P) ∧ Q = (A P).primeFactors ∧ P = (A Q).primeFactors ∧ Disjoint P Q := by
  obtain ⟨e1, e2⟩ := (forcing (admissible_of_primes hP) (admissible_of_primes hQ)).1 heq
  refine ⟨e1 ▸ squarefree_M_of_primes hQ, ?_, ?_, ?_⟩
  · rw [e1, primeFactors_M hQ]
  · rw [e2, primeFactors_M hP]
  · refine disjoint_of_solution (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
    intro h1
    rcases Finset.mem_union.1 h1 with h | h
    · exact Nat.not_prime_one (hP 1 h)
    · exact Nat.not_prime_one (hQ 1 h)

/-- The arithmetic derivative restricted to squarefree arguments: for squarefree `n`,
`n' = ∑_{p ∣ n} n / p`. (On non-squarefree `n` this is *not* the arithmetic derivative.) -/
def sqfDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n / p

lemma sqfDeriv_M (h : ∀ p ∈ S, p.Prime) : sqfDeriv (M S) = A S := by
  unfold sqfDeriv A
  rw [primeFactors_M h]

/-- **2-cycle equivalence.** For prime sets, `(∑_P 1/p)(∑_Q 1/q) = 1` iff the squarefree numbers
`M P`, `M Q` form a 2-cycle of the arithmetic derivative. -/
theorem two_cycle (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔
      sqfDeriv (M P) = M Q ∧ sqfDeriv (M Q) = M P := by
  rw [sqfDeriv_M hP, sqfDeriv_M hQ]
  exact forcing (admissible_of_primes hP) (admissible_of_primes hQ)

/-! ## The formal-conjectures statements, restated -/

/-- `erdos_307` (formal-conjectures) is equivalent to the integer system `A P = M Q, A Q = M P`
over sets of primes. -/
theorem erdos_307_iff :
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧ A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).2 h⟩

/-- Under the side conditions of the open variant, every element is positive. -/
lemma pos_of_variant {S : Finset ℕ} (h1 : 1 ∉ S) (hcard : 1 < S.card)
    (hcop : (S : Set ℕ).Pairwise Nat.Coprime) : ∀ a ∈ S, 0 < a := by
  intro a ha
  rcases Nat.eq_zero_or_pos a with h0 | h
  · exfalso
    subst h0
    obtain ⟨b, hb, hb0⟩ := Finset.exists_mem_ne hcard 0
    have := hcop ha hb (Ne.symm hb0)
    rw [Nat.coprime_zero_left] at this
    exact h1 (this ▸ hb)
  · exact h

/-- `erdos_307.variants.coprime_one_notMem` (formal-conjectures) restated through forcing. -/
theorem coprime_one_notMem_iff :
    (∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, Admissible P ∧ Admissible Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, -, h1, hcP, hcQ, cP, cQ, h⟩
    have hP : Admissible P :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    have hQ : Admissible Q :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩
    exact ⟨P, Q, hP, hQ, h1, hcP, hcQ, (forcing' hP hQ).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h1, hcP, hcQ, h⟩
    refine ⟨P, Q, ?_, h1, hcP, hcQ, hP.2, hQ.2, (forcing' hP hQ).2 h⟩
    intro h0
    exact (hP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl

end Erdos307
