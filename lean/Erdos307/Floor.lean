import Erdos307.Forcing

/-!
# Erdős #307 — the 59-element floor for the coprime variant (E6)

Any solution with `P`, `Q` positive, pairwise coprime and `1 ∉ P ∪ Q` has `59 ≤ #(P ∪ Q)`.

1. Forcing gives `gcd (M P) (M Q) = 1`, so `P ∪ Q` is pairwise coprime (and `P`, `Q` disjoint).
2. AM-GM: `Σ_P · Σ_Q = 1` gives `Σ_P + Σ_Q ≥ 2`.
3. `x ↦ minFac x` is injective on `P ∪ Q`, and `1/x ≤ 1/minFac x`.
4. A set `V` of at most 58 primes has `Σ_V 1/p ≤ Σ_F 1/p`, where `F` lists the 58 primes below
   277: a prime of `V \ F` is `≥ 277`, every entry of `F` is `< 277`, and `|V \ F| ≤ |F \ V|`.
5. `Σ_F 1/p < 2` (≈ 1.99874).

Only the finite facts `#F = 58`, `Σ_F 1/p < 2` and "every prime below 277 lies in `F`" are
computed; the primality of the entries of `F` is never used.
-/

namespace Erdos307

open Finset

/-- The 58 primes below 277. -/
def F58 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271}

set_option maxRecDepth 100000 in
lemma F58_card : F58.card = 58 := by decide

set_option maxRecDepth 100000 in
lemma F58_bounds : ∀ p ∈ F58, 0 < p ∧ p < 277 := by decide

lemma F58_sum : (∑ p ∈ F58, (p : ℚ)⁻¹) < 2 := by
  simp only [F58]
  norm_num

set_option maxRecDepth 100000 in
/-- Every prime outside `F58` is at least 277. -/
lemma le_of_prime_notMem_F58 {p : ℕ} (hp : p.Prime) (h : p ∉ F58) : 277 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | exact h (by decide) | exact absurd hp (by norm_num)

/-- Comparison against any set `F` of `k` numbers in `(0, B)` containing every prime `< B`. -/
lemma sum_inv_primes_le_of {F V : Finset ℕ} {k B : ℕ} (hB : 0 < B) (hFcard : F.card = k)
    (hFb : ∀ p ∈ F, 0 < p ∧ p < B) (hFp : ∀ p, p.Prime → p ∉ F → B ≤ p)
    (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ k) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F, (p : ℚ)⁻¹ := by
  rw [← Finset.sum_inter_add_sum_sdiff V F, ← Finset.sum_inter_add_sum_sdiff F V,
    Finset.inter_comm F V]
  have h1 : (∑ p ∈ V \ F, (p : ℚ)⁻¹) ≤ (V \ F).card • (B : ℚ)⁻¹ := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    obtain ⟨hpV, hpF⟩ := Finset.mem_sdiff.1 hp
    have h277 : (B : ℚ) ≤ p := by exact_mod_cast hFp p (hV p hpV) hpF
    exact inv_anti₀ (by exact_mod_cast hB) h277
  have h2 : (F \ V).card • (B : ℚ)⁻¹ ≤ ∑ p ∈ F \ V, (p : ℚ)⁻¹ := by
    refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
    obtain ⟨hpos, hlt⟩ := hFb p (Finset.mem_sdiff.1 hp).1
    exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hlt.le)
  have hc : (V \ F).card ≤ (F \ V).card := by
    have a := Finset.card_sdiff_add_card_inter V F
    have b := Finset.card_sdiff_add_card_inter F V
    rw [Finset.inter_comm, hFcard] at b
    omega
  have h3 : (V \ F).card • (B : ℚ)⁻¹ ≤ (F \ V).card • (B : ℚ)⁻¹ := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  linarith

/-- At most 58 primes have reciprocal sum at most that of the 58 primes below 277. -/
lemma sum_inv_primes_le {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ 58) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F58, (p : ℚ)⁻¹ :=
  sum_inv_primes_le_of (by norm_num) F58_card F58_bounds (fun _ hp h => le_of_prime_notMem_F58 hp h) hV hcard

/-- On a pairwise-coprime set of integers `> 1`, `minFac` is injective onto primes and
`1/x ≤ 1/minFac x`. -/
lemma sum_inv_le_minFac {U : Finset ℕ} (hgt : ∀ x ∈ U, 1 < x)
    (hcop : (U : Set ℕ).Pairwise Nat.Coprime) :
    (∑ x ∈ U, (x : ℚ)⁻¹) ≤ ∑ p ∈ U.image Nat.minFac, (p : ℚ)⁻¹ ∧
      (U.image Nat.minFac).card = U.card ∧ ∀ p ∈ U.image Nat.minFac, p.Prime := by
  have hinj : Set.InjOn Nat.minFac (U : Set ℕ) := by
    intro x hx y hy hxy
    by_contra hne
    have c := hcop hx hy hne
    have hdx : x.minFac ∣ x := Nat.minFac_dvd x
    have hdy : x.minFac ∣ y := hxy ▸ Nat.minFac_dvd y
    have h1 : x.minFac ∣ 1 := c ▸ Nat.dvd_gcd hdx hdy
    have : x = 1 := Nat.minFac_eq_one_iff.1 (Nat.dvd_one.1 h1)
    exact absurd (hgt x hx) (by omega)
  refine ⟨?_, Finset.card_image_of_injOn hinj, ?_⟩
  · rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum fun x hx => ?_
    have hx0 : 0 < x := by have := hgt x hx; omega
    exact inv_anti₀ (by exact_mod_cast Nat.minFac_pos x)
      (by exact_mod_cast Nat.minFac_le hx0)
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    exact Nat.minFac_prime (by have := hgt x hx; omega)

/-- In a solution, elements of `P` and `Q` are coprime. -/
lemma cross_coprime {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) {a b : ℕ} (ha : a ∈ P)
    (hb : b ∈ Q) : Nat.Coprime a b := by
  have e := ((forcing hP hQ).1 heq).1
  have c : Nat.Coprime (M P) (M Q) := e ▸ (coprime_A_M hP).symm
  exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hb)
    (Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem (fun x => x) ha) c)

/-- AM-GM for a product equal to one. -/
lemma two_le_add_of_mul_eq_one {s t : ℚ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s * t = 1) :
    2 ≤ s + t := by
  nlinarith [sq_nonneg (s - t)]

/-- **E6: the floor.** Any solution of the coprime variant with `1 ∉ P ∪ Q` uses at least
59 numbers. -/
theorem card_floor {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : 59 ≤ (P ∪ Q).card := by
  by_contra hlt
  push Not at hlt
  have hgt : ∀ x ∈ P ∪ Q, 1 < x := by
    intro x hx
    have hpos : 0 < x := by
      rcases Finset.mem_union.1 hx with h | h
      · exact hP.1 x h
      · exact hQ.1 x h
    have hne : x ≠ 1 := fun e => h1 (e ▸ hx)
    omega
  have hcop : ((P ∪ Q : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hne
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hP.2 hx hy hne
    · exact cross_coprime hP hQ heq hx hy
    · exact (cross_coprime hP hQ heq hy hx).symm
    · exact hQ.2 hx hy hne
  obtain ⟨hle, hcard, hprime⟩ := sum_inv_le_minFac hgt hcop
  have hV := sum_inv_primes_le hprime (by omega)
  have hsum : (∑ x ∈ P ∪ Q, (x : ℚ)⁻¹) = (∑ a ∈ P, (a : ℚ)⁻¹) + ∑ b ∈ Q, (b : ℚ)⁻¹ :=
    Finset.sum_union (disjoint_of_solution hP hQ h1 heq)
  have hamgm := two_le_add_of_mul_eq_one
    (Finset.sum_nonneg fun a _ => inv_nonneg.2 (Nat.cast_nonneg a))
    (Finset.sum_nonneg fun b _ => inv_nonneg.2 (Nat.cast_nonneg b)) heq
  linarith [F58_sum]

/-- The floor in the exact form of formal-conjectures' `erdos_307.variants.coprime_one_notMem`
hypotheses. -/
theorem coprime_one_notMem_card_floor {P Q : Finset ℕ} (h1 : 1 ∉ P ∪ Q) (hcP : 1 < P.card)
    (hcQ : 1 < Q.card) (cP : (P : Set ℕ).Pairwise Nat.Coprime)
    (cQ : (Q : Set ℕ).Pairwise Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card :=
  card_floor ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩ h1 heq.symm

/-- Cross-check: the same argument gives the 59-prime half of the upstream `erdos_307.barrier`
(Bonfioli), with no `Q.Nonempty` hypothesis. -/
theorem prime_card_floor {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card := by
  refine card_floor (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq.symm
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact Nat.not_prime_one (hP 1 h)
  · exact Nat.not_prime_one (hQ 1 h)

end Erdos307
