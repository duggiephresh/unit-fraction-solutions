import Mathlib

/-!
# Reciprocity constraints on odd Znám-type and Giuga-type sets

Let `S` be a finite set of odd, pairwise coprime integers `> 1`, and let `a` be the number of
elements of `S` that are `≡ 3 (mod 4)`.

* (Znám / PPN type) If `x ∣ (∏_{y ∈ S, y ≠ x} y) + 1` for every `x ∈ S`, then `a % 4 ∈ {0, 3}`.
* (Giuga type) If `x ∣ (∏_{y ∈ S, y ≠ x} y) - 1` for every `x ∈ S`, then `a % 4 ∈ {0, 1}`.

Proof: multiply the Jacobi symbols `J(N_x, x)` over `x ∈ S`, where `N_x = ∏_{y ≠ x} y`.
By quadratic reciprocity the double product equals `(-1)^(a choose 2)`; by the congruence
`N_x ≡ ∓1 (mod x)` it equals `(-1)^a` (Znám) or `1` (Giuga). Compare parities.
-/

namespace Erdos307.Reciprocity

open Finset

/-- Number of elements of `S` congruent to `3 mod 4`. -/
def a3 (S : Finset ℕ) : ℕ := (S.filter (fun x => x % 4 = 3)).card

/-- The double Jacobi product `∏_{x ∈ S} ∏_{y ∈ S, y ≠ x} J(y, x)`. -/
noncomputable def F (S : Finset ℕ) : ℤ :=
  ∏ x ∈ S, ∏ y ∈ S.erase x, jacobiSym (y : ℤ) x

/-- Odd, pairwise coprime. -/
def OddCoprime (S : Finset ℕ) : Prop :=
  (∀ x ∈ S, Odd x) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y

lemma jacobiSym_prod_left (s : Finset ℕ) (b : ℕ) (f : ℕ → ℤ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.induction_on with
  | empty => simp [jacobiSym.one_left]
  | insert i s hi ih => rw [prod_insert hi, prod_insert hi, jacobiSym.mul_left, ih]

lemma jacobiSym_sq_eq_one {x y : ℕ} (h : Nat.Coprime y x) :
    jacobiSym (y : ℤ) x * jacobiSym (y : ℤ) x = 1 := by
  have hg : (y : ℤ).gcd (x : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h
  rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1 <;> rw [h1] <;> norm_num

/-- Pairwise reciprocity: `J(y,x) J(x,y) = -1` iff `x ≡ y ≡ 3 (mod 4)`. -/
lemma pair_sign {x y : ℕ} (hx : Odd x) (hy : Odd y) (hxy : Nat.Coprime x y) :
    jacobiSym (y : ℤ) x * jacobiSym (x : ℤ) y =
      if x % 4 = 3 ∧ y % 4 = 3 then -1 else 1 := by
  have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by
    rcases hx with ⟨k, rfl⟩; omega
  have hy4 : y % 4 = 1 ∨ y % 4 = 3 := by
    rcases hy with ⟨k, rfl⟩; omega
  split_ifs with h
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h.1 h.2, mul_neg,
      jacobiSym_sq_eq_one hxy.symm]
  · rcases hx4 with h1 | h1
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hy]
      exact jacobiSym_sq_eq_one hxy.symm
    · have h2 : y % 4 = 1 := by omega
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four h2 hx]
      exact jacobiSym_sq_eq_one hxy.symm

lemma prod_ite_three (S : Finset ℕ) :
    (∏ y ∈ S, (if y % 4 = 3 then (-1 : ℤ) else 1)) = (-1) ^ a3 S := by
  rw [prod_ite, prod_const, prod_const_one, mul_one, a3]

lemma a3_insert {S : Finset ℕ} {z : ℕ} (hz : z ∉ S) :
    a3 (insert z S) = a3 S + if z % 4 = 3 then 1 else 0 := by
  unfold a3
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp [hz])]
  · rfl

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- The double Jacobi product of an odd pairwise-coprime set is `(-1)^(a choose 2)`. -/
theorem F_eq (S : Finset ℕ) (hS : OddCoprime S) : F S = (-1) ^ (a3 S).choose 2 := by
  induction S using Finset.induction_on with
  | empty => simp [F, a3]
  | insert z S hz ih =>
    obtain ⟨hodd, hcop⟩ := hS
    have hS' : OddCoprime S :=
      ⟨fun x hx => hodd x (mem_insert_of_mem hx),
       fun x hx y hy hxy => hcop x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy⟩
    have key : F (insert z S) =
        (∏ y ∈ S, jacobiSym (y : ℤ) z * jacobiSym (z : ℤ) y) * F S := by
      unfold F
      rw [prod_insert hz, erase_insert hz, prod_mul_distrib, mul_assoc]
      congr 1
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun x hx => ?_
      have hxz : x ≠ z := fun h => hz (h ▸ hx)
      rw [erase_insert_of_ne (Ne.symm hxz), prod_insert (by simp [hz])]
    have pairs : (∏ y ∈ S, jacobiSym (y : ℤ) z * jacobiSym (z : ℤ) y) =
        (-1 : ℤ) ^ (if z % 4 = 3 then a3 S else 0) := by
      rw [prod_congr rfl fun y hy => pair_sign (hodd z (mem_insert_self z S))
        (hodd y (mem_insert_of_mem hy))
        (hcop z (mem_insert_self z S) y (mem_insert_of_mem hy) (fun h => hz (h ▸ hy)))]
      split_ifs with h
      · rw [← prod_ite_three]; simp [h]
      · simp [h]
    rw [key, pairs, ih hS', a3_insert hz, ← pow_add]
    split_ifs with h
    · rw [choose_two_succ, add_comm]
    · simp

lemma choose_two_mod_two (a : ℕ) :
    a.choose 2 % 2 = if a % 4 = 2 ∨ a % 4 = 3 then 1 else 0 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [choose_two_succ]
    split_ifs at ih ⊢ <;> omega

lemma neg_one_pow_eq_iff (m n : ℕ) : ((-1 : ℤ) ^ m = (-1) ^ n) ↔ m % 2 = n % 2 := by
  rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n]
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp_all
  · intro h; rw [h]

/-- `J(N, x)` where `N` is the product of the other elements. -/
lemma jacobi_others (S : Finset ℕ) (x : ℕ) :
    jacobiSym ((∏ y ∈ S.erase x, y : ℕ) : ℤ) x = ∏ y ∈ S.erase x, jacobiSym (y : ℤ) x := by
  rw [Nat.cast_prod, jacobiSym_prod_left]

lemma prod_one_le (S : Finset ℕ) (hS : ∀ x ∈ S, 1 < x) (x : ℕ) :
    1 ≤ ∏ y ∈ S.erase x, y :=
  Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun y hy => by
    have := hS y (mem_of_mem_erase hy); omega)

/-- **Znám / PPN type.** -/
theorem znam_type (S : Finset ℕ) (hodd : ∀ x ∈ S, Odd x) (hgt : ∀ x ∈ S, 1 < x)
    (hcop : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y)
    (hdiv : ∀ x ∈ S, x ∣ (∏ y ∈ S.erase x, y) + 1) :
    (S.filter (fun x => x % 4 = 3)).card % 4 = 0 ∨
      (S.filter (fun x => x % 4 = 3)).card % 4 = 3 := by
  have _ := hgt
  have hF := F_eq S ⟨hodd, hcop⟩
  have hF' : F S = (-1) ^ a3 S := by
    rw [F, ← prod_ite_three]
    refine prod_congr rfl fun x hx => ?_
    rw [← jacobi_others]
    have hmod : (((∏ y ∈ S.erase x, y : ℕ)) : ℤ) % (x : ℤ) = (-1) % (x : ℤ) := by
      apply Int.ModEq.eq
      rw [Int.modEq_iff_dvd]
      have h := Int.natCast_dvd_natCast.mpr (hdiv x hx)
      push_cast at h
      have : (-1 : ℤ) - ((∏ y ∈ S.erase x, y : ℕ) : ℤ) = -((∏ y ∈ S.erase x, (y : ℤ)) + 1) := by
        push_cast; ring
      rw [this]; exact h.neg_right
    rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one (hodd x hx), ZMod.χ₄_nat_eq_if_mod_four]
    have hx2 : x % 2 = 1 := Nat.odd_iff.mp (hodd x hx)
    have hx1 : ¬ x % 2 = 0 := by omega
    by_cases h3 : x % 4 = 3
    · simp [hx1, h3]
    · have h1 : x % 4 = 1 := by omega
      simp [hx1, h1]
  rw [hF] at hF'
  have h := (neg_one_pow_eq_iff _ _).mp hF'
  rw [choose_two_mod_two] at h
  unfold a3 at h
  split_ifs at h <;> omega

/-- **Giuga type.** -/
theorem giuga_type (S : Finset ℕ) (hodd : ∀ x ∈ S, Odd x) (hgt : ∀ x ∈ S, 1 < x)
    (hcop : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y)
    (hdiv : ∀ x ∈ S, x ∣ (∏ y ∈ S.erase x, y) - 1) :
    (S.filter (fun x => x % 4 = 3)).card % 4 = 0 ∨
      (S.filter (fun x => x % 4 = 3)).card % 4 = 1 := by
  have hF := F_eq S ⟨hodd, hcop⟩
  have hF' : F S = 1 := by
    rw [F]
    refine prod_eq_one fun x hx => ?_
    rw [← jacobi_others]
    have hmod : (((∏ y ∈ S.erase x, y : ℕ)) : ℤ) % (x : ℤ) = 1 % (x : ℤ) := by
      have h := Int.natCast_dvd_natCast.mpr (hdiv x hx)
      rw [Nat.cast_sub (prod_one_le S hgt x)] at h
      exact (Int.modEq_iff_dvd.mpr (by simpa using h)).symm.eq
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
  rw [hF', ← pow_zero (-1 : ℤ)] at hF
  have h := (neg_one_pow_eq_iff _ _).mp hF.symm
  rw [choose_two_mod_two] at h
  unfold a3 at h
  split_ifs at h; omega

/-! ## Sanity checks -/

/-- Direct computation: `F {3, 5, 7} = -1 = (-1)^(2 choose 2)`. -/
example : F {3, 5, 7} = -1 := by
  simp only [F]
  decide +kernel

example : a3 {3, 5, 7} = 2 := by decide

example : F {3, 5, 7} = (-1) ^ (a3 {3, 5, 7}).choose 2 :=
  F_eq _ ⟨by decide, by decide⟩

end Erdos307.Reciprocity
