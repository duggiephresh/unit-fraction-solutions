import Erdos307.Floor

/-!
# Erdős #307 — the square criterion and the closing lemma (E7)

* `A_union` : for disjoint positive `P`, `Q` : `A (P ∪ Q) = A P * M Q + A Q * M P`.
* `square_criterion` : in a solution with `P`, `Q` disjoint,
  `A (P ∪ Q) = M P ^ 2 + M Q ^ 2` and `M (P ∪ Q) = M P * M Q`; hence (`square_pm`)
  `A U + 2 M U = (M P + M Q)²` and `A U − 2 M U = (M P − M Q)²`.
* `prime_square` : for prime sets, `n = ∏ (P ∪ Q)` has `n' + 2n` and `n' − 2n` both squares
  (`n'` the arithmetic derivative, `sqfDeriv`).
* `closing` : if `P0`, `Q0` are admissible, cross-coprime and `M Q0 · M P0 = A Q0 · A P0 + 1`,
  then `P0 ∪ {M Q0² + A Q0 · M P0}` and `Q0 ∪ {M Q0 · A P0 + M P0²}` solve the equation, with
  everything pairwise coprime. `coprime_one_notMem_of_closing` : such a pair with
  `1 ∉ P0 ∪ Q0`, both nonempty, proves the open variant `erdos_307.variants.coprime_one_notMem`.
-/

namespace Erdos307

open Finset

variable {P Q : Finset ℕ}

lemma M_union (h : Disjoint P Q) : M (P ∪ Q) = M P * M Q := Finset.prod_union h

lemma pos_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) : ∀ x ∈ P ∪ Q, 0 < x := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hP x h
  · exact hQ x h

lemma A_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) (h : Disjoint P Q) :
    A (P ∪ Q) = A P * M Q + A Q * M P := by
  have e := sum_inv_eq (pos_union hP hQ)
  rw [Finset.sum_union h, sum_inv_eq hP, sum_inv_eq hQ, M_union h] at e
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ).ne'
  have key : (A (P ∪ Q) : ℚ) = A P * M Q + A Q * M P := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- **Square criterion.** -/
theorem square_criterion (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) = M P ^ 2 + M Q ^ 2 ∧ M (P ∪ Q) = M P * M Q := by
  obtain ⟨e1, e2⟩ := (forcing hP hQ).1 heq
  refine ⟨?_, M_union hd⟩
  rw [A_union hP.1 hQ.1 hd, e1, e2]
  ring

theorem square_pm (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) + 2 * M (P ∪ Q) = (M P + M Q) ^ 2 ∧
      (A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q) = ((M P : ℤ) - M Q) ^ 2 := by
  obtain ⟨h1, h2⟩ := square_criterion hP hQ hd heq
  refine ⟨by rw [h1, h2]; ring, ?_⟩
  rw [h1, h2]
  push_cast
  ring

/-- For the open variant (`1 ∉ P ∪ Q`) disjointness is automatic. -/
theorem square_pm_of_one_notMem (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (A (P ∪ Q) + 2 * M (P ∪ Q)) ∧ IsSquare ((A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q)) := by
  obtain ⟨h1', h2'⟩ := square_pm hP hQ (disjoint_of_solution hP hQ h1 heq) heq
  exact ⟨⟨M P + M Q, by rw [h1']; ring⟩, ⟨(M P : ℤ) - M Q, by rw [h2']; ring⟩⟩

/-- **Prime form:** for a solution in primes and `n = ∏ (P ∪ Q)`, both `n' + 2n` and `n' − 2n` are
perfect squares, `n'` the arithmetic derivative. -/
theorem prime_square (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (sqfDeriv (M (P ∪ Q)) + 2 * M (P ∪ Q)) ∧
      IsSquare ((sqfDeriv (M (P ∪ Q)) : ℤ) - 2 * M (P ∪ Q)) := by
  have hU : ∀ x ∈ P ∪ Q, x.Prime := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hP x h
    · exact hQ x h
  rw [sqfDeriv_M hU]
  refine square_pm_of_one_notMem (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
  intro h
  exact Nat.not_prime_one (hU 1 h)

/-! ## The closing lemma -/

section closing

variable {P0 Q0 : Finset ℕ}

/-- **Closing lemma.** A pair with `M Q0 · M P0 = A Q0 · A P0 + 1` closes to a solution. -/
theorem closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    Admissible (insert (M Q0 ^ 2 + A Q0 * M P0) P0) ∧
    Admissible (insert (M Q0 * A P0 + M P0 ^ 2) Q0) ∧
    (M Q0 ^ 2 + A Q0 * M P0) ∉ P0 ∧ (M Q0 * A P0 + M P0 ^ 2) ∉ Q0 ∧
    (∀ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, ∀ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0,
      Nat.Coprime x y) ∧
    (∑ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, (x : ℚ)⁻¹) *
      (∑ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0, (y : ℚ)⁻¹) = 1 := by
  set MP := M P0 with hMPdef
  set AP := A P0 with hAPdef
  set MQ := M Q0 with hMQdef
  set AQ := A Q0 with hAQdef
  set a := MQ ^ 2 + AQ * MP with ha
  set b := MQ * AP + MP ^ 2 with hb
  -- basic coprimality
  have cPQ : Nat.Coprime MP MQ :=
    Nat.Coprime.prod_left fun x hx => Nat.Coprime.prod_right fun y hy => hcross x hx y hy
  have cAP : Nat.Coprime AP MP := coprime_A_M hP
  have cAQ : Nat.Coprime AQ MQ := coprime_A_M hQ
  have ha_MP : Nat.Coprime a MP := by
    rw [ha, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ.symm
  have ha_MQ : Nat.Coprime a MQ := by
    have : a = AQ * MP + MQ * MQ := by rw [ha]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cAQ cPQ
  have hb_MQ : Nat.Coprime b MQ := by
    have : b = MP ^ 2 + AP * MQ := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ
  have hb_MP : Nat.Coprime b MP := by
    have : b = MQ * AP + MP * MP := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cPQ.symm cAP
  -- the two linear relations, from hD
  have hDz : (MQ : ℤ) * MP = AQ * AP + 1 := by exact_mod_cast hD
  have E1 : MQ * b = MP + AP * a := by
    have : (MQ : ℤ) * b = MP + AP * a := by
      rw [hb, ha]; push_cast; linear_combination (MP : ℤ) * hDz
    exact_mod_cast this
  have E2 : MP * a = MQ + AQ * b := by
    have : (MP : ℤ) * a = MQ + AQ * b := by
      rw [hb, ha]; push_cast; linear_combination (MQ : ℤ) * hDz
    exact_mod_cast this
  have hab : Nat.Coprime a b := by
    have h' : Nat.Coprime (MP + AP * a) a := by
      rw [Nat.coprime_add_mul_right_left]; exact ha_MP.symm
    rw [← E1] at h'
    exact Nat.Coprime.coprime_mul_left_right h'.symm
  -- sizes
  have hMQ2 : 2 ≤ MQ := by
    obtain ⟨y, hy⟩ := hQne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
    have hy0 := hQ.1 y hy
    have : y ≤ MQ := Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have hMP2 : 2 ≤ MP := by
    obtain ⟨y, hy⟩ := hPne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
    have hy0 := hP.1 y hy
    have : y ≤ MP := Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have ha2 : 2 ≤ a := by rw [ha]; nlinarith
  have hb2 : 2 ≤ b := by rw [hb]; nlinarith
  have haP : a ∉ P0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd ha_MP (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  have hbQ : b ∉ Q0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd hb_MQ (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  -- admissibility
  have adP : Admissible (insert a P0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hP.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hP.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime a y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MP
      exact ⟨c, c.symm⟩
  have adQ : Admissible (insert b Q0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hQ.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hQ.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime b y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) hb_MQ
      exact ⟨c, c.symm⟩
  refine ⟨adP, adQ, haP, hbQ, ?_, ?_⟩
  · intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx <;> rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hab
    · exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MQ
    · exact (Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hx) hb_MP).symm
    · exact hcross x hx y hy
  · rw [Finset.sum_insert haP, Finset.sum_insert hbQ, sum_inv_eq hP.1, sum_inv_eq hQ.1]
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hP0 : (MP : ℚ) ≠ 0 := by exact_mod_cast (show MP ≠ 0 by omega)
    have hQ0 : (MQ : ℚ) ≠ 0 := by exact_mod_cast (show MQ ≠ 0 by omega)
    have E1q : (MQ : ℚ) * b = MP + AP * a := by exact_mod_cast E1
    have E2q : (MP : ℚ) * a = MQ + AQ * b := by exact_mod_cast E2
    have s1 : (a : ℚ)⁻¹ + AP / MP = (MQ * b) / (a * MP) := by
      rw [E1q]; field_simp
    have s2 : (b : ℚ)⁻¹ + AQ / MQ = (MP * a) / (b * MQ) := by
      rw [E2q]; field_simp
    rw [s1, s2]
    field_simp

/-- **Sufficient condition for the open variant.** A cross-coprime admissible pair `P0`, `Q0`,
both nonempty, without `1`, with `M Q0 · M P0 = A Q0 · A P0 + 1`, proves
`erdos_307.variants.coprime_one_notMem` (stated exactly as in formal-conjectures). -/
theorem coprime_one_notMem_of_closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  obtain ⟨adP, adQ, haP, hbQ, -, heq⟩ := closing hP hQ hcross hQne hPne h1 hD
  refine ⟨_, _, ?_, ?_, ?_, ?_, adP.2, adQ.2, heq.symm⟩
  · intro h0
    exact (adP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · -- the new element `a` is ≥ 2
        have : 2 ≤ M Q0 ^ 2 + A Q0 * M P0 := by
          obtain ⟨y, hy⟩ := hQne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
          have : y ≤ M Q0 :=
            Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hQ.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_left _ h)
    · rcases Finset.mem_insert.1 h with e | h
      · have : 2 ≤ M Q0 * A P0 + M P0 ^ 2 := by
          obtain ⟨y, hy⟩ := hPne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
          have : y ≤ M P0 :=
            Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hP.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_right _ h)
  · rw [Finset.card_insert_of_notMem haP]
    have := Finset.card_pos.2 hPne
    omega
  · rw [Finset.card_insert_of_notMem hbQ]
    have := Finset.card_pos.2 hQne
    omega

end closing

end Erdos307
