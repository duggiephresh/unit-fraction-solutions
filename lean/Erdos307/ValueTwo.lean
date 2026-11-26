import Erdos307.ImplicitChain

/-!
# Value-2 unit-fraction sets from a one-sided implicit chain (Claude, 2026-11-25)

A one-sided chain is an implicit chain with `Q = {1}`, so `Dev P {1} = M P − A P`. A chain ending at
deviation `1` gives a pairwise-coprime set `P` with `∑ 1/x + 1/∏x = 1`. When `30 ∈ P`, splitting `30` into
`2, 3, 5` raises the reciprocal sum by exactly `1` (`1/2 + 1/3 + 1/5 = 1 + 1/30`) without changing the
product. Appending `∏ − 1` then turns each set into a Giuga sequence. From one such `P` we get:

* `brentonHill_two`: pairwise-coprime integers `> 1` with `∑ 1/x + 1/∏x = 2`;
* `giuga_two`: a Giuga sequence of value `2` (`∑ 1/x − 1/∏x = 2`);
* `giuga_same_product`: two distinct Giuga sequences with the same product.

`stepCheck_sound_sub` is `stepCheck_sound` that also records that the final set contains the seed.
-/

namespace Erdos307

open Finset

/-- `stepCheck_sound`, also recording `P ⊆ P'`. -/
theorem stepCheck_sound_sub {Q : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs) :
    ∀ (rest : List ℕ) (P : Finset ℕ) (d R Em lb : ℕ),
      Admissible P → (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) → 1 ∉ P → P.Nonempty →
      Dev P Q = d → 0 < d → R = M Q * (d :: rest).prod → Em ≡ A Q * M P [MOD R] →
      lb ≤ A Q * M P → stepCheck qs R Em lb d rest = true →
      ∃ P' : Finset ℕ, P ⊆ P' ∧ Admissible P' ∧ (∀ a ∈ P', ∀ b ∈ Q, Nat.Coprime a b) ∧ 1 ∉ P' ∧
        P'.Nonempty ∧ Dev P' Q = 1 := by
  intro rest
  induction rest with
  | nil =>
    intro P d R Em lb hP hcross h1 hne hdev _ _ _ _ hchk
    simp only [stepCheck, beq_iff_eq] at hchk
    exact ⟨P, subset_rfl, hP, hcross, h1, hne, by rw [hdev, hchk]; rfl⟩
  | cons d' rest ih =>
    intro P d R Em lb hP hcross h1 hne hdev hd hR hEm hlb hchk
    simp only [stepCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
      Nat.ble_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hi, hii⟩, hd'0⟩, hiii⟩, hiv⟩, hnext⟩ := hchk
    set E := A Q * M P with hE
    set Rn := M Q * (d' :: rest).prod with hRn
    have hRdRn : R = d * Rn := by rw [hR, hRn, List.prod_cons]; ring
    have hRdiv : R / d = Rn := by rw [hRdRn, Nat.mul_div_cancel_left _ hd]
    have hdR : d ∣ R := ⟨Rn, hRdRn⟩
    have hRnR : Rn ∣ R := ⟨d, by rw [hRdRn]; ring⟩
    have hd'R : d' ∣ R := by
      rw [hRdRn, hRn, List.prod_cons]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right d' _) _) _
    have hEmd : Em ≡ E [MOD d] := Nat.ModEq.of_dvd hdR hEm
    have hdiv : d ∣ E + d' := by
      apply Nat.dvd_of_mod_eq_zero
      have := (hEmd.add_right d').symm
      unfold Nat.ModEq at this; rw [this]; exact hi
    set s := (E + d') / d with hsdef
    have hs : s * d = E + d' := Nat.div_mul_cancel hdiv
    have hcop : Nat.Coprime d' E := by
      have h' : Em % d' = E % d' := Nat.ModEq.of_dvd hd'R hEm
      rw [h'] at hii
      unfold Nat.Coprime; rw [Nat.gcd_rec]; exact hii
    have hsm : ((Em + d') % R) / d ≡ s [MOD Rn] := by
      have ht : (Em + d') % R ≡ E + d' [MOD R] := (Nat.mod_modEq _ _).trans (hEm.add_right d')
      have htd : d ∣ (Em + d') % R := by
        apply Nat.dvd_of_mod_eq_zero
        have := Nat.ModEq.of_dvd hdR ht
        unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_zero_of_dvd hdiv
      have e1 : (Em + d') % R = d * (((Em + d') % R) / d) := (Nat.mul_div_cancel' htd).symm
      have e2 : E + d' = d * s := by rw [mul_comm]; exact hs.symm
      rw [e1, e2] at ht
      rw [hRdRn] at ht ⊢
      exact Nat.ModEq.mul_left_cancel' (c := d) (by omega) ht
    have hsQ : ∀ q ∈ Q, Nat.Coprime s q := by
      intro q hq
      have hqRn : q ∣ Rn := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hq) _
      have h3 := hiii q (hqs q hq)
      have h' : (((Em + d') % R) / d) % q = s % q := Nat.ModEq.of_dvd hqRn hsm
      rw [h'] at h3
      have : Nat.gcd q s = 1 := by rw [Nat.gcd_rec]; exact h3
      exact Nat.Coprime.symm this
    have hs1 : 1 < s := by
      have h2 : 2 * d ≤ E + d' := le_trans hiv (by omega)
      rw [← hs] at h2
      have : 2 ≤ s := Nat.le_of_mul_le_mul_right (by rw [mul_comm] at h2; linarith [h2]) hd
      omega
    obtain ⟨hsP, hP', hcross', h1', hdev', hE'⟩ :=
      implicit_step hP hcross h1 hdev hs hcop hsQ hs1
    obtain ⟨P', hsub, rest'⟩ := ih (insert s P) d' Rn ((Em % Rn) * (((Em + d') % R) / d) % Rn)
      (min capLB (lb * ((lb + d') / d))) hP' hcross' h1' (Finset.insert_nonempty _ _) hdev'
      (by omega) hRn
      (by
        rw [hE']
        have hEmRn : Em % Rn ≡ E [MOD Rn] := (Nat.mod_modEq _ _).trans (Nat.ModEq.of_dvd hRnR hEm)
        exact (Nat.mod_modEq _ _).trans (hEmRn.mul hsm))
      (by
        rw [hE']
        refine le_trans (min_le_right _ _) (Nat.mul_le_mul hlb ?_)
        exact Nat.div_le_div_right (by omega))
      (by rw [hRdiv] at hnext; exact hnext)
    exact ⟨P', (Finset.subset_insert s P).trans hsub, rest'⟩

/-- A Giuga sequence of value `v` (Borwein–Borwein–Borwein–Girgensohn 1996): integers `> 1` with
`∑ 1/x − 1/∏x = v`. -/
def IsGiuga (S : Finset ℕ) (v : ℕ) : Prop :=
  (∀ x ∈ S, 1 < x) ∧ (∑ x ∈ S, (x : ℚ)⁻¹) - (∏ x ∈ S, (x : ℚ))⁻¹ = v

/-- The three value-2 consequences of a pairwise-coprime `P ∋ 30` with `M P − A P = 1`. -/
theorem value_two_package {P : Finset ℕ} (hP : Admissible P) (h1 : 1 ∉ P) (h30 : 30 ∈ P)
    (hdev : Dev P {1} = 1) :
    (∃ S : Finset ℕ, (∀ x ∈ S, 1 < x) ∧ (S : Set ℕ).Pairwise Nat.Coprime ∧
        (∑ x ∈ S, (x : ℚ)⁻¹) + (∏ x ∈ S, (x : ℚ))⁻¹ = 2) ∧
    (∃ T : Finset ℕ, IsGiuga T 2) ∧
    (∃ T₁ T₂ : Finset ℕ, T₁ ≠ T₂ ∧ IsGiuga T₁ 1 ∧ IsGiuga T₂ 2 ∧
        ∏ x ∈ T₁, x = ∏ x ∈ T₂, x) := by
  obtain ⟨hpos, hpw⟩ := hP
  set N := M P with hNdef
  -- the identity M − A = 1, in ℚ
  have hM1 : M ({1} : Finset ℕ) = 1 := by simp [M]
  have hA1 : A ({1} : Finset ℕ) = 1 := by simp [A, M]
  have hMA : (A P : ℚ) = (N : ℚ) - 1 := by
    have h := hdev
    simp only [Dev, hM1, hA1, Nat.cast_one, one_mul] at h
    have : ((N : ℤ) : ℚ) - ((A P : ℤ) : ℚ) = 1 := by exact_mod_cast h
    push_cast at this
    linarith
  have hNpos : 0 < N := M_pos hpos
  have h30N : 30 ∣ N := Finset.dvd_prod_of_mem _ h30
  have hN30 : 30 ≤ N := Nat.le_of_dvd hNpos h30N
  have hNq : (30 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN30
  have hn0 : (N : ℚ) ≠ 0 := by positivity
  have hn1 : (N : ℚ) - 1 ≠ 0 := by linarith
  have hsumP : (∑ x ∈ P, (x : ℚ)⁻¹) = ((N : ℚ) - 1) / N := by
    rw [sum_inv_eq hpos, hMA]
  have hprodP : (∏ x ∈ P, (x : ℚ)) = N := by simp [hNdef, M]
  -- R = P \ {30}: its elements are > 1 and coprime to 30
  set R := P.erase 30 with hRdef
  have hRcop : ∀ x ∈ R, Nat.Coprime x 30 := by
    intro x hx
    exact hpw (Finset.mem_of_mem_erase hx) h30 (Finset.ne_of_mem_erase hx)
  have hRgt : ∀ x ∈ R, 1 < x := by
    intro x hx
    have hx0 := hpos x (Finset.mem_of_mem_erase hx)
    have hx1 : x ≠ 1 := fun h => h1 (h ▸ Finset.mem_of_mem_erase hx)
    omega
  have hRc : ∀ x ∈ R, Nat.Coprime x 2 ∧ Nat.Coprime x 3 ∧ Nat.Coprime x 5 := by
    intro x hx
    have h := hRcop x hx
    exact ⟨h.coprime_dvd_right (by norm_num), h.coprime_dvd_right (by norm_num),
      h.coprime_dvd_right (by norm_num)⟩
  have h2R : 2 ∉ R := fun h => by have := (hRc 2 h).1; norm_num at this
  have h3R : 3 ∉ R := fun h => by have := (hRc 3 h).2.1; norm_num at this
  have h5R : 5 ∉ R := fun h => by have := (hRc 5 h).2.2; norm_num at this
  have h30R : 30 ∉ R := Finset.notMem_erase 30 P
  have hsumR : (∑ x ∈ R, (x : ℚ)⁻¹) = ((N : ℚ) - 1) / N - 1 / 30 := by
    have := Finset.add_sum_erase P (fun x => (x : ℚ)⁻¹) h30
    rw [hsumP] at this
    push_cast at this
    linarith
  have hprodR : (30 : ℚ) * (∏ x ∈ R, (x : ℚ)) = N := by
    have := Finset.mul_prod_erase P (fun x => (x : ℚ)) h30
    rw [hprodP] at this
    push_cast at this
    exact this
  -- S2 = R ∪ {2, 3, 5}
  set S2 := insert 2 (insert 3 (insert 5 R)) with hS2
  have h5 : 5 ∉ R := h5R
  have h3 : 3 ∉ insert 5 R := by simp [h3R]
  have h2 : 2 ∉ insert 3 (insert 5 R) := by simp [h2R]
  have hsumS2 : (∑ x ∈ S2, (x : ℚ)⁻¹) = ((N : ℚ) - 1) / N + 1 := by
    rw [hS2, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_insert h5, hsumR]
    push_cast; ring
  have hprodS2 : (∏ x ∈ S2, (x : ℚ)) = N := by
    rw [hS2, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_insert h5, ← hprodR]
    push_cast; ring
  have hprodS2N : (∏ x ∈ S2, x) = N := by
    have : ((∏ x ∈ S2, x : ℕ) : ℚ) = N := by push_cast; exact hprodS2
    exact_mod_cast this
  have hS2gt : ∀ x ∈ S2, 1 < x := by
    intro x hx
    simp only [hS2, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hx
    · norm_num
    · norm_num
    · norm_num
    · exact hRgt x hx
  have hS2pw : (S2 : Set ℕ).Pairwise Nat.Coprime := by
    have hRpw : (R : Set ℕ).Pairwise Nat.Coprime :=
      hpw.mono (by intro x hx; exact Finset.mem_of_mem_erase hx)
    rw [hS2]
    simp only [Finset.coe_insert]
    refine Set.Pairwise.insert ?_ ?_
    · refine Set.Pairwise.insert ?_ ?_
      · refine Set.Pairwise.insert hRpw ?_
        intro x hx _
        have := (hRc x hx).2.2
        exact ⟨this.symm, this⟩
      · intro x hx _
        rcases hx with rfl | hx
        · exact ⟨by norm_num, by norm_num⟩
        · have := (hRc x hx).2.1
          exact ⟨this.symm, this⟩
    · intro x hx _
      rcases hx with rfl | rfl | hx
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · have := (hRc x hx).1
        exact ⟨this.symm, this⟩
  -- the appended element z = N − 1
  have hz1 : 1 < N - 1 := by omega
  have hzq : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hz_notdvd : ¬ (N - 1) ∣ N := by
    intro h
    have h' : (N - 1) ∣ N - (N - 1) := Nat.dvd_sub h (dvd_refl _)
    rw [show N - (N - 1) = 1 by omega] at h'
    have := Nat.le_of_dvd one_pos h'
    omega
  have hzS2 : N - 1 ∉ S2 := by
    intro h
    have hd : (N - 1) ∣ ∏ x ∈ S2, x := Finset.dvd_prod_of_mem (fun x => x) h
    rw [hprodS2N] at hd
    exact hz_notdvd hd
  have hzP : N - 1 ∉ P := fun h => hz_notdvd (Finset.dvd_prod_of_mem _ h)
  refine ⟨⟨S2, hS2gt, hS2pw, ?_⟩, ⟨insert (N - 1) S2, ?_⟩,
    ⟨insert (N - 1) P, insert (N - 1) S2, ?_, ?_, ?_, ?_⟩⟩
  · rw [hsumS2, hprodS2]; field_simp; ring
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz1
      · exact hS2gt x hx
    · rw [Finset.sum_insert hzS2, Finset.prod_insert hzS2, hsumS2, hprodS2, hzq]
      push_cast; field_simp; ring
  · intro h
    have h30T : 30 ∈ insert (N - 1) P := Finset.mem_insert_of_mem h30
    rw [h] at h30T
    rcases Finset.mem_insert.mp h30T with h' | h'
    · have : 30 ∣ N - 1 + 1 := by rw [show N - 1 + 1 = N by omega]; exact h30N
      rw [← h'] at this
      norm_num at this
    · simp only [hS2, Finset.mem_insert] at h'
      rcases h' with h' | h' | h' | h'
      · norm_num at h'
      · norm_num at h'
      · norm_num at h'
      · exact h30R h'
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz1
      · have := hpos x hx
        have hx1 : x ≠ 1 := fun h => h1 (h ▸ hx)
        omega
    · rw [Finset.sum_insert hzP, Finset.prod_insert hzP, hsumP, hprodP, hzq]
      push_cast; field_simp; ring
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz1
      · exact hS2gt x hx
    · rw [Finset.sum_insert hzS2, Finset.prod_insert hzS2, hsumS2, hprodS2, hzq]
      push_cast; field_simp; ring
  · rw [Finset.prod_insert hzP, Finset.prod_insert hzS2, hprodS2N]
    rfl

end Erdos307
