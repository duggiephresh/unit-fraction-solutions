import Erdos307.Square
import Erdos307.Descent

/-!
# Kernel check of implicit descent chains (Claude, 2026-11-25)

A chain is given by `Q`, a seed `P₀` and deviations `d₀, d₁, …, dₙ`. The elements are
`sⱼ = (Eⱼ + dⱼ₊₁)/dⱼ` with `E₀ = A(Q)·M(P₀)` and `Eⱼ₊₁ = Eⱼ·sⱼ`. They are never computed: a Bool checker
works with residues only, and `chain_sound` turns a `true` answer into the hypotheses of `closing`.

* `implicit_step`: one step preserves admissibility, cross-coprimality and `1 ∉ P`, and moves `Dev` from
  `d` to `d'`.
* `stepCheck`, `stepCheck_sound`: the residue checker and its soundness.
-/

namespace Erdos307

open Finset

/-- **One implicit step.** If `s·d = E + d'` with `E = A(Q)·M(P)`, `d'` coprime to `E`, `s` coprime to
every element of `Q` and `s > 1`, then `insert s P` is again admissible, cross-coprime with `Q`, free
of `1`, and has deviation `d'`. -/
theorem implicit_step {P Q : Finset ℕ} {d d' s : ℕ}
    (hP : Admissible P) (hcross : ∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) (h1 : 1 ∉ P)
    (hdev : Dev P Q = d)
    (hs : s * d = A Q * M P + d') (hcop : Nat.Coprime d' (A Q * M P))
    (hsQ : ∀ q ∈ Q, Nat.Coprime s q) (hs1 : 1 < s) :
    s ∉ P ∧ Admissible (insert s P) ∧ (∀ a ∈ insert s P, ∀ b ∈ Q, Nat.Coprime a b) ∧
      1 ∉ insert s P ∧ Dev (insert s P) Q = d' ∧ A Q * M (insert s P) = (A Q * M P) * s := by
  set E := A Q * M P with hE
  -- s is coprime to E: a common prime would divide s·d − E = d'
  have hsE : Nat.Coprime s E := by
    apply Nat.coprime_of_dvd
    intro l hl hls hlE
    have h1' : l ∣ E + d' := hs ▸ Dvd.dvd.mul_right hls d
    have hld' : l ∣ d' := (Nat.dvd_add_right hlE).mp h1'
    have : l ∣ Nat.gcd d' E := Nat.dvd_gcd hld' hlE
    rw [hcop] at this
    exact hl.one_lt.ne' (Nat.dvd_one.mp this)
  have hMdvd : ∀ p ∈ P, p ∣ E := fun p hp =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hp) _
  have hsP : s ∉ P := by
    intro hsP
    have : Nat.gcd s E = s := Nat.gcd_eq_left (hMdvd s hsP)
    rw [hsE] at this
    omega
  refine ⟨hsP, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert]
    refine Set.Pairwise.insert hP.2 fun p hp _ => ?_
    have hc : Nat.Coprime s p := Nat.Coprime.coprime_dvd_right (hMdvd p hp) hsE
    exact ⟨hc, hc.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hsQ b hb
    · exact hcross a ha b hb
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact h1 h
  · have hS : ∀ x ∈ ({s} : Finset ℕ), 0 < x := by
      intro x hx; rw [Finset.mem_singleton] at hx; omega
    have hdisj : Disjoint P {s} := Finset.disjoint_singleton_right.mpr hsP
    have hform := dev_union (Q := Q) hP.1 hS hdisj
    have hMs : M ({s} : Finset ℕ) = s := by simp [M]
    have hAs : A ({s} : Finset ℕ) = 1 := by
      simp only [A, hMs, Finset.sum_singleton]; exact Nat.div_self (by omega)
    rw [show insert s P = P ∪ {s} by rw [Finset.insert_eq, Finset.union_comm], hform, hMs, hAs, hdev]
    have : ((s * d : ℕ) : ℤ) = ((E + d' : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    simp only [hE] at this ⊢
    push_cast
    linarith
  · rw [M, Finset.prod_insert hsP]
    simp only [hE, M]
    ring

/-- Cap for the running lower bound on `E` (any value ≥ 2·max dⱼ works). -/
def capLB : ℕ := 10 ^ 200

/-- **The residue checker.** `R` is the current modulus, `Em` the residue of the implicit `E`, `lb` a lower
bound for `E`, `d` the current deviation; the list holds the remaining deviations. -/
def stepCheck (qs : List ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | _, _, _, d, [] => d == 1
  | R, Em, lb, d, d' :: rest =>
    ((Em + d') % d == 0) && (Nat.gcd (Em % d') d' == 1) && (d' != 0) &&
      qs.all (fun q => Nat.gcd ((((Em + d') % R) / d) % q) q == 1) && Nat.ble (2 * d) (lb + d') &&
      stepCheck qs (R / d) ((Em % (R / d)) * (((Em + d') % R) / d) % (R / d))
        (min capLB (lb * ((lb + d') / d))) d' rest

/-- **Soundness of the residue checker.** -/
theorem stepCheck_sound {Q : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs) :
    ∀ (rest : List ℕ) (P : Finset ℕ) (d R Em lb : ℕ),
      Admissible P → (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) → 1 ∉ P → P.Nonempty →
      Dev P Q = d → 0 < d → R = M Q * (d :: rest).prod → Em ≡ A Q * M P [MOD R] →
      lb ≤ A Q * M P → stepCheck qs R Em lb d rest = true →
      ∃ P' : Finset ℕ, Admissible P' ∧ (∀ a ∈ P', ∀ b ∈ Q, Nat.Coprime a b) ∧ 1 ∉ P' ∧
        P'.Nonempty ∧ Dev P' Q = 1 := by
  intro rest
  induction rest with
  | nil =>
    intro P d R Em lb hP hcross h1 hne hdev _ _ _ _ hchk
    simp only [stepCheck, beq_iff_eq] at hchk
    exact ⟨P, hP, hcross, h1, hne, by rw [hdev, hchk]; rfl⟩
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
    -- (i) integrality
    have hEmd : Em ≡ E [MOD d] := Nat.ModEq.of_dvd hdR hEm
    have hdiv : d ∣ E + d' := by
      apply Nat.dvd_of_mod_eq_zero
      have := (hEmd.add_right d').symm
      unfold Nat.ModEq at this; rw [this]; exact hi
    set s := (E + d') / d with hsdef
    have hs : s * d = E + d' := Nat.div_mul_cancel hdiv
    -- (ii) coprimality with E
    have hcop : Nat.Coprime d' E := by
      have h' : Em % d' = E % d' := Nat.ModEq.of_dvd hd'R hEm
      rw [h'] at hii
      unfold Nat.Coprime; rw [Nat.gcd_rec]; exact hii
    -- s modulo Rn
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
    -- (iii) s coprime to Q
    have hsQ : ∀ q ∈ Q, Nat.Coprime s q := by
      intro q hq
      have hqRn : q ∣ Rn := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hq) _
      have h3 := hiii q (hqs q hq)
      have h' : (((Em + d') % R) / d) % q = s % q := Nat.ModEq.of_dvd hqRn hsm
      rw [h'] at h3
      have : Nat.gcd q s = 1 := by rw [Nat.gcd_rec]; exact h3
      exact Nat.Coprime.symm this
    -- (iv) s > 1
    have hs1 : 1 < s := by
      have h2 : 2 * d ≤ E + d' := le_trans hiv (by omega)
      rw [← hs] at h2
      have : 2 ≤ s := Nat.le_of_mul_le_mul_right (by rw [mul_comm] at h2; linarith [h2]) hd
      omega
    obtain ⟨hsP, hP', hcross', h1', hdev', hE'⟩ :=
      implicit_step hP hcross h1 hdev hs hcop hsQ hs1
    refine ih (insert s P) d' Rn ((Em % Rn) * (((Em + d') % R) / d) % Rn)
      (min capLB (lb * ((lb + d') / d))) hP' hcross' h1' (Finset.insert_nonempty _ _) hdev'
      (by omega) hRn ?_ ?_ ?_
    · rw [hE']
      have hEmRn : Em % Rn ≡ E [MOD Rn] := (Nat.mod_modEq _ _).trans (Nat.ModEq.of_dvd hRnR hEm)
      exact (Nat.mod_modEq _ _).trans (hEmRn.mul hsm)
    · rw [hE']
      refine le_trans (min_le_right _ _) (Nat.mul_le_mul hlb ?_)
      exact Nat.div_le_div_right (by omega)
    · rw [hRdiv] at hnext; exact hnext

/-- **From a passing check to the open statement.** -/
theorem coprime_one_notMem_of_stepCheck {Q P0 : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs)
    (hQ : Admissible Q) (hQne : Q.Nonempty) (h1Q : 1 ∉ Q)
    (hP0 : Admissible P0) (hcross : ∀ a ∈ P0, ∀ b ∈ Q, Nat.Coprime a b) (h1P : 1 ∉ P0)
    (hP0ne : P0.Nonempty) {d0 : ℕ} (hdev : Dev P0 Q = d0) (hd0 : 0 < d0) (rest : List ℕ)
    (hchk : stepCheck qs (M Q * (d0 :: rest).prod) ((A Q * M P0) % (M Q * (d0 :: rest).prod))
      (A Q * M P0) d0 rest = true) : CoprimeOneNotMem := by
  obtain ⟨P, hP, hc, h1, hne, hdev1⟩ := stepCheck_sound hqs rest P0 d0 _ _ _ hP0 hcross h1P hP0ne
    hdev hd0 rfl (Nat.mod_modEq _ _) le_rfl hchk
  refine closes_of_dev_one ⟨hP, hQ, hc, hne, hQne, ?_, by rw [hdev1]; norm_num⟩ hdev1
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact h1 h
  · exact h1Q h

end Erdos307
