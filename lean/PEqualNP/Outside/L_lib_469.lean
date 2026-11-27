import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_469 : ∀ (n m : ℕ) (P N : Fin m → Finset (Fin n)),
  (∃ x : Fin n → Bool, ∀ i, (∃ v ∈ P i, x v = true) ∨ (∃ v ∈ N i, x v = false)) ↔
    ∃ z : Fin n → ℤ, (∀ v, z v = 0 ∨ z v = 1) ∧
      ∀ i, 1 ≤ (P i).sum z + (N i).sum (fun v => 1 - z v) := by
  intro n m P N
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun v => if x v = true then 1 else 0, fun v => by by_cases h : x v = true <;> simp [h], fun i => ?_⟩
    have h1 : 0 ≤ (P i).sum (fun v => if x v = true then (1:ℤ) else 0) :=
      Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
    have h2 : 0 ≤ (N i).sum (fun v => 1 - if x v = true then (1:ℤ) else 0) :=
      Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
    rcases hx i with ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
    · have := Finset.single_le_sum (f := fun v => if x v = true then (1:ℤ) else 0)
        (fun v _ => by split_ifs <;> norm_num) hv
      simp only [hxv, ↓reduceIte] at this
      dsimp only; linarith
    · have := Finset.single_le_sum (f := fun v => 1 - if x v = true then (1:ℤ) else 0)
        (fun v _ => by split_ifs <;> norm_num) hv
      simp only [hxv, Bool.false_eq_true, ↓reduceIte, sub_zero] at this
      dsimp only; linarith
  · rintro ⟨z, hz, hs⟩
    refine ⟨fun v => decide (z v = 1), fun i => ?_⟩
    by_contra hc
    simp only [not_or, not_exists, not_and, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hc
    obtain ⟨hp, hn⟩ := hc
    have e1 : (P i).sum z = 0 := Finset.sum_eq_zero (fun v hv => by
      rcases hz v with h | h
      · exact h
      · exact absurd h (hp v hv))
    have e2 : (N i).sum (fun v => 1 - z v) = 0 := Finset.sum_eq_zero (fun v hv => by
      rw [hn v hv]; norm_num)
    have := hs i
    rw [e1, e2] at this
    norm_num at this
