import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18666_aux

theorem main (R : Fin 12 → Fin 12 → Prop) [DecidableRel R] (x : Fin (12 + 12) → Bool)
    (hx : ¬∃ (p : Fin 12) (l : Fin 12), R p l ∧ x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 12 l) = true) :
    ∃ P : Fin 12 → Bool,
      (fun (T : Fin 12 → Bool) (p : Fin 12) => decide (∀ l, R p l → T l = false))
        ((fun (S : Fin 12 → Bool) (l : Fin 12) => decide (∀ p, R p l → S p = false)) P) = P ∧
      ∀ i, x i = true → Fin.addCases P ((fun (S : Fin 12 → Bool) (l : Fin 12) => decide (∀ p, R p l → S p = false)) P) i = true := by
  set A : (Fin 12 → Bool) → Fin 12 → Bool := fun S l => decide (∀ p, R p l → S p = false) with hA
  set B : (Fin 12 → Bool) → Fin 12 → Bool := fun T p => decide (∀ l, R p l → T l = false) with hB
  have le1 : ∀ S p, S p = true → B (A S) p = true := by
    intro S p hp
    simp only [hA, hB, decide_eq_true_iff, decide_eq_false_iff_not, not_forall]
    intro l hl
    exact ⟨p, hl, by simp [hp]⟩
  have anti : ∀ S S' : Fin 12 → Bool, (∀ p, S p = true → S' p = true) → ∀ l, A S' l = true → A S l = true := by
    intro S S' h l hl
    simp only [hA, decide_eq_true_iff] at hl ⊢
    intro p hp
    have := hl p hp
    cases hS : S p
    · rfl
    · simp [h p hS] at this
  have ABA : A (B (A (fun p => x (Fin.castAdd 12 p)))) = A (fun p => x (Fin.castAdd 12 p)) := by
    funext l
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact anti _ _ (le1 _) l
    · intro hl
      simp only [hA, decide_eq_true_iff]
      intro p hp
      cases h : B (A (fun p => x (Fin.castAdd 12 p))) p
      · rfl
      · exfalso
        simp only [hB, decide_eq_true_iff] at h
        have h2 := h l hp
        rw [h2] at hl
        exact Bool.false_ne_true hl
  refine ⟨B (A (fun p => x (Fin.castAdd 12 p))), ?_, ?_⟩
  · show B (A (B (A _))) = _
    rw [ABA]
  · intro i hi
    refine Fin.addCases (fun p hp => ?_) (fun l hl => ?_) i hi
    · rw [Fin.addCases_left]
      exact le1 _ p hp
    · rw [Fin.addCases_right]
      show A (B (A _)) l = true
      rw [ABA]
      simp only [hA, decide_eq_true_iff]
      intro p hp
      cases h : x (Fin.castAdd 12 p)
      · rfl
      · exact absurd ⟨p, l, hp, h, hl⟩ hx

end PEqualNP.Outside.L_meta_18666_aux

theorem PEqualNP.Outside.L_meta_18666 : ∀ (x1 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) [x2 : DecidableRel x1],   have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x1 x5 x4 → x3 x5 = Bool.false);   have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x1 x5 x6 → x4 x6 = Bool.false);   ∀ (x5 : Fin ((12 : ℕ) + (12 : ℕ)) → Bool), (¬∃ (x6 : Fin (12 : ℕ)) (x7 : Fin (12 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (12 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (12 : ℕ) x7) = Bool.true) → ∃ (x7 : Fin (12 : ℕ) → Bool), x4 (x3 x7) = x7 ∧ ∀ (x8 : Fin ((12 : ℕ) + (12 : ℕ))), x5 x8 = Bool.true → Fin.addCases x7 (x3 x7) x8 = Bool.true := by
  intro R inst
  exact fun x hx => PEqualNP.Outside.L_meta_18666_aux.main R x hx
