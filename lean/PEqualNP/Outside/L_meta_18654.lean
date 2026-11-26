import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18654_aux

open PEqualNP.CircuitLowerBounds

def R (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

theorem step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : R a b) :
    R (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hl, hv⟩ := h
  have hev : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hg | hg <;> rw [hg] <;> simp [GateOp.eval]
    · intro H j hj; exact hv _ (H j hj)
    · intro j hj H; exact ⟨j, hj, hv _ H⟩
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rcases lt_trichotomy i a.length with h1 | h1 | h1
  · rw [List.getD_append _ _ _ _ h1] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ h1)]
    exact hv _ hi
  · subst h1
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp at hi ⊢
    exact hev hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

theorem fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, R a b →
      R (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (step g (hg g (by simp)) a b h)

end PEqualNP.Outside.L_meta_18654_aux

open PEqualNP.Outside.L_meta_18654_aux in
theorem PEqualNP.Outside.L_meta_18654 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → ∀ (x7 : ℕ), PEqualNP.ReadTwo.wval x2 x4 x7 = Bool.true → PEqualNP.ReadTwo.wval x2 x5 x7 = Bool.true := by
  intro n C hC x y hxy w hw
  have h0 : R (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    rcases Nat.lt_or_ge i n with h | h
    · rw [dif_pos h] at hi ⊢
      exact hxy _ hi
    · rw [dif_neg (by omega)] at hi
      simp at hi
  exact (fold C.gates hC.1 _ _ h0).2 w hw
