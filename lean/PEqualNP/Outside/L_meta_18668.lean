import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18668_aux

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

end PEqualNP.Outside.L_meta_18668_aux

open PEqualNP.Outside.L_meta_18668_aux in
theorem PEqualNP.Outside.L_meta_18668 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (24 : ℕ) → Bool), (∀ (x5 : Fin (24 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C hC x y hxy k hk
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h := (hC g hgm).1
    simpa using h
  have hR : R (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun i hi => ?_⟩
    by_cases h : i < 24
    · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      simp at hi
  exact (fold C.gates hg _ _ hR).2 k hk
