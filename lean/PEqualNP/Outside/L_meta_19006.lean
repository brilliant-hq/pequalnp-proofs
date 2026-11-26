import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19006_aux

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

theorem fa (a b : List Bool) (h : List.Forall₂ (fun (x5 x6 : Bool) => x5 ≤ x6) a b) :
    ∀ i, a.getD i false = true → b.getD i false = true := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi
    cases i with
    | zero =>
      simp at hi ⊢
      subst hi
      revert hab
      decide +revert
    | succ n => simpa using ih n (by simpa using hi)

end PEqualNP.Outside.L_meta_19006_aux

open PEqualNP.Outside.L_meta_19006_aux in
theorem PEqualNP.Outside.L_meta_19006 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : Fin x1), x3 x6 = Bool.true → x4 x6 = Bool.true) → x2.eval (List.ofFn x3) = Bool.true → x2.eval (List.ofFn x4) = Bool.true := by
  intro n C x y hC hxy hx
  have hxy2 : List.Forall₂ (fun (x5 x6 : Bool) => x5 ≤ x6) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by rw [List.length_ofFn, List.length_ofFn], fun i h1 h2 => ?_⟩
    rw [List.get_ofFn, List.get_ofFn]
    simp only [Fin.cast_mk]
    have := hxy ⟨i, by simpa using h1⟩
    revert this
    cases x ⟨i, by simpa using h1⟩ <;> cases y ⟨i, by simpa using h1⟩ <;> decide
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h := (hC g hgm).1
    simpa using h
  have hR : R (List.ofFn x) (List.ofFn y) := ⟨hxy2.length_eq, fa _ _ hxy2⟩
  have h2 := (fold C.gates hg _ _ hR).2 C.output
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at hx ⊢
  exact h2 hx
