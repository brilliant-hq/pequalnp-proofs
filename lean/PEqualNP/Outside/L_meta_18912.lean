import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18912

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ev_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_eq_true, List.any_eq_true,
    List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩
    subst hx
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem key : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl stp U).getD i false = true → (gs.foldl stp V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stp, hl]
    · intro k hk
      unfold stp at hk ⊢
      rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hk
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h k hk
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact ev_mono g (hgs g (List.mem_cons_self ..)) U V h hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        exact absurd hk (by simp)

theorem fa_getD : ∀ (U V : List Bool), List.Forall₂ (fun a b : Bool => a ≤ b) U V →
    ∀ i, U.getD i false = true → V.getD i false = true := by
  intro U V h
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      rw [hi] at hab
      exact le_antisymm (by simp) hab |>.symm ▸ rfl
    | succ i =>
      simp only [List.getD_cons_succ] at hi ⊢
      exact ih i hi

end PEqualNP.Outside.L_meta_18912

open PEqualNP.Outside.L_meta_18912 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18912 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : List Bool), List.Forall₂ (fun (x5 x6 : Bool) => x5 ≤ x6) x3 x4 → ∀ (x6 : ℕ), (x1.wires x3).getD x6 Bool.false ≤ (x1.wires x4).getD x6 Bool.false := by
  intro C hC U V h w
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have k := key C.gates hgs U V h.length_eq (fa_getD U V h) w
  cases hu : (C.wires U).getD w false
  · exact Bool.false_le _
  · have := k hu
    change (List.foldl stp V C.gates).getD w false = true at this
    show true ≤ (List.foldl stp V C.gates).getD w false
    rw [this]
