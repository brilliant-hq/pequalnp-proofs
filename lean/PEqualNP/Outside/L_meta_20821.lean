import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20821_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
    simp [stepW, List.getD, List.getElem?_append_left hi]

theorem fold_getD_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ (gs[j]).inputs, i < w.length + j) →
    (gs.foldl stepW w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (gs.foldl stepW w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hr
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.foldl_cons, Nat.add_zero] at hr ⊢
      rw [fold_getD_lt gs (stepW w g) w.length (by simp [stepW])]
      have hm : (g.inputs.map fun i => (gs.foldl stepW (stepW w g)).getD i false) =
          g.inputs.map fun i => w.getD i false := by
        apply List.map_congr_left
        intro i hi
        rw [fold_getD_lt gs (stepW w g) i (by simp [stepW]; have := hr i hi; omega)]
        simp [stepW, List.getD, List.getElem?_append_left (hr i hi)]
      rw [hm]
      simp [stepW, List.getD]
    | succ j =>
      simp only [List.getElem_cons_succ, List.foldl_cons] at hr ⊢
      have hl : w.length + (j + 1) = (stepW w g).length + j := by simp [stepW]; omega
      rw [hl]
      exact ih (stepW w g) j (by simp at hj; omega) (fun i hi => by rw [← hl]; exact hr i hi)

end PEqualNP.Outside.L_meta_20821_aux

open PEqualNP.Outside.L_meta_20821_aux in
theorem PEqualNP.Outside.L_meta_20821 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → (∀ i ∈ S, i < m) → (∀ j ∈ Rg, j < C.size) →
  (∀ j ∈ Rg,
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg)) →
  ∀ x : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∈ S → x i = false) →
    ∀ j ∈ Rg, (C.wires (List.ofFn x)).getD (m + j) false = false := by
  intro m C S Rg hRB hS hRg hgate x hx
  have hW : C.wires (List.ofFn x) = C.gates.foldl stepW (List.ofFn x) := rfl
  rw [hW]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hjs : j < C.gates.length := hRg j hj
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hjs]
    have hr := hRB j hjs
    rw [hga] at hr
    have key := fold_getD_gate C.gates (List.ofFn x) j hjs (by rw [List.length_ofFn]; exact hr)
    rw [List.length_ofFn] at key
    rw [key, ← hga]
    have hall : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.gates.foldl stepW (List.ofFn x)).getD i false = false := by
      intro i hi
      rcases (hgate j hj).2 i hi with hiS | ⟨hmi, hiR⟩
      · have him : i < m := hS i hiS
        rw [fold_getD_lt _ _ _ (by rw [List.length_ofFn]; exact him)]
        have : (List.ofFn x).getD i false = x ⟨i, him⟩ := by
          simp [List.getD_eq_getElem?_getD, him]
        rw [this]
        exact hx ⟨i, him⟩ hiS
      · have hil : i < m + j := by rw [hga] at hi; exact hr i hi
        have h2 := ih (i - m) (by omega) hiR
        rwa [show m + (i - m) = i by omega] at h2
    obtain ⟨hop, hlen⟩ := (hgate j hj).1
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    rw [hab] at hall ⊢
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    rcases hop with h | h <;> rw [h] <;>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, ha, hb] <;> rfl
