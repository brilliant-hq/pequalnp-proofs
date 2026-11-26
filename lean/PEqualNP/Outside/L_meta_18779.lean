import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18779_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (ho : C.output < n) :
    C.eval (List.ofFn x) = x ⟨C.output, ho⟩ := by
  unfold Circuit.eval Circuit.wires
  rw [foldl_getD _ _ _ (by simpa using ho)]
  simp [List.getD_eq_getElem?_getD, ho]

end PEqualNP.Outside.L_meta_18779_aux

open PEqualNP.Outside.L_meta_18779_aux in
theorem PEqualNP.Outside.L_meta_18779 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C ho _ _ h
  exfalso
  have h1 := (h (fun j => decide (j = ⟨C.output, ho⟩))).1 (by rw [eval_input C 42 _ ho]; simp)
  obtain ⟨a, b, ⟨ha, hb, _⟩, hxa, hxb⟩ := h1
  simp at hxa hxb
  subst hxa
  have := congrArg Fin.val hxb
  simp at this
  omega
