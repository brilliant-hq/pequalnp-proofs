import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18759_aux

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

end PEqualNP.Outside.L_meta_18759_aux

open PEqualNP.Outside.L_meta_18759_aux in
theorem PEqualNP.Outside.L_meta_18759 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (32 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (32 : ℕ)) (x7 : Fin (32 : ℕ)), (↑x6 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x7 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x6 (0 : ℕ)).testBit (↑x7 - (16 : ℕ)) = Bool.true) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (79 : ℕ) ≤ x1.size := by
  intro C ho _ _ h
  exfalso
  have h1 := (h (fun j => decide (j = ⟨C.output, ho⟩))).1 (by rw [eval_input C 32 _ ho]; simp)
  obtain ⟨a, b, ⟨ha, hb, _⟩, hxa, hxb⟩ := h1
  simp at hxa hxb
  subst hxa
  have := congrArg Fin.val hxb
  simp at this
  omega
