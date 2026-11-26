import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18767_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_getD (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
      = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := foldl_getD _ _ _ h

end PEqualNP.Outside.L_meta_18767_aux

open PEqualNP.Outside.L_meta_18767_aux in
theorem PEqualNP.Outside.L_meta_18767 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size := by
  intro C ho _ hC _
  exfalso
  have h1 := (hC fun j => decide (j = ⟨C.output, ho⟩)).1 (by
    rw [eval_input C _ (by simpa using ho), List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
    simp)
  obtain ⟨a, b, _, _, ha, hb⟩ := h1
  simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at ha hb
  omega
