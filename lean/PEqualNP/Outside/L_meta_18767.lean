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

