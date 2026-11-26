import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18775_aux

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

theorem key : ∀ o : Fin 10, ((fun j : Fin 10 => decide (j = o)) (0 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (1 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (1 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (2 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (2 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (3 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (3 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (4 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (4 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (0 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (0 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (5 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (1 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (6 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (2 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (7 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (3 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (8 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (4 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (9 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (5 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (7 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (7 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (9 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (9 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (6 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (6 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (8 : Fin (10 : ℕ)) || (fun j : Fin 10 => decide (j = o)) (8 : Fin (10 : ℕ)) && (fun j : Fin 10 => decide (j = o)) (5 : Fin (10 : ℕ))) = false := by
  decide

end PEqualNP.Outside.L_meta_18775_aux

open PEqualNP.Outside.L_meta_18775_aux in
theorem PEqualNP.Outside.L_meta_18775 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (10 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  intro C ho _ _ _
  refine ⟨fun j => decide (j = ⟨C.output, ho⟩), ?_⟩
  rw [key ⟨C.output, ho⟩, eval_input C _ (by simpa using ho)]
  rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
  simp
