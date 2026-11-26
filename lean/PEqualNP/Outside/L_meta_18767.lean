import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18767

open PEqualNP.CircuitLowerBounds

private theorem inputRead (gates : List Gate) (w : List Bool) (i : ℕ)
    (h : i < w.length) :
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false
      = w.getD i false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g tail ih =>
    rw [List.foldl_cons, ih, List.getD_append _ _ _ _ h]
    simp
    omega

end PEqualNP.Outside.L_meta_18767

open PEqualNP.Outside.L_meta_18767 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18767 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size := by
  intro C ho _ computes _
  let j : Fin 26 := ⟨C.output,ho⟩
  let x : Fin 26 → Bool := fun k => decide (k = j)
  have good : C.eval (List.ofFn x) = true := by
    change (List.foldl _ (List.ofFn x) C.gates).getD C.output false = true
    have ok : C.output < (List.ofFn x).length := by simpa using ho
    rw [inputRead _ _ _ ok, List.getD_eq_getElem _ _ ok, List.getElem_ofFn]
    exact decide_eq_true rfl
  obtain ⟨p, l, _, _, hp, hl⟩ := (computes x).mp good
  have left : Fin.castAdd 13 p = j := of_decide_eq_true hp
  have right : Fin.natAdd 13 l = j := of_decide_eq_true hl
  have eq := congrArg Fin.val (left.trans right.symm)
  simp at eq
  omega

