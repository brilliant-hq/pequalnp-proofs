import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18759

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

end PEqualNP.Outside.L_meta_18759

open PEqualNP.Outside.L_meta_18759 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18759 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (32 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (32 : ℕ)) (x7 : Fin (32 : ℕ)), (↑x6 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x7 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x6 (0 : ℕ)).testBit (↑x7 - (16 : ℕ)) = Bool.true) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (79 : ℕ) ≤ x1.size := by
  intro C houtput _ _ computes
  let j : Fin 32 := ⟨C.output,houtput⟩
  let x : Fin 32 → Bool := fun k => decide (k = j)
  have good : C.eval (List.ofFn x) = true := by
    change (List.foldl _ (List.ofFn x) C.gates).getD C.output false = true
    have ok : C.output < (List.ofFn x).length := by simpa using houtput
    rw [inputRead _ _ _ ok, List.getD_eq_getElem _ _ ok, List.getElem_ofFn]
    exact decide_eq_true rfl
  obtain ⟨a,b,range,ha,hb⟩ := (computes x).mp good
  have aEq : a = j := of_decide_eq_true ha
  have bEq : b = j := of_decide_eq_true hb
  subst a
  subst b
  omega

