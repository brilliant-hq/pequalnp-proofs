import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18779

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

end PEqualNP.Outside.L_meta_18779

open PEqualNP.Outside.L_meta_18779 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18779 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C ho _ _ computes
  let j : Fin 42 := ⟨C.output,ho⟩
  let x : Fin 42 → Bool := fun k => decide (k = j)
  have good : C.eval (List.ofFn x) = true := by
    change (List.foldl _ (List.ofFn x) C.gates).getD C.output false = true
    have ok : C.output < (List.ofFn x).length := by simpa using ho
    rw [inputRead _ _ _ ok, List.getD_eq_getElem _ _ ok, List.getElem_ofFn]
    exact decide_eq_true rfl
  obtain ⟨a,b,range,ha,hb⟩ := (computes x).mp good
  have aEq : a = j := of_decide_eq_true ha
  have bEq : b = j := of_decide_eq_true hb
  subst a
  subst b
  omega

