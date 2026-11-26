import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18755
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem stable (gs : List Gate) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

end PEqualNP.Outside.L_meta_18755

open PEqualNP.Outside.L_meta_18755 in
theorem PEqualNP.Outside.L_meta_18755 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C hraw _ _ computes
  let i : Fin 42 := ⟨C.output,hraw⟩
  let x : Fin 42 → Bool := fun w => decide (w = i)
  have yes : C.eval (List.ofFn x) = true := by
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true
    rw [stable _ _ _ (by simp [hraw])]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hraw,dite_true,Option.getD_some]
    exact decide_eq_true (rfl : i = i)
  obtain ⟨l,r,⟨hl,hr,_⟩,le,re⟩ := (computes x).mp yes
  have a : l = i := of_decide_eq_true le
  have b : r = i := of_decide_eq_true re
  subst l; subst r
  omega
