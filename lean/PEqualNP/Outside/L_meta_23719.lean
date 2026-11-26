import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23719_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [7, 9]⟩], 10⟩

def fanTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanTwoB_sound (C : Circuit) (h : fanTwoB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (414 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23719_aux

theorem PEqualNP.Outside.L_meta_23719 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (414 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_23719_aux.main
