import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21648_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩

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

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21648_aux

theorem PEqualNP.Outside.L_meta_21648 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_21648_aux.main
