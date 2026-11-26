import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.not, [7]⟩, ⟨.not, [4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩

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

theorem main : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨witness, fanTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25370

theorem PEqualNP.Outside.L_meta_25370 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact PEqualNP.Outside.L_meta_25370.main
