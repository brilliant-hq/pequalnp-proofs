import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21998_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.not, [10]⟩, ⟨.and, [2, 11]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩

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

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17175 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21998_aux

theorem PEqualNP.Outside.L_meta_21998 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17175 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_21998_aux.main
