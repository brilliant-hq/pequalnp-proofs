import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22104_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 8]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [2, 0]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.not, [15]⟩], 16⟩

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

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17331 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22104_aux

theorem PEqualNP.Outside.L_meta_22104 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17331 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_22104_aux.main
