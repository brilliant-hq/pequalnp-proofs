import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25217

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩
      , ⟨GateOp.or, [5, 0]⟩
      , ⟨GateOp.or, [1, 2]⟩
      , ⟨GateOp.or, [1, 0]⟩
      , ⟨GateOp.and, [8, 7]⟩
      , ⟨GateOp.or, [3, 10]⟩
      , ⟨GateOp.not, [11]⟩
      , ⟨GateOp.and, [12, 9]⟩
      , ⟨GateOp.and, [3, 2]⟩
      , ⟨GateOp.or, [13, 14]⟩
      ]
    output := 15 }

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | GateOp.and => true
     | GateOp.or => true
     | GateOp.not => true
     | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanInTwoB_sound (C : Circuit) (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_proof : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34225 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanInTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25217

theorem PEqualNP.Outside.L_meta_25217 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34225 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := PEqualNP.Outside.L_meta_25217.main_proof
