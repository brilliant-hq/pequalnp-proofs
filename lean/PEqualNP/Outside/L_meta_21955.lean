import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21955_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩

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

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33715 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨C_, fanTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21955_aux

theorem PEqualNP.Outside.L_meta_21955 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33715 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_21955_aux.main
