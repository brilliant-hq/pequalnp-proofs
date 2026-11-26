import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21966_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.or,[0, 1]⟩, ⟨.or,[2, 4]⟩, ⟨.and,[6, 7]⟩, ⟨.or,[0, 2]⟩, ⟨.or,[1, 3]⟩, ⟨.and,[9, 10]⟩, ⟨.or,[8, 11]⟩], 12⟩

private def legalB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
      Nat.ble g.inputs.length 2

theorem legal : FanInTwo circuit := by
  intro g hg
  have all : legalB circuit = true := by decide +kernel
  have chk := List.all_eq_true.1 all g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at chk
  refine ⟨?_, chk.2⟩
  cases hop : g.op <;> simp [hop] at chk ⊢

end PEqualNP.Outside.L_meta_21966_aux

theorem PEqualNP.Outside.L_meta_21966 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21966_aux.circuit, PEqualNP.Outside.L_meta_21966_aux.legal, by decide +kernel, by decide +kernel⟩
