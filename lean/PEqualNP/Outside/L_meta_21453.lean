import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21453_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.and,[0, 1]⟩, ⟨.or,[0, 1]⟩, ⟨.or,[2, 3]⟩, ⟨.and,[6, 7]⟩, ⟨.or,[5, 8]⟩], 9⟩

private def legalB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
      Nat.ble g.inputs.length 2

theorem legal : Monotone2 circuit := by
  intro g hg
  have all : legalB circuit = true := by decide +kernel
  have chk := List.all_eq_true.1 all g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at chk
  refine ⟨?_, chk.2⟩
  cases hop : g.op <;> simp [hop] at chk ⊢

end PEqualNP.Outside.L_meta_21453_aux

theorem PEqualNP.Outside.L_meta_21453 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (398 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21453_aux.circuit, PEqualNP.Outside.L_meta_21453_aux.legal, by decide +kernel, by decide +kernel⟩
