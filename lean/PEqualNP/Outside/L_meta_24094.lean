import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24094

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807511 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24094

theorem PEqualNP.Outside.L_meta_24094 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807511 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24094.witness, PEqualNP.Outside.L_meta_24094.gatesOK, PEqualNP.Outside.L_meta_24094.sizeOK, PEqualNP.Outside.L_meta_24094.evalOK⟩
