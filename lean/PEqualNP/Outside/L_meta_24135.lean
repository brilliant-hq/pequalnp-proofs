import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24135

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275164 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24135

theorem PEqualNP.Outside.L_meta_24135 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275164 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24135.witness, PEqualNP.Outside.L_meta_24135.gatesOK, PEqualNP.Outside.L_meta_24135.sizeOK, PEqualNP.Outside.L_meta_24135.evalOK⟩
