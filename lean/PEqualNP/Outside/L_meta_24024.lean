import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24024

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [9, 11]⟩], 12⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807647 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24024

theorem PEqualNP.Outside.L_meta_24024 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807647 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24024.witness, PEqualNP.Outside.L_meta_24024.gatesOK, PEqualNP.Outside.L_meta_24024.sizeOK, PEqualNP.Outside.L_meta_24024.evalOK⟩
