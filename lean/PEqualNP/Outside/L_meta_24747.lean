import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24747

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [10, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100269 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24747

theorem PEqualNP.Outside.L_meta_24747 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100269 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24747.witness, PEqualNP.Outside.L_meta_24747.gatesOK, PEqualNP.Outside.L_meta_24747.sizeOK, PEqualNP.Outside.L_meta_24747.evalOK⟩
