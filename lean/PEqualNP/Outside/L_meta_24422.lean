import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24422

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24422

theorem PEqualNP.Outside.L_meta_24422 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24422.witness, PEqualNP.Outside.L_meta_24422.gatesOK, PEqualNP.Outside.L_meta_24422.sizeOK, PEqualNP.Outside.L_meta_24422.evalOK⟩
