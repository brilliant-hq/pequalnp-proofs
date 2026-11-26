import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4428 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24102

theorem PEqualNP.Outside.L_meta_24102 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4428 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24102.witness, PEqualNP.Outside.L_meta_24102.gatesOK, PEqualNP.Outside.L_meta_24102.sizeOK, PEqualNP.Outside.L_meta_24102.evalOK⟩
