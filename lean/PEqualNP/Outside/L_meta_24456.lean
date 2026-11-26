import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [9, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24456

theorem PEqualNP.Outside.L_meta_24456 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24456.witness, PEqualNP.Outside.L_meta_24456.gatesOK, PEqualNP.Outside.L_meta_24456.sizeOK, PEqualNP.Outside.L_meta_24456.evalOK⟩
