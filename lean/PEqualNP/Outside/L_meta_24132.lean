import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24132

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275095 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24132

theorem PEqualNP.Outside.L_meta_24132 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275095 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24132.witness, PEqualNP.Outside.L_meta_24132.gatesOK, PEqualNP.Outside.L_meta_24132.sizeOK, PEqualNP.Outside.L_meta_24132.evalOK⟩
