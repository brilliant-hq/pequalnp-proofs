import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24121

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [7, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266775 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24121

theorem PEqualNP.Outside.L_meta_24121 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266775 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24121.witness, PEqualNP.Outside.L_meta_24121.gatesOK, PEqualNP.Outside.L_meta_24121.sizeOK, PEqualNP.Outside.L_meta_24121.evalOK⟩
