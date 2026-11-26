import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24259

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [9, 11]⟩], 12⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 7 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24259

theorem PEqualNP.Outside.L_meta_24259 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24259.witness, PEqualNP.Outside.L_meta_24259.gatesOK, PEqualNP.Outside.L_meta_24259.sizeOK, PEqualNP.Outside.L_meta_24259.evalOK⟩
