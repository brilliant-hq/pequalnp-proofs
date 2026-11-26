import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24762

theorem PEqualNP.Outside.L_meta_24762 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24762.witness, PEqualNP.Outside.L_meta_24762.gatesOK, PEqualNP.Outside.L_meta_24762.sizeOK, PEqualNP.Outside.L_meta_24762.evalOK⟩
