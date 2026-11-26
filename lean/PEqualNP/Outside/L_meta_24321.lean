import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24321

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [6, 11]⟩], 12⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 7 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377519 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24321

theorem PEqualNP.Outside.L_meta_24321 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377519 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24321.witness, PEqualNP.Outside.L_meta_24321.gatesOK, PEqualNP.Outside.L_meta_24321.sizeOK, PEqualNP.Outside.L_meta_24321.evalOK⟩
