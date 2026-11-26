import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24197

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 6 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24197

theorem PEqualNP.Outside.L_meta_24197 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24197.witness, PEqualNP.Outside.L_meta_24197.gatesOK, PEqualNP.Outside.L_meta_24197.sizeOK, PEqualNP.Outside.L_meta_24197.evalOK⟩
