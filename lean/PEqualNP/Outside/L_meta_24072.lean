import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24072

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [9, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266909 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24072

theorem PEqualNP.Outside.L_meta_24072 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266909 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24072.witness, PEqualNP.Outside.L_meta_24072.gatesOK, PEqualNP.Outside.L_meta_24072.sizeOK, PEqualNP.Outside.L_meta_24072.evalOK⟩
