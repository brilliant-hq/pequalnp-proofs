import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24429

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52540 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24429

theorem PEqualNP.Outside.L_meta_24429 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52540 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24429.witness, PEqualNP.Outside.L_meta_24429.gatesOK, PEqualNP.Outside.L_meta_24429.sizeOK, PEqualNP.Outside.L_meta_24429.evalOK⟩
