import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24056

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 12]⟩], 13⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 9 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12891 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24056

theorem PEqualNP.Outside.L_meta_24056 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12891 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24056.witness, PEqualNP.Outside.L_meta_24056.gatesOK, PEqualNP.Outside.L_meta_24056.sizeOK, PEqualNP.Outside.L_meta_24056.evalOK⟩
