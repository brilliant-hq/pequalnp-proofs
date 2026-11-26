import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23986

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩], 12⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13147 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23986

theorem PEqualNP.Outside.L_meta_23986 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13147 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_23986.witness, PEqualNP.Outside.L_meta_23986.gatesOK, PEqualNP.Outside.L_meta_23986.sizeOK, PEqualNP.Outside.L_meta_23986.evalOK⟩
