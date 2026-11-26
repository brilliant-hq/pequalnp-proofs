import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24187 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266846 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩], 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
