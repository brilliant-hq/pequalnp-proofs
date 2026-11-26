import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24189 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283230 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩], 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
