import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24516 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148285 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩], 13⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
