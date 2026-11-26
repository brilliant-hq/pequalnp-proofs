import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24093 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807507 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
