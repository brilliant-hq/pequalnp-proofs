import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22788 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16799 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨(⟨
      [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩],
      10⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
