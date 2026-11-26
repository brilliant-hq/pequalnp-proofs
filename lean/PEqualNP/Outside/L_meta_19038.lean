import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19038 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4731 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
