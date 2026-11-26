import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19093 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1915 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 7]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · decide
