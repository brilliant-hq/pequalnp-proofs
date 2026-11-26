import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19656 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881169 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 15]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
