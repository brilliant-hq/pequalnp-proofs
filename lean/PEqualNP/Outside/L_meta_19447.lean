import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19447 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236078 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
