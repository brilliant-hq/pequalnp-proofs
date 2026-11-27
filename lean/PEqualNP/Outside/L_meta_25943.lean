import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25943 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 3, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
