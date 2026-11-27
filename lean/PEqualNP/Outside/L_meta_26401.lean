import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26401 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 3, 28, 31] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
