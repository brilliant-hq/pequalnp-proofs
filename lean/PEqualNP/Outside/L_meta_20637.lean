import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20637 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3178496 : ℕ).testBit (5 * u.val + v.val)) 4) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
