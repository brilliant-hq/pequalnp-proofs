import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19099 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 1 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4095 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [3] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl <;> simp
  · decide +kernel
