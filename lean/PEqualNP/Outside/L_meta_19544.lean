import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19544 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4590 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.not, [10]⟩,
    ⟨.or, [9, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
