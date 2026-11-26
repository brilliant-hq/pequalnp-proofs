import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20568 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3677463 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [1, 9]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.not, [15]⟩,
    ⟨.or, [16, 17]⟩
  ], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
