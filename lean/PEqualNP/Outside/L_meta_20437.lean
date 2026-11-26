import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20437 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15768113 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [1, 13]⟩,
    ⟨.or, [7, 14]⟩,
    ⟨.or, [6, 15]⟩,
    ⟨.or, [0, 16]⟩,
    ⟨.and, [12, 17]⟩
  ], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
