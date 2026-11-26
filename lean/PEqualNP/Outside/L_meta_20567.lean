import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20567 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16254518 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [14, 17]⟩
  ], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
