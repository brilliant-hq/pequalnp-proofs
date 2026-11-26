import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20430 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3686974 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [15, 17]⟩
  ], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
