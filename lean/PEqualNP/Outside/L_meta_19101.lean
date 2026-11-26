import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19101 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6127 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [1, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 7]⟩,
      ⟨.or, [5, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [8, 10]⟩,
      ⟨.or, [13, 12]⟩, ⟨.not, [14]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.FanInTwo]
  · unfold PEqualNP.Represents.Represents
    decide +kernel
