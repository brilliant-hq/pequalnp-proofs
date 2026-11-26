import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20652 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6390784 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [13, 15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
