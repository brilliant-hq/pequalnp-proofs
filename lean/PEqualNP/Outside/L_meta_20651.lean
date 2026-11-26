import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20651 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15958016 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.and, [10, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
