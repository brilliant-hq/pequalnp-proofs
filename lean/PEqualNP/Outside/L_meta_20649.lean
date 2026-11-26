import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20649 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15761408 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨⟨[
    ⟨.and, [3, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.and, [12, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
