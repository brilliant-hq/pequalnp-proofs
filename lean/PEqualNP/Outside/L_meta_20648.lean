import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20648 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (13729792 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.and, [4, 13]⟩,
    ⟨.or, [12, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
