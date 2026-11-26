import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20647 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11763712 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [13, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
