import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21434 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241598 : ℕ).testBit (5 * u.val + v.val)) 15) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.or, [7, 15]⟩,
    ⟨.and, [9, 17]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [11, 19]⟩,
    ⟨.and, [14, 20]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.or, [18, 22]⟩
  ], 23⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
