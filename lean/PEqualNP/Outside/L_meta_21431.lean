import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21431 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241565 : ℕ).testBit (5 * u.val + v.val)) 14) := by
  refine ⟨⟨[
    ⟨.and, [0, 4]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.and, [6, 12]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [7, 16]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [2, 19]⟩,
    ⟨.and, [18, 20]⟩,
    ⟨.or, [15, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
