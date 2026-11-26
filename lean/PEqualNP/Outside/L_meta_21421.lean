import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21421 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112348 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [15, 19]⟩,
    ⟨.or, [18, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
