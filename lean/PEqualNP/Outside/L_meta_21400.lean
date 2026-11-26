import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21400 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112574 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [13, 16]⟩,
    ⟨.or, [7, 17]⟩,
    ⟨.or, [6, 18]⟩,
    ⟨.and, [15, 19]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
