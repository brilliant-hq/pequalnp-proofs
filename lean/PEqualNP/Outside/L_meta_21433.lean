import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21433 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (515965 : ℕ).testBit (5 * u.val + v.val)) 14) := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [18, 20]⟩,
    ⟨.or, [19, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
