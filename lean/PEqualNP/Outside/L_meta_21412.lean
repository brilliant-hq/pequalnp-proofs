import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21412 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47867 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.and, [4, 13]⟩,
    ⟨.and, [7, 15]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [16, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
