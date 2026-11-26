import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23049 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947514 : ℕ).testBit (6 * u.val + v.val)) 16) := by
  refine ⟨⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [20, 19]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [22, 18]⟩
  ], 23⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
