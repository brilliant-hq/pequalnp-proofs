import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23050 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947518 : ℕ).testBit (6 * u.val + v.val)) 16) := by
  refine ⟨⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.and, [0, 17]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [3, 16]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [23, 22]⟩
  ], 24⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
