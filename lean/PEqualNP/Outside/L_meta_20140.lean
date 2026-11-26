import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20140 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3306370337538841395 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[
    ⟨.or, [8, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [14, 19]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.or, [8, 21]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [15, 26]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [13, 19]⟩,
    ⟨.or, [18, 28]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.and, [1, 29]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.and, [3, 31]⟩,
    ⟨.and, [4, 22]⟩,
    ⟨.and, [5, 27]⟩,
    ⟨.and, [6, 23]⟩,
    ⟨.and, [7, 30]⟩,
    ⟨.or, [35, 34]⟩,
    ⟨.or, [33, 36]⟩,
    ⟨.or, [37, 32]⟩,
    ⟨.or, [42, 40]⟩,
    ⟨.or, [43, 38]⟩,
    ⟨.or, [39, 41]⟩,
    ⟨.or, [44, 45]⟩
  ], 46⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
