import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19864 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15374695358257377210 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨⟨[
    ⟨.or, [8, 10]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [15, 21]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [24, 17]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [10, 21]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [31, 19]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.or, [34, 19]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [37, 18]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [12, 20]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 41]⟩
  ], 48⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
