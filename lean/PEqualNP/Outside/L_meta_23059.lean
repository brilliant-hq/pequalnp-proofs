import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23059 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948542 : ℕ).testBit (6 * u.val + v.val)) 17) := by
  refine ⟨⟨[
    ⟨.or, [7, 9]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.and, [0, 18]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [24, 23]⟩
  ], 25⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
