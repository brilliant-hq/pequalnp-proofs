import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21418 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112118 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [4, 15]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.and, [12, 16]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.or, [13, 19]⟩,
    ⟨.and, [17, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
