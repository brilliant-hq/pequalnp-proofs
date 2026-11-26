import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21427 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245629 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.and, [12, 16]⟩,
    ⟨.or, [4, 18]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [19, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
