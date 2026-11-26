import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19741 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11683908189968026665 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [21, 14]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
