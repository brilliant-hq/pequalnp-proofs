import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19825 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1432153032174414900 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [8, 18]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [25, 14]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [28, 15]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
