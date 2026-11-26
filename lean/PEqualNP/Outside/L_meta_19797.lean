import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19797 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  let C : Circuit := ⟨[⟨.or, [9, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [25, 13]⟩, ⟨.or, [26, 19]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [35, 15]⟩, ⟨.or, [36, 16]⟩, ⟨.and, [5, 37]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
