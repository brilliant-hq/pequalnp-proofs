import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22223 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849401 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let C : Circuit := ⟨[⟨.and, [3, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 13]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [12, 15]⟩,
    ⟨.or, [9, 17]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [4, 20]⟩], 21⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
