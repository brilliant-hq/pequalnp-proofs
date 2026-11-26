import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_20161 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13467367414173452220 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [2, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [10, 14]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 19]⟩, ⟨.or, [12, 13]⟩,
    ⟨.or, [7, 17]⟩, ⟨.or, [1, 20]⟩, ⟨.or, [4, 25]⟩, ⟨.or, [13, 15]⟩,
    ⟨.or, [9, 11]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [4, 16]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [1, 5]⟩,
    ⟨.and, [31, 33]⟩, ⟨.and, [29, 34]⟩, ⟨.and, [22, 26]⟩, ⟨.and, [2, 14]⟩,
    ⟨.and, [28, 32]⟩, ⟨.and, [23, 30]⟩, ⟨.and, [24, 27]⟩,
    ⟨.or, [36, 39]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [37, 43]⟩,
    ⟨.or, [41, 42]⟩, ⟨.or, [38, 45]⟩, ⟨.or, [44, 46]⟩], 47⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
