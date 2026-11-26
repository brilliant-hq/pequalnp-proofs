import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20049_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit := ⟨[
  { op := .or, inputs := [10, 11] },
  { op := .or, inputs := [9, 12] },
  { op := .or, inputs := [8, 14] },
  { op := .or, inputs := [13, 18] },
  { op := .or, inputs := [9, 15] },
  { op := .or, inputs := [16, 17] },
  { op := .or, inputs := [15, 19] },
  { op := .or, inputs := [13, 16] },
  { op := .or, inputs := [14, 23] },
  { op := .or, inputs := [24, 12] },
  { op := .and, inputs := [0, 25] },
  { op := .or, inputs := [11, 22] },
  { op := .and, inputs := [1, 27] },
  { op := .or, inputs := [12, 22] },
  { op := .and, inputs := [2, 29] },
  { op := .or, inputs := [19, 17] },
  { op := .and, inputs := [3, 31] },
  { op := .or, inputs := [18, 10] },
  { op := .or, inputs := [33, 20] },
  { op := .and, inputs := [4, 34] },
  { op := .or, inputs := [20, 23] },
  { op := .and, inputs := [5, 36] },
  { op := .or, inputs := [15, 21] },
  { op := .and, inputs := [6, 38] },
  { op := .or, inputs := [8, 21] },
  { op := .and, inputs := [7, 40] },
  { op := .or, inputs := [37, 32] },
  { op := .or, inputs := [42, 30] },
  { op := .or, inputs := [43, 41] },
  { op := .or, inputs := [44, 28] },
  { op := .or, inputs := [45, 26] },
  { op := .or, inputs := [46, 39] },
  { op := .or, inputs := [47, 35] }
], 48⟩

lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, circuit]

end PEqualNP.Outside.L_meta_20049_aux

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_20049 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2278450633163008380 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨PEqualNP.Outside.L_meta_20049_aux.circuit,
    PEqualNP.Outside.L_meta_20049_aux.monotone, ?_, ?_⟩
  · decide
  · decide +kernel
