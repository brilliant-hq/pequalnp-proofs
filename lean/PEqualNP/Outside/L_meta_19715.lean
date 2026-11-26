import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19715
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [23, 17]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [26, 18]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [33, 19]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [6, 36]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [38, 13]⟩,
    ⟨.or, [39, 14]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 32]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 41]⟩
  ], 48⟩

end PEqualNP.Outside.L_meta_19715

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_19715 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7598353482589123020 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨PEqualNP.Outside.L_meta_19715.circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_19715.circuit]
  · decide +kernel
  · decide +kernel
