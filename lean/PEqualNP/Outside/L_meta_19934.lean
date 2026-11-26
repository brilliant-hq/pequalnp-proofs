import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19934

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
     ⟨.or, [12, 14]⟩,
     ⟨.or, [10, 16]⟩,
     ⟨.and, [0, 18]⟩,
     ⟨.or, [10, 12]⟩,
     ⟨.or, [20, 13]⟩,
     ⟨.and, [1, 21]⟩,
     ⟨.or, [10, 11]⟩,
     ⟨.or, [23, 15]⟩,
     ⟨.and, [2, 24]⟩,
     ⟨.or, [15, 16]⟩,
     ⟨.and, [3, 26]⟩,
     ⟨.or, [8, 13]⟩,
     ⟨.or, [28, 14]⟩,
     ⟨.and, [4, 29]⟩,
     ⟨.or, [15, 17]⟩,
     ⟨.and, [5, 31]⟩,
     ⟨.or, [11, 17]⟩,
     ⟨.and, [6, 33]⟩,
     ⟨.or, [9, 11]⟩,
     ⟨.or, [35, 13]⟩,
     ⟨.and, [7, 36]⟩,
     ⟨.or, [19, 22]⟩,
     ⟨.or, [38, 25]⟩,
     ⟨.or, [39, 27]⟩,
     ⟨.or, [40, 30]⟩,
     ⟨.or, [41, 32]⟩,
     ⟨.or, [42, 34]⟩,
     ⟨.or, [43, 37]⟩], 44⟩

end PEqualNP.Outside.L_meta_19934

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_19934 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  refine ⟨PEqualNP.Outside.L_meta_19934.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_19934.circuit]
  · decide +kernel
