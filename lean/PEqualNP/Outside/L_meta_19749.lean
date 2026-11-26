import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19749

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [10, 12]⟩,
     ⟨.or, [9, 11]⟩,
     ⟨.or, [17, 14]⟩,
     ⟨.or, [16, 18]⟩,
     ⟨.and, [0, 19]⟩,
     ⟨.or, [8, 13]⟩,
     ⟨.or, [12, 21]⟩,
     ⟨.or, [14, 15]⟩,
     ⟨.or, [22, 23]⟩,
     ⟨.and, [1, 24]⟩,
     ⟨.or, [8, 16]⟩,
     ⟨.or, [26, 15]⟩,
     ⟨.or, [9, 27]⟩,
     ⟨.and, [2, 28]⟩,
     ⟨.or, [11, 13]⟩,
     ⟨.or, [10, 30]⟩,
     ⟨.or, [31, 18]⟩,
     ⟨.and, [3, 32]⟩,
     ⟨.or, [17, 22]⟩,
     ⟨.and, [4, 34]⟩,
     ⟨.or, [11, 27]⟩,
     ⟨.and, [5, 36]⟩,
     ⟨.or, [9, 21]⟩,
     ⟨.or, [38, 23]⟩,
     ⟨.and, [6, 39]⟩,
     ⟨.or, [31, 23]⟩,
     ⟨.and, [7, 41]⟩,
     ⟨.or, [20, 25]⟩,
     ⟨.or, [43, 29]⟩,
     ⟨.or, [44, 33]⟩,
     ⟨.or, [45, 35]⟩,
     ⟨.or, [46, 37]⟩,
     ⟨.or, [47, 40]⟩,
     ⟨.or, [48, 42]⟩], 49⟩

end PEqualNP.Outside.L_meta_19749

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_19749 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨PEqualNP.Outside.L_meta_19749.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_19749.circuit]
  · decide +kernel
