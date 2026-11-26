import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20104_aux

def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [10, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [12, 23]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [10, 22]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [8, 24]⟩, ⟨.or, [14, 27]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [11, 22]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [3, 31]⟩, ⟨.and, [1, 30]⟩, ⟨.and, [7, 33]⟩, ⟨.and, [5, 25]⟩, ⟨.and, [0, 26]⟩, ⟨.and, [2, 32]⟩, ⟨.and, [6, 29]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩, ⟨.or, [46, 40]⟩, ⟨.or, [47, 41]⟩], 48⟩

end PEqualNP.Outside.L_meta_20104_aux

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_meta_20104 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11442406341415304295 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨PEqualNP.Outside.L_meta_20104_aux.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20104_aux.circuit]
  · decide +kernel
