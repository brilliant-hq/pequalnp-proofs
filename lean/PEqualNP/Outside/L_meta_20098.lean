import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20098
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [9, 24]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [12, 24]⟩, ⟨.or, [8, 25]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [10, 25]⟩, ⟨.and, [0, 27]⟩, ⟨.and, [1, 31]⟩, ⟨.and, [2, 26]⟩, ⟨.and, [3, 30]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩, ⟨.or, [46, 40]⟩, ⟨.or, [47, 41]⟩], 48⟩

end PEqualNP.Outside.L_meta_20098

open PEqualNP.Outside.L_meta_20098 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20098 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
