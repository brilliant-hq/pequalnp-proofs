import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20136
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [14, 15]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [9, 21]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [16, 25]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [19, 25]⟩, ⟨.and, [0, 28]⟩, ⟨.and, [1, 30]⟩, ⟨.and, [2, 31]⟩, ⟨.and, [3, 33]⟩, ⟨.and, [4, 27]⟩, ⟨.and, [5, 26]⟩, ⟨.and, [6, 32]⟩, ⟨.and, [7, 29]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩, ⟨.or, [46, 40]⟩, ⟨.or, [47, 41]⟩], 48⟩

end PEqualNP.Outside.L_meta_20136

open PEqualNP.Outside.L_meta_20136 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20136 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17022383772369540555 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
