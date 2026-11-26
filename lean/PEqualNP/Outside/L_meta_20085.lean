import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20085
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [13, 15]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [16, 23]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [20, 23]⟩, ⟨.and, [0, 30]⟩, ⟨.and, [1, 24]⟩, ⟨.and, [2, 27]⟩, ⟨.and, [3, 29]⟩, ⟨.and, [4, 25]⟩, ⟨.and, [5, 28]⟩, ⟨.and, [6, 26]⟩, ⟨.and, [7, 31]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

end PEqualNP.Outside.L_meta_20085

open PEqualNP.Outside.L_meta_20085 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20085 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6650604754610151990 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
