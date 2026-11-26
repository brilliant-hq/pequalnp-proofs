import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20122
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [13, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [0, 21]⟩, ⟨.and, [1, 26]⟩, ⟨.and, [2, 24]⟩, ⟨.and, [3, 25]⟩, ⟨.and, [4, 28]⟩, ⟨.and, [5, 23]⟩, ⟨.and, [6, 27]⟩, ⟨.and, [7, 22]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [37, 31]⟩, ⟨.or, [38, 32]⟩, ⟨.or, [39, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩], 43⟩

end PEqualNP.Outside.L_meta_20122

open PEqualNP.Outside.L_meta_20122 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20122 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
