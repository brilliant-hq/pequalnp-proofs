import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20373
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 8]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.or, [0, 17]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [4, 18]⟩,
    ⟨.or, [2, 19]⟩,
    ⟨.or, [7, 21]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.or, [0, 15]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [19, 25]⟩,
    ⟨.or, [11, 27]⟩,
    ⟨.or, [24, 29]⟩,
    ⟨.or, [7, 31]⟩,
    ⟨.or, [17, 23]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [26, 28]⟩,
    ⟨.or, [11, 34]⟩,
    ⟨.and, [30, 37]⟩,
    ⟨.and, [33, 36]⟩,
    ⟨.and, [35, 32]⟩,
    ⟨.or, [40, 39]⟩,
    ⟨.or, [41, 38]⟩], 42⟩

end PEqualNP.Outside.L_meta_20373

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20373 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨PEqualNP.Outside.L_meta_20373.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20373.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
