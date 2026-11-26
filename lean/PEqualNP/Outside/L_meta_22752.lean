import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22752
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [3, 8]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.and, [13, 18]⟩,
    ⟨.and, [1, 17]⟩,
    ⟨.and, [16, 15]⟩,
    ⟨.or, [21, 20]⟩,
    ⟨.or, [22, 19]⟩], 23⟩

end PEqualNP.Outside.L_meta_22752

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22752 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940148 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨PEqualNP.Outside.L_meta_22752.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22752.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
