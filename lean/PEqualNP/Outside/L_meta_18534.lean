import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18534

open PEqualNP.CircuitLowerBounds

def cycle : Circuit :=
  ⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [10, 15]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.and, [12, 17]⟩,
    ⟨.and, [14, 13]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [20, 19]⟩
  ], 21⟩

theorem computes : PEqualNP.Represents.Represents
    (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) cycle := by
  decide +kernel

end PEqualNP.Outside.L_meta_18534

theorem PEqualNP.Outside.L_meta_18534 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_18534.cycle, ?_, ?_, PEqualNP.Outside.L_meta_18534.computes⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_18534.cycle, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
