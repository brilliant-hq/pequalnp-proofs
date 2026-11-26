import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_18534_aux

def cycle : Circuit := ⟨[
  ⟨.or, [0, 5]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.or, [2, 7]⟩,
  ⟨.or, [3, 8]⟩,
  ⟨.or, [4, 9]⟩,
  ⟨.or, [11, 14]⟩,
  ⟨.and, [10, 15]⟩,
  ⟨.or, [11, 13]⟩,
  ⟨.and, [12, 17]⟩,
  ⟨.and, [13, 14]⟩,
  ⟨.or, [16, 18]⟩,
  ⟨.or, [20, 19]⟩], 21⟩

end PEqualNP.Outside.L_meta_18534_aux

open PEqualNP.Outside.L_meta_18534_aux in
theorem PEqualNP.Outside.L_meta_18534 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) 12 := by
  refine ⟨cycle, ?_, by decide, ?_⟩
  · intro gate hg
    simp [cycle] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · decide +kernel
