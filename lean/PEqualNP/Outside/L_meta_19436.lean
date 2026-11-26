import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19436
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[0, 1]⟩,
  ⟨.and,[3, 7]⟩,
  ⟨.or,[2, 4]⟩,
  ⟨.and,[6, 12]⟩,
  ⟨.or,[5, 10]⟩,
  ⟨.or,[2, 6]⟩,
  ⟨.not,[15]⟩,
  ⟨.and,[14, 16]⟩,
  ⟨.or,[13, 17]⟩,
  ⟨.or,[11, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19436

theorem PEqualNP.Outside.L_meta_19436 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3312573 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19436.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19436.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
