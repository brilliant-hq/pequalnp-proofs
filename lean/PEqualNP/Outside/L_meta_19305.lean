import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19305
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[1, 9]⟩,
  ⟨.and,[0, 5]⟩,
  ⟨.not,[11]⟩,
  ⟨.not,[1]⟩,
  ⟨.and,[6, 13]⟩,
  ⟨.or,[5, 14]⟩,
  ⟨.or,[0, 15]⟩,
  ⟨.and,[12, 16]⟩,
  ⟨.or,[10, 17]⟩
], 18⟩

end PEqualNP.Outside.L_meta_19305

theorem PEqualNP.Outside.L_meta_19305 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247678 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19305.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19305.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
