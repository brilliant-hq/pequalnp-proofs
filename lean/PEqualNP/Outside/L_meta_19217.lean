import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19217
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[1, 4]⟩,
  ⟨.or,[1, 4]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[8, 10]⟩,
  ⟨.not,[11]⟩,
  ⟨.or,[0, 12]⟩
], 13⟩

end PEqualNP.Outside.L_meta_19217

theorem PEqualNP.Outside.L_meta_19217 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19217.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19217.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
