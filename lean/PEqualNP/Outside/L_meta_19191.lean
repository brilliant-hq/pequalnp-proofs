import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19191
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[1, 2]⟩,
  ⟨.and,[1, 5]⟩,
  ⟨.or,[4, 9]⟩,
  ⟨.and,[8, 10]⟩,
  ⟨.not,[4]⟩,
  ⟨.and,[0, 12]⟩,
  ⟨.or,[11, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_19191

theorem PEqualNP.Outside.L_meta_19191 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (318 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19191.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19191.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
