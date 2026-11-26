import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19307
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[0, 5]⟩,
  ⟨.not,[10]⟩,
  ⟨.or,[3, 4]⟩,
  ⟨.or,[6, 7]⟩,
  ⟨.and,[12, 13]⟩,
  ⟨.or,[5, 14]⟩,
  ⟨.or,[0, 15]⟩,
  ⟨.and,[11, 16]⟩
], 17⟩

end PEqualNP.Outside.L_meta_19307

theorem PEqualNP.Outside.L_meta_19307 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570494 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19307.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19307.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
