import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19186
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[0]⟩,
  ⟨.and,[7, 8]⟩,
  ⟨.or,[4, 9]⟩,
  ⟨.or,[3, 10]⟩,
  ⟨.not,[4]⟩,
  ⟨.or,[0, 12]⟩,
  ⟨.and,[11, 13]⟩,
  ⟨.not,[14]⟩
], 15⟩

end PEqualNP.Outside.L_meta_19186

theorem PEqualNP.Outside.L_meta_19186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6014 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19186.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19186.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
