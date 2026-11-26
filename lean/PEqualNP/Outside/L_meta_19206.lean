import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19206
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[2, 7]⟩,
  ⟨.or,[4, 8]⟩,
  ⟨.or,[3, 9]⟩,
  ⟨.not,[10]⟩,
  ⟨.and,[3, 4]⟩,
  ⟨.or,[11, 12]⟩,
  ⟨.or,[0, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_19206

theorem PEqualNP.Outside.L_meta_19206 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5871 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19206.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19206.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
