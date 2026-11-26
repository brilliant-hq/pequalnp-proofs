import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19309
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[0, 9]⟩,
  ⟨.and,[1, 8]⟩,
  ⟨.not,[0]⟩,
  ⟨.and,[5, 12]⟩,
  ⟨.not,[1]⟩,
  ⟨.or,[6, 7]⟩,
  ⟨.and,[14, 15]⟩,
  ⟨.or,[13, 16]⟩,
  ⟨.or,[11, 17]⟩,
  ⟨.or,[10, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19309

theorem PEqualNP.Outside.L_meta_19309 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576886 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19309.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19309.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
