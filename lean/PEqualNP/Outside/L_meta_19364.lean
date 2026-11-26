import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19364
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[0, 6]⟩,
  ⟨.or,[1, 5]⟩,
  ⟨.or,[7, 10]⟩,
  ⟨.and,[11, 12]⟩,
  ⟨.not,[13]⟩,
  ⟨.or,[5, 12]⟩,
  ⟨.and,[14, 15]⟩
], 16⟩

end PEqualNP.Outside.L_meta_19364

theorem PEqualNP.Outside.L_meta_19364 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19364.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19364.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
