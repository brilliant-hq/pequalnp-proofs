import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19489
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[9]⟩,
  ⟨.and,[5, 4]⟩,
  ⟨.or,[0, 3]⟩,
  ⟨.and,[6, 12]⟩,
  ⟨.not,[13]⟩,
  ⟨.and,[3, 10]⟩,
  ⟨.or,[0, 15]⟩,
  ⟨.or,[6, 16]⟩,
  ⟨.and,[14, 17]⟩,
  ⟨.or,[11, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19489

theorem PEqualNP.Outside.L_meta_19489 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3573853 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19489.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19489.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
