import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19424
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[0]⟩,
  ⟨.and,[0, 8]⟩,
  ⟨.or,[7, 10]⟩,
  ⟨.or,[1, 2]⟩,
  ⟨.or,[7, 9]⟩,
  ⟨.and,[13, 14]⟩,
  ⟨.or,[8, 15]⟩,
  ⟨.not,[16]⟩,
  ⟨.and,[12, 17]⟩,
  ⟨.or,[11, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19424

theorem PEqualNP.Outside.L_meta_19424 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19424.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19424.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
