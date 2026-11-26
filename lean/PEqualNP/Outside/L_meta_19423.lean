import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19423
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[0]⟩,
  ⟨.and,[0, 5]⟩,
  ⟨.or,[9, 10]⟩,
  ⟨.or,[4, 5]⟩,
  ⟨.or,[3, 13]⟩,
  ⟨.not,[14]⟩,
  ⟨.or,[8, 15]⟩,
  ⟨.and,[12, 16]⟩,
  ⟨.or,[11, 17]⟩,
  ⟨.not,[18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19423

theorem PEqualNP.Outside.L_meta_19423 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19423.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19423.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
