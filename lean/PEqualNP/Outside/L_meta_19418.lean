import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19418
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[0]⟩,
  ⟨.or,[0, 1]⟩,
  ⟨.and,[9, 11]⟩,
  ⟨.or,[6, 10]⟩,
  ⟨.or,[1, 9]⟩,
  ⟨.not,[14]⟩,
  ⟨.or,[5, 15]⟩,
  ⟨.and,[13, 16]⟩,
  ⟨.or,[12, 17]⟩
], 18⟩

end PEqualNP.Outside.L_meta_19418

theorem PEqualNP.Outside.L_meta_19418 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236082 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19418.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19418.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
