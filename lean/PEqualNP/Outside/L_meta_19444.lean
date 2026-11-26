import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19444
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[5, 8]⟩,
  ⟨.or,[5, 9]⟩,
  ⟨.and,[1, 11]⟩,
  ⟨.or,[0, 10]⟩,
  ⟨.or,[6, 13]⟩,
  ⟨.and,[0, 10]⟩,
  ⟨.or,[1, 15]⟩,
  ⟨.not,[16]⟩,
  ⟨.and,[14, 17]⟩,
  ⟨.or,[12, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19444

theorem PEqualNP.Outside.L_meta_19444 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11906614 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19444.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19444.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
