import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19363
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[1, 5]⟩,
  ⟨.or,[0, 6]⟩,
  ⟨.or,[7, 11]⟩,
  ⟨.and,[10, 12]⟩,
  ⟨.or,[10, 11]⟩,
  ⟨.not,[13]⟩,
  ⟨.and,[14, 15]⟩
], 16⟩

end PEqualNP.Outside.L_meta_19363

theorem PEqualNP.Outside.L_meta_19363 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19363.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19363.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
