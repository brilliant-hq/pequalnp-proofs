import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19268
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[0, 4]⟩,
  ⟨.not,[4]⟩,
  ⟨.or,[1, 9]⟩,
  ⟨.and,[8, 10]⟩
], 11⟩

end PEqualNP.Outside.L_meta_19268

theorem PEqualNP.Outside.L_meta_19268 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19268.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19268.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
