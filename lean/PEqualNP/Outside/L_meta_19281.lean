import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19281
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[2, 7]⟩,
  ⟨.or,[3, 8]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[4, 10]⟩
], 11⟩

end PEqualNP.Outside.L_meta_19281

theorem PEqualNP.Outside.L_meta_19281 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19281.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19281.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
