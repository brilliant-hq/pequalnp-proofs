import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19202
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[1, 5]⟩,
  ⟨.or,[3, 8]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[4, 10]⟩,
  ⟨.not,[2]⟩,
  ⟨.or,[5, 12]⟩,
  ⟨.and,[11, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_19202

theorem PEqualNP.Outside.L_meta_19202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4831 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19202.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19202.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
