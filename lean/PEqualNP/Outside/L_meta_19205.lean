import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19205
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[2, 7]⟩,
  ⟨.or,[4, 8]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[3, 10]⟩,
  ⟨.not,[3]⟩,
  ⟨.or,[4, 12]⟩,
  ⟨.and,[11, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_19205

theorem PEqualNP.Outside.L_meta_19205 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5870 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19205.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19205.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
