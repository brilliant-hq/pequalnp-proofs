import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19212
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.and,[0, 5]⟩,
  ⟨.or,[3, 8]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[4, 5]⟩,
  ⟨.or,[0, 11]⟩,
  ⟨.and,[10, 12]⟩
], 13⟩

end PEqualNP.Outside.L_meta_19212

theorem PEqualNP.Outside.L_meta_19212 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19212.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19212.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
