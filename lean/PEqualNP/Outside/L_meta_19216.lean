import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19216
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[0, 1]⟩,
  ⟨.and,[4, 8]⟩,
  ⟨.not,[9]⟩,
  ⟨.or,[1, 4]⟩,
  ⟨.or,[0, 11]⟩,
  ⟨.and,[10, 12]⟩
], 13⟩

end PEqualNP.Outside.L_meta_19216

theorem PEqualNP.Outside.L_meta_19216 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4590 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19216.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19216.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
