import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19372
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[6, 7]⟩,
  ⟨.or,[0, 10]⟩,
  ⟨.or,[1, 5]⟩,
  ⟨.or,[8, 12]⟩,
  ⟨.and,[11, 13]⟩,
  ⟨.not,[14]⟩,
  ⟨.or,[11, 12]⟩,
  ⟨.and,[15, 16]⟩
], 17⟩

end PEqualNP.Outside.L_meta_19372

theorem PEqualNP.Outside.L_meta_19372 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577398 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19372.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19372.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
