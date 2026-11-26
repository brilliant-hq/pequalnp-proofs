import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19425
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[8]⟩,
  ⟨.or,[6, 7]⟩,
  ⟨.and,[0, 11]⟩,
  ⟨.or,[3, 4]⟩,
  ⟨.and,[10, 13]⟩,
  ⟨.or,[8, 5]⟩,
  ⟨.or,[1, 2]⟩,
  ⟨.and,[15, 16]⟩,
  ⟨.or,[14, 17]⟩,
  ⟨.or,[12, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19425

theorem PEqualNP.Outside.L_meta_19425 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24880422 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19425.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19425.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
