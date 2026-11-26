import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19439
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not,[5]⟩,
  ⟨.or,[5, 6]⟩,
  ⟨.and,[4, 11]⟩,
  ⟨.or,[1, 10]⟩,
  ⟨.or,[7, 4]⟩,
  ⟨.or,[6, 14]⟩,
  ⟨.not,[15]⟩,
  ⟨.or,[0, 16]⟩,
  ⟨.and,[13, 17]⟩,
  ⟨.or,[12, 18]⟩
], 19⟩

end PEqualNP.Outside.L_meta_19439

theorem PEqualNP.Outside.L_meta_19439 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3957566 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19439.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19439.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
