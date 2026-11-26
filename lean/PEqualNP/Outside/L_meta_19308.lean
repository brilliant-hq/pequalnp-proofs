import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19308
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or,[3, 4]⟩,
  ⟨.and,[7, 10]⟩,
  ⟨.or,[5, 6]⟩,
  ⟨.or,[0, 12]⟩,
  ⟨.and,[0, 12]⟩,
  ⟨.not,[14]⟩,
  ⟨.and,[13, 15]⟩,
  ⟨.or,[11, 16]⟩
], 17⟩

end PEqualNP.Outside.L_meta_19308

theorem PEqualNP.Outside.L_meta_19308 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19308.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19308.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
