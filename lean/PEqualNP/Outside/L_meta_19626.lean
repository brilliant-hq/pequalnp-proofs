import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19626_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [4, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 13]⟩, ⟨.not, [15]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_19626_aux

theorem PEqualNP.Outside.L_meta_19626 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7711899 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19626_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19626_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
