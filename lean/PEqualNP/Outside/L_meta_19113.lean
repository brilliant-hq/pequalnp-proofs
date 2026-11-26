import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19113_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.not, [9]⟩], 10⟩

end PEqualNP.Outside.L_meta_19113_aux

theorem PEqualNP.Outside.L_meta_19113 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (16383 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19113_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19113_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp
