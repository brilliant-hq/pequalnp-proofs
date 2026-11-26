import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19249_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [11]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.not, [16]⟩], 17⟩

end PEqualNP.Outside.L_meta_19249_aux

theorem PEqualNP.Outside.L_meta_19249 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19249_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19249_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
