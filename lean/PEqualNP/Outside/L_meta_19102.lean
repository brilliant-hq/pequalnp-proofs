import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19102_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [2, 4]⟩, ⟨.not, [4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.not, [11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19102_aux

theorem PEqualNP.Outside.L_meta_19102 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7935 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19102_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19102_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
