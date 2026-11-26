import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19251_aux

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [0]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [17, 18]⟩], 19⟩

theorem witnessFit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19251_aux

open PEqualNP.Outside.L_meta_19251_aux in
theorem PEqualNP.Outside.L_meta_19251 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
