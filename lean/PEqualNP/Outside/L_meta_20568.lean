import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20568_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20568_aux

theorem PEqualNP.Outside.L_meta_20568 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3677463 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_20568_aux.circuit, PEqualNP.Outside.L_meta_20568_aux.fan, by decide, by decide +kernel⟩
