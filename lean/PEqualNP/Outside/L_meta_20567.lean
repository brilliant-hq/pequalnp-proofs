import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20567_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [15]⟩, ⟨.and, [16, 17]⟩], 18⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20567_aux

theorem PEqualNP.Outside.L_meta_20567 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16254518 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_20567_aux.circuit, PEqualNP.Outside.L_meta_20567_aux.fan, by decide, by decide +kernel⟩
