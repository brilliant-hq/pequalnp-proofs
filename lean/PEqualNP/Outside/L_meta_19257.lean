import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19257

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 11]⟩], 12⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (895 : ℕ).testBit (4 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_19257

theorem PEqualNP.Outside.L_meta_19257 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (895 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19257.C0, PEqualNP.Outside.L_meta_19257.fan, by decide, PEqualNP.Outside.L_meta_19257.rep⟩
