import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19104

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [8, 9]⟩,
  ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [12]⟩], 13⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (13279 : ℕ).testBit (4 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_19104

theorem PEqualNP.Outside.L_meta_19104 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13279 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19104.C0, PEqualNP.Outside.L_meta_19104.fan, by decide, PEqualNP.Outside.L_meta_19104.rep⟩
