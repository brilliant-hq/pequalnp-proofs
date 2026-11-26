import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20435_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [14, 15]⟩], 16⟩
theorem fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun u v : Fin 5 => (15762513 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_20435_aux

theorem PEqualNP.Outside.L_meta_20435 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762513 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_20435_aux.circ, PEqualNP.Outside.L_meta_20435_aux.fan, by decide, PEqualNP.Outside.L_meta_20435_aux.rep⟩
