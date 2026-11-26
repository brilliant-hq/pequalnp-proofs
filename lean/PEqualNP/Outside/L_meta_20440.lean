import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20440_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.and, [4, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [12, 16]⟩], 17⟩
theorem fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun u v : Fin 5 => (16269874 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_20440_aux

theorem PEqualNP.Outside.L_meta_20440 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269874 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_20440_aux.circ, PEqualNP.Outside.L_meta_20440_aux.fan, by decide, PEqualNP.Outside.L_meta_20440_aux.rep⟩
