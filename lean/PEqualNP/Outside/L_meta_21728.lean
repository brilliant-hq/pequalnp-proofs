import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21728_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [11, 14]⟩], 15⟩
theorem basis : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (4441 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel
end PEqualNP.Outside.L_meta_21728_aux

theorem PEqualNP.Outside.L_meta_21728 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4441 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21728_aux.circ, PEqualNP.Outside.L_meta_21728_aux.basis, by decide, PEqualNP.Outside.L_meta_21728_aux.right⟩
