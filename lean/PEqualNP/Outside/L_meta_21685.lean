import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21685_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [9, 11]⟩], 12⟩
theorem basis : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
    (12635 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel
end PEqualNP.Outside.L_meta_21685_aux

theorem PEqualNP.Outside.L_meta_21685 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12635 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21685_aux.circ, PEqualNP.Outside.L_meta_21685_aux.basis, by decide, PEqualNP.Outside.L_meta_21685_aux.right⟩
