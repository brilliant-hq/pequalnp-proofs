import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22991
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_22991

theorem PEqualNP.Outside.L_meta_22991 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22991.circ, PEqualNP.Outside.L_meta_22991.shape, by decide, PEqualNP.Outside.L_meta_22991.right⟩
