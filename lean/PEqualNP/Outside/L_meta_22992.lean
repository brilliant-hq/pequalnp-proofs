import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22992
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1822 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_22992

theorem PEqualNP.Outside.L_meta_22992 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1822 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22992.circ, PEqualNP.Outside.L_meta_22992.shape, by decide, PEqualNP.Outside.L_meta_22992.right⟩
