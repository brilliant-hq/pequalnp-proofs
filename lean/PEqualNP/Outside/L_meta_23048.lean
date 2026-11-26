import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23048
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [7, 13]⟩], 14⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23048

theorem PEqualNP.Outside.L_meta_23048 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23048.circ, PEqualNP.Outside.L_meta_23048.shape, by decide, PEqualNP.Outside.L_meta_23048.right⟩
