import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23034
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [9, 12]⟩], 13⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100152 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23034

theorem PEqualNP.Outside.L_meta_23034 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100152 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23034.circ, PEqualNP.Outside.L_meta_23034.shape, by decide, PEqualNP.Outside.L_meta_23034.right⟩
