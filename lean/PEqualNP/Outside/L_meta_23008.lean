import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23008
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [10, 11]⟩], 12⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36668 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23008

theorem PEqualNP.Outside.L_meta_23008 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36668 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23008.circ, PEqualNP.Outside.L_meta_23008.shape, by decide, PEqualNP.Outside.L_meta_23008.right⟩
