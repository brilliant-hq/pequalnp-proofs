import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [8, 11]⟩], 12⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99870 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23009

theorem PEqualNP.Outside.L_meta_23009 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99870 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23009.circ, PEqualNP.Outside.L_meta_23009.shape, by decide, PEqualNP.Outside.L_meta_23009.right⟩
