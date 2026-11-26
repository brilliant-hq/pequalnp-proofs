import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23892
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [7, 10]⟩], 11⟩

theorem shape : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25374 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23892

theorem PEqualNP.Outside.L_meta_23892 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25374 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23892.circ, PEqualNP.Outside.L_meta_23892.shape, by decide, PEqualNP.Outside.L_meta_23892.right⟩
