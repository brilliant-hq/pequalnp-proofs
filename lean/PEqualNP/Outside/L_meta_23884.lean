import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23884
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [7, 10]⟩], 11⟩

theorem shape : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12623 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23884

theorem PEqualNP.Outside.L_meta_23884 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12623 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23884.circ, PEqualNP.Outside.L_meta_23884.shape, by decide, PEqualNP.Outside.L_meta_23884.right⟩
