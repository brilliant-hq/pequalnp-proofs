import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23030
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23030

theorem PEqualNP.Outside.L_meta_23030 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23030.circ, PEqualNP.Outside.L_meta_23030.shape, by decide, PEqualNP.Outside.L_meta_23030.right⟩
