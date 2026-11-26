import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23045
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [0, 12]⟩], 13⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23045

theorem PEqualNP.Outside.L_meta_23045 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23045.circ, PEqualNP.Outside.L_meta_23045.shape, by decide, PEqualNP.Outside.L_meta_23045.right⟩
