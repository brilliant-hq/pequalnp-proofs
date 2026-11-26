import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23037
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23037

theorem PEqualNP.Outside.L_meta_23037 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23037.circ, PEqualNP.Outside.L_meta_23037.shape, by decide, PEqualNP.Outside.L_meta_23037.right⟩
