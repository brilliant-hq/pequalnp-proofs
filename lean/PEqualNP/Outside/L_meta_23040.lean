import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23040
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233018 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_23040

theorem PEqualNP.Outside.L_meta_23040 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233018 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23040.circ, PEqualNP.Outside.L_meta_23040.shape, by decide, PEqualNP.Outside.L_meta_23040.right⟩
