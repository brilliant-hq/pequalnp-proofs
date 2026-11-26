import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22820
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [7, 9]⟩], 10⟩

theorem shape : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116639 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by decide +kernel

end PEqualNP.Outside.L_meta_22820

theorem PEqualNP.Outside.L_meta_22820 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116639 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22820.circ, PEqualNP.Outside.L_meta_22820.shape, by decide, PEqualNP.Outside.L_meta_22820.right⟩
