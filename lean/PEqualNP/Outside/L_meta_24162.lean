import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24162

open PEqualNP.CircuitLowerBounds

def circ : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [9, 8]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24162

theorem PEqualNP.Outside.L_meta_24162 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266910 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24162.circ, PEqualNP.Outside.L_meta_24162.shape, by decide, by decide +kernel⟩
