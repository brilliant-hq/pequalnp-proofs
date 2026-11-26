import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23854

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.not, [3, 3]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.not, [7, 7]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.and, [8, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23854

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23854 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4439 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23854.circuit, PEqualNP.Outside.L_meta_23854.shape, by decide, by decide +kernel⟩
