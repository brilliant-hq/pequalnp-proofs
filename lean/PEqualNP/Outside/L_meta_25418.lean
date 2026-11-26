import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25418

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [5, 5]⟩,
    ⟨GateOp.or, [1, 0]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.not, [2, 2]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.not, [11, 11]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.and, [13, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25418

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25418 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25418.circuit, PEqualNP.Outside.L_meta_25418.shape, by decide, by decide +kernel⟩
