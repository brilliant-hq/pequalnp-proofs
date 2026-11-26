import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22481

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22481

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22481 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22481.circuit, PEqualNP.Outside.L_meta_22481.shape, by decide, by decide +kernel⟩
