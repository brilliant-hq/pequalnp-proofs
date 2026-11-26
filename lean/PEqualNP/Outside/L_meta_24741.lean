import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24741_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.and, [7, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24741_aux

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_24741 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100138 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24741_aux.circuit, PEqualNP.Outside.L_meta_24741_aux.shape, by decide, by decide +kernel⟩
