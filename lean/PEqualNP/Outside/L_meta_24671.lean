import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24671

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.and, [5, 9]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.not, [12]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24671

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24671 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322095 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24671.circuit, PEqualNP.Outside.L_meta_24671.shape, by decide, by decide +kernel⟩
