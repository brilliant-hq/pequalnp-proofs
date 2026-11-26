import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24989_aux

def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.and, [3, 6]⟩,
  ⟨.or, [2, 1]⟩,
  ⟨.or, [3, 1]⟩,
  ⟨.and, [2, 9]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [8, 11]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.or, [0, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_24989_aux

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24989 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12799679 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24989_aux.circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24989_aux.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
