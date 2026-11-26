import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24749_aux

def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.not, [5]⟩,
  ⟨.and, [1, 6]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [5, 2]⟩,
  ⟨.and, [0, 9]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [3, 11]⟩,
  ⟨.and, [8, 12]⟩,
  ⟨.or, [7, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_24749_aux

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24749 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100286 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24749_aux.circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24749_aux.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
