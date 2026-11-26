import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24141_aux

def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [0, 1]⟩,
  ⟨.not, [6]⟩,
  ⟨.and, [5, 7]⟩,
  ⟨.and, [2, 4]⟩,
  ⟨.or, [2, 4]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [3, 11]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.or, [12, 13]⟩
], 14⟩

end PEqualNP.Outside.L_meta_24141_aux

theorem PEqualNP.Outside.L_meta_24141 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279517 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24141_aux.circuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24141_aux.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
