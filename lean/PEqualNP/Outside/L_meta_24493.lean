import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24493

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.not, [6]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [7, 8]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.and, [3, 10]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.not, [12]⟩], 13⟩

theorem basis : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24493

theorem PEqualNP.Outside.L_meta_24493 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2117055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24493.circuit, PEqualNP.Outside.L_meta_24493.basis, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
