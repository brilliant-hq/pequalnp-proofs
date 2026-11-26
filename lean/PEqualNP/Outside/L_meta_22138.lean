import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22138
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.and, [2, 3]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.not, [9]⟩,
  ⟨.and, [7, 10]⟩,
  ⟨.or, [6, 11]⟩], 12⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22138

open PEqualNP.Outside.L_meta_22138 in
theorem PEqualNP.Outside.L_meta_22138 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33939 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
