import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23405
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [6, 2]⟩,
  ⟨.and, [6, 2]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [7, 9]⟩], 10⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23405

open PEqualNP.Outside.L_meta_23405 in
theorem PEqualNP.Outside.L_meta_23405 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (249531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
