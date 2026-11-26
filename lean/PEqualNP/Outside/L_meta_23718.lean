import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23718 : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [5, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_23718 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (221 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23718, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23718, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

