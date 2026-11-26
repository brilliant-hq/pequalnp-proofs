import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23719 : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.and, [8, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_23719 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (414 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23719, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23719, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

