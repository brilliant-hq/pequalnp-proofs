import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23170 : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.not, [9]⟩,
  ⟨.and, [6, 10]⟩], 11⟩

theorem PEqualNP.Outside.L_meta_23170 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (415 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23170, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23170, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

