import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23180 : Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.not, [6]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.and, [0, 8]⟩,
  ⟨.or, [9, 10]⟩], 11⟩

theorem PEqualNP.Outside.L_meta_23180 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23180, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23180, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

