import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23200 : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [6, 9]⟩,
  ⟨.or, [7, 10]⟩], 11⟩

theorem PEqualNP.Outside.L_meta_23200 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33679 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23200, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23200, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

