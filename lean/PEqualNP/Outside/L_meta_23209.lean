import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23209 : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [1, 3]⟩,
  ⟨.and, [4, 6]⟩,
  ⟨.and, [7, 8]⟩,
  ⟨.or, [9, 10]⟩], 11⟩

theorem PEqualNP.Outside.L_meta_23209 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23209, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23209, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

