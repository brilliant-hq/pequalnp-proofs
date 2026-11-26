import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23217 : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [4, 8]⟩,
  ⟨.and, [9, 10]⟩], 11⟩

theorem PEqualNP.Outside.L_meta_23217 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34588 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23217, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23217, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

