import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23717 : Circuit := ⟨[
  ⟨.or, [3, 4]⟩,
  ⟨.and, [0, 5]⟩,
  ⟨.or, [0, 5]⟩,
  ⟨.not, [7]⟩,
  ⟨.and, [1, 8]⟩,
  ⟨.or, [6, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_23717 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (216 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23717, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23717, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

