import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23725 : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.and, [0, 3]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.not, [7]⟩,
  ⟨.and, [5, 8]⟩,
  ⟨.or, [6, 9]⟩], 10⟩

theorem PEqualNP.Outside.L_meta_23725 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4302 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨circuit23725, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23725, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

