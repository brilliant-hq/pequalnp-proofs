import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24975 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [5]⟩,
    ⟨.or, [3, 2]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [8, 1]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [12, 0]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
