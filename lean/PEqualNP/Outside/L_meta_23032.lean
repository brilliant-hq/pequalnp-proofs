import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_23032 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [10, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
