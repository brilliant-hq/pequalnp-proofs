import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22216 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17341 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
