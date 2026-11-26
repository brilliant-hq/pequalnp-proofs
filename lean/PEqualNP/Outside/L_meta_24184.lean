import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_24184 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (553817 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.and, [0, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [6, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
