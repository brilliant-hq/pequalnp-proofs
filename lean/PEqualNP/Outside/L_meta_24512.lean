import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_24512 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147775 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
