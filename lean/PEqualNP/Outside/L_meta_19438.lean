import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19438 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3585970 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.or, [9, 4]⟩, ⟨.or, [10, 0]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [6, 11]⟩, ⟨.not, [13]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [0, 15]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [12, 18]⟩], 19⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
