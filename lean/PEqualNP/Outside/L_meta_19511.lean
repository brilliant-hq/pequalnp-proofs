import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19511 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236691 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.or, [9, 1]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [2, 16]⟩, ⟨.not, [17]⟩, ⟨.or, [13, 18]⟩], 19⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
