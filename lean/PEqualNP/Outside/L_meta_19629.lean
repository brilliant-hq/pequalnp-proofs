import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19629 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.or, [8, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.not, [16]⟩, ⟨.or, [13, 17]⟩], 18⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
