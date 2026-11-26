import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19658 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762641 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.and, [0, 9]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.not, [15]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [10, 17]⟩], 18⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
