import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20548 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7373913 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 10]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [11, 17]⟩], 18⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
