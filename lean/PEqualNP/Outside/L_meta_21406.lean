import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21406 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241149 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨(⟨[⟨.or, [0, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [9, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
