import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20649 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15761408 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨(⟨[⟨.and, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
