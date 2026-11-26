import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20648 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (13729792 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨(⟨[⟨.or, [5, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
