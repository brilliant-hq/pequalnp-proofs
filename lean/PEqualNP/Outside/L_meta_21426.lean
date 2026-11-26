import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21426 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245566 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨(⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [2, 16]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [3, 17]⟩, ⟨.and, [13, 19]⟩, ⟨.or, [18, 20]⟩], 21⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
