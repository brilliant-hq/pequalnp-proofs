import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21349 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112606 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
