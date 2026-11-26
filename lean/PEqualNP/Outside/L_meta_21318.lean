import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21318 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103902 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
