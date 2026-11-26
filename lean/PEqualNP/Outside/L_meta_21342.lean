import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21342 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112117 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.and, [0, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [6, 14]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
