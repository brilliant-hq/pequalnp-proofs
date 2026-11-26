import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21260 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39162 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.and, [1, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
