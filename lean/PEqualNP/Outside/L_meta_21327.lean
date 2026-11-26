import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21327 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105852 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [3, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 15]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
