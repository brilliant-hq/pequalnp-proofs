import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20565 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16254033 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [1, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [11]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [10, 15]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [16, 17]⟩], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
