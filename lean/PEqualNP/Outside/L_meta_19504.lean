import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19504 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [5, 4]⟩, ⟨.not, [10]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [18, 17]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
