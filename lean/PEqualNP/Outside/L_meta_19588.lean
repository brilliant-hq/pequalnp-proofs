import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19588 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223379 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨(⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.not, [17]⟩], 18⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
