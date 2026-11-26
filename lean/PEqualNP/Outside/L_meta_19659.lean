import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19659 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15767761 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [11, 0]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [10, 4]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
