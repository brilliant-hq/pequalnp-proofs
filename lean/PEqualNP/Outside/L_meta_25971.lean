import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25971 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 11, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [8, 9]⟩,
      ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩], 12⟩, ?_, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff]
