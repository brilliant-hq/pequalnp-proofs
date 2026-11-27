import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25965 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 13, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.not, [5]⟩, ⟨.and, [8, 9]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> cases h <;> simp
