import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25977 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 7, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [8, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [9, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> cases h <;> simp
