import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19692 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11911377 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [5]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [0, 10]⟩,
      ⟨.or, [11, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [6, 14]⟩, ⟨.not, [15]⟩,
      ⟨.and, [12, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
