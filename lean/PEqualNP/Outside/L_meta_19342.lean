import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19342 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235582 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.not, [10]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.not, [15]⟩
  ], 16⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    dsimp only [C]
    decide +kernel
