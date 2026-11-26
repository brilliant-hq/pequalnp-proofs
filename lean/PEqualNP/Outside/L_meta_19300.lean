import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19300 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16240236 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.not, [16]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [11, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
