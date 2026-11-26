import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19298 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237180 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [0, 9]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [6, 14]⟩,
    ⟨.and, [11, 15]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [17, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
