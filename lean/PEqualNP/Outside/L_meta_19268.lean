import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19268 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
