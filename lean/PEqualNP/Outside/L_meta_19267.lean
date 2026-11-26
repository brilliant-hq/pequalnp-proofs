import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19267 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [7]⟩, ⟨.and, [9, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
