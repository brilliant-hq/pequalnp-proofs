import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19281 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [4, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
