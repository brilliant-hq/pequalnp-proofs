import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19038 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4731 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
