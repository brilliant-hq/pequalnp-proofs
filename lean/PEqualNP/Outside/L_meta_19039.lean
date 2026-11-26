import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19039 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4732 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.not, [7]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
