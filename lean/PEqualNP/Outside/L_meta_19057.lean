import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19057 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4973 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [11, 14]⟩], 15⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
