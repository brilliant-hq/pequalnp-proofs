import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19041 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4990 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.and, [3, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [4, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [9, 15]⟩], 16⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
