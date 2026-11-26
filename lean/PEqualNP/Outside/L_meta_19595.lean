import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19595 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16240236 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [11, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
