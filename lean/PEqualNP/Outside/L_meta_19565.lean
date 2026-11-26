import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19565 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894510 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.not, [5]⟩, ⟨.and, [1, 10]⟩, ⟨.not, [0]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 15]⟩, ⟨.not, [17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
