import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19596 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [14]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [13, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
