import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22254 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816764 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : Circuit := ⟨[⟨.or, [6, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [7, 2]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [18, 10]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [16, 20]⟩, ⟨.or, [19, 21]⟩], 22⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
