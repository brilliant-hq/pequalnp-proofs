import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20692 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15795200 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  let C : Circuit := ⟨[⟨.or, [2, 4]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [4, 14]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [15, 16]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
