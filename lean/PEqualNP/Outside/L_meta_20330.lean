import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20330 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1892380200682152600 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  let C : Circuit := ⟨[⟨.or, [8, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [11, 18]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [22, 14]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [20, 9]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [14, 24]⟩, ⟨.and, [26, 7]⟩, ⟨.and, [23, 4]⟩, ⟨.or, [28, 19]⟩, ⟨.and, [33, 29]⟩, ⟨.or, [32, 34]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [35, 31]⟩, ⟨.and, [36, 30]⟩, ⟨.or, [38, 37]⟩], 39⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
