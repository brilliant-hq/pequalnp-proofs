import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22386 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843065 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [5, 4]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [17, 14]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [21, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
