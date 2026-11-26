import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22295 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838775 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [8, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [6, 15]⟩, ⟨.and, [16, 14]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [20, 19]⟩, ⟨.and, [18, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
