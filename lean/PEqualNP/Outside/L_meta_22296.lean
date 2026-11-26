import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22296 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838901 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [6, 1]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [14, 7]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [14, 1]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [19, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
