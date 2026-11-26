import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22365 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841524 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [1, 16]⟩, ⟨.and, [15, 14]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [2, 20]⟩, ⟨.or, [19, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
