import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22369 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841582 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [14, 13]⟩, ⟨.and, [9, 0]⟩, ⟨.and, [12, 8]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
