import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22671 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841652 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [1, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [12, 0]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [15, 14]⟩, ⟨.and, [16, 10]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [20, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
