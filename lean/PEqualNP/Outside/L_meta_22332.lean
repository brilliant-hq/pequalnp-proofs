import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22332 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841132 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.and, [0, 9]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [14, 0]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [21, 18]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
