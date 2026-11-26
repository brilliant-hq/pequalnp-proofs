import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22362 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841521 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [4, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [14, 9]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [21, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
