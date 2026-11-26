import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22669 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841649 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [8, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [18, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
