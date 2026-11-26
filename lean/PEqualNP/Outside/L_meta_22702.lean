import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22702 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903022 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [5, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [15, 13]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [2, 19]⟩, ⟨.and, [12, 16]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
