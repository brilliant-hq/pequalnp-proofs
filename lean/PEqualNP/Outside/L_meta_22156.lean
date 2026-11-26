import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22156 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840636 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨(⟨[⟨.or, [8, 9]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [10, 0]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [18, 13]⟩, ⟨.and, [20, 19]⟩], 21⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
