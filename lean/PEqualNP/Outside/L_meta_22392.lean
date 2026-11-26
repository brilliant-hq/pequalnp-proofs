import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22392 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849716 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [3, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [17, 16]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
