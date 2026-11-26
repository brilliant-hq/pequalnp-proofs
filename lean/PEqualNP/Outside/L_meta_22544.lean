import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22544 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940213 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [2, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 0]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [21, 15]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
