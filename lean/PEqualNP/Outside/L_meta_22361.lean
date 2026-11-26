import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22361 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841518 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [3, 7]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [12, 1]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [8, 1]⟩, ⟨.and, [17, 11]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [18, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
