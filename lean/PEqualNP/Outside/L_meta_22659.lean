import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22659 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841148 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [3, 6]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [17, 16]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [18, 14]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [22, 21]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
