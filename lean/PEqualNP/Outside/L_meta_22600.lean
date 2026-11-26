import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_22600 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965627 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 15]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [21, 16]⟩], 22⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
