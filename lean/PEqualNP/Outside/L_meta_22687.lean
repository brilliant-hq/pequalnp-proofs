import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_22687 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843194 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [5, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [1, 14]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [22, 17]⟩], 23⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
