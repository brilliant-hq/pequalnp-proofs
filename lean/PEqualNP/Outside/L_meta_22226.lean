import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_22226 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849775 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [4, 20]⟩], 21⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
