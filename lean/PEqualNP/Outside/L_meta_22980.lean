import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_22980 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34588 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
