import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22330 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841130 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
