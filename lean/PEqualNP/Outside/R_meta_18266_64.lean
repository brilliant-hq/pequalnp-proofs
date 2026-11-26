import PEqualNP.Defs

-- A case split on the size of the circuit: either it has fewer than 18 gates, or exactly 18
-- (the step already bounds the size by 18, so the second piece is the circuits of the top size).
-- Each piece is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_18266_64
    (small : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size < (18 : ℕ) → PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x1.size ≤ (18 : ℕ) → have x4 : ℕ → Bool := fun (x4 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x4.testBit ↑x5; (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x4 x5 = Bool.true) → ∃ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x4 x6 = Bool.true)
    (top : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (18 : ℕ) ≤ x1.size → PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x1.size ≤ (18 : ℕ) → have x4 : ℕ → Bool := fun (x4 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x4.testBit ↑x5; (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x4 x5 = Bool.true) → ∃ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x4 x6 = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x1.size ≤ (18 : ℕ) → have x4 : ℕ → Bool := fun (x4 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x4.testBit ↑x5; (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x4 x5 = Bool.true) → ∃ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x4 x6 = Bool.true := by
  intro x1
  rcases Nat.lt_or_ge (x1.size) ((18 : ℕ)) with h | h
  · exact small x1 h
  · exact top x1 h
