import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18475_307
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (30 : ℕ) → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (32 : ℕ)) (x6 : Fin (32 : ℕ)), (↑x5 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x6 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x5 (0 : ℕ)).testBit (↑x6 - (16 : ℕ)) = Bool.true) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → (79 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (30 : ℕ) < x1.size → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (32 : ℕ)) (x6 : Fin (32 : ℕ)), (↑x5 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x6 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x5 (0 : ℕ)).testBit (↑x6 - (16 : ℕ)) = Bool.true) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → (79 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (32 : ℕ)) (x6 : Fin (32 : ℕ)), (↑x5 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x6 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x5 (0 : ℕ)).testBit (↑x6 - (16 : ℕ)) = Bool.true) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → (79 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : x1.size ≤ (30 : ℕ)
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> first | assumption | omega
