import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7750_733
    (a1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 →
      x1.size ≤ (123 : ℕ) →
      x1.output < 42 →
      ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true))
    (a2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 →
      x1.size ≤ (123 : ℕ) →
      42 ≤ x1.output →
      ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 →
      x1.size ≤ (123 : ℕ) →
      ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) := by
  intro x1 h1 h2
  by_cases h : x1.output < 42
  · exact a1 x1 h1 h2 h
  · exact a2 x1 h1 h2 (Nat.le_of_not_lt h)
