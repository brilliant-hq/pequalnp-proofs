import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17591`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17591_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (26 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (26 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (26 : ℕ) ≤ x1.size) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption

-- reduction for L-meta-17591; re-checked against the current base.
