import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The last gate of the circuit is an AND gate or it is not, so the step is asked once under
-- each of the two cases and the two children together give the step by a case split.
theorem PEqualNP.Outside.R_meta_18251_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (26 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (26 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (26 : ℕ) ≤ x1.size := by
  intros x1 h1 h2 h3 h4
  by_cases hq : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact lastAnd x1 h1 h2 h3 h4 hq
  · exact lastOr x1 h1 h2 h3 h4 hq
