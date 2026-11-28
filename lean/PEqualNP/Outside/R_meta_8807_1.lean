import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8807_1
    (hGalois :
      ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (X Y : Finset (Fin n)),
        PEqualNP.GenericRejection.IsFalseInput S X Y ↔ X ⊆ PEqualNP.GenericRejection.zeroSet S Y)
    (hZero :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (300 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x4.output < x2 + x2 + x4.size →
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
        (∀ (x12 : Finset (Fin x2)),
          x12.card ≤ x1 →
          x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x12) x12) = Bool.false) →
        (∃ x13 < x4.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∃ (x14 : Finset (Fin x2)),
            (100 : ℕ) < x14.card ∧
            have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};
            Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (300 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →
      (∃ x13 < x4.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ (x14 : Finset (Fin x2)),
          (100 : ℕ) < x14.card ∧
          have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};
          Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact hZero x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7
    (fun x12 hx12 => h8 (PEqualNP.GenericRejection.zeroSet x3 x12) x12 hx12 ((hGalois x2 x3 (PEqualNP.GenericRejection.zeroSet x3 x12) x12).mpr Finset.Subset.rfl))
    h9
