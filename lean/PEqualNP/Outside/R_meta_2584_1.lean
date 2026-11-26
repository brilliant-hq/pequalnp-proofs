import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2584_1
    (normalize : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧
          z (Fin.natAdd P l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
        (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧
            y (Fin.natAdd P l) = true)) ∧
        D.size ≤ C.size ∧
        ∀ k < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          ¬ PEqualNP.CleanedNonEdge.OrReaches (P + L) D D.output k →
          ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, P + L ≤ w →
            ¬ ∀ y : Fin (P + L) → Bool, PEqualNP.EdgeOwnership.gateVal (P + L) D (w - (P + L)) y = true →
              ∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)
    (blocks : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧
          z (Fin.natAdd P l) = true)) →
      (∀ k < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          ¬ PEqualNP.CleanedNonEdge.OrReaches (P + L) C C.output k →
          ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, P + L ≤ w →
            ¬ ∀ y : Fin (P + L) → Bool, PEqualNP.EdgeOwnership.gateVal (P + L) C (w - (P + L)) y = true →
              ∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
        (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧
            y (Fin.natAdd P l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2) :
    (∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2) := by
  intro P L I _ C hfree hao hfun
  obtain ⟨C', hao', hfun', hsize', hform'⟩ := normalize P L I C hao hfun
  obtain ⟨D, haoD, hfunD, hsizeD, hreadD⟩ := blocks P L I C' hfree hao' hfun' hform'
  exact ⟨D, haoD, hfunD, hsizeD.trans hsize', hreadD⟩
