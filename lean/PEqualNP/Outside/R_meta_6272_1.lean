import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6272`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6272_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (39 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (39 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (39 : ℕ) ≤ x1.size) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
