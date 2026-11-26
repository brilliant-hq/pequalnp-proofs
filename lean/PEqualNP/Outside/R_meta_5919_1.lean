import Mathlib
import PEqualNP.Defs

open PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5919_1
    (geometry : let base : Finset (Fin 13) := {0, 1, 3, 9}
      let S := fun (l : Fin 13) => Finset.univ.filter fun p : Fin 13 => p - l ∈ base
      let D : Fin 13 → Finset (Fin 13) := fun p => Finset.univ.filter (fun l => p ∈ S l)
      ∀ X Y : Finset (Fin 13),
        (((∃ l, X ⊂ S l) ∧ Y = missLines S X) ∨
         ((∃ p, Y ⊂ D p) ∧ X = zeroSet S Y)) ↔
        IsMaximalFalse S X Y ∧ (¬ InNoLine S X ∨ ¬ InNoPencil S Y))
    (finiteTests : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x4.card ≤ (12 : ℕ) →       x3.size + (2 : ℕ) * x4.card ≤ (64 : ℕ) →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           let x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) →             (let off := fun (P L : Finset (Fin 13)) => ∀ t ∈ x4, ¬x9 t (incidenceInput P L)
              let D : Fin 13 → Finset (Fin 13) := fun p => Finset.univ.filter (fun l => p ∈ x2 l)
              ∀ (k : Fin 13) (U : Finset (Fin 13)),
                (U ⊂ x2 k → off U (missLines x2 U)) ∧
                (U ⊂ D k → off (zeroSet x2 U) U)) →               (∃ x12 ∈ x4,                   have x13 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := {x13 ∈ PEqualNP.HeptadCover.incidences x2 | x9 x12 (PEqualNP.GenericRejection.incidenceInput {x13.1} {x13.2})};                   (5 : ℕ) ≤ x13.card ∧ ∃ x14 ∈ x13, ∃ x15 ∈ x13, x14.1 ∉ x2 x15.2 ∧ ¬x9 x12 (PEqualNP.GenericRejection.incidenceInput {x14.1} {x15.2})) →                 ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x2 x14 ∧ ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput {x13} {x14})) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x4.card ≤ (12 : ℕ) →       x3.size + (2 : ℕ) * x4.card ≤ (64 : ℕ) →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           let x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) →             (∀ (x11 x12 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x2 x11 x12 → ¬PEqualNP.GenericRejection.InNoLine x2 x11 ∨ ¬PEqualNP.GenericRejection.InNoPencil x2 x12 → ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput x11 x12)) →               (∃ x12 ∈ x4,                   have x13 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := {x13 ∈ PEqualNP.HeptadCover.incidences x2 | x9 x12 (PEqualNP.GenericRejection.incidenceInput {x13.1} {x13.2})};                   (5 : ℕ) ≤ x13.card ∧ ∃ x14 ∈ x13, ∃ x15 ∈ x13, x14.1 ∉ x2 x15.2 ∧ ¬x9 x12 (PEqualNP.GenericRejection.incidenceInput {x14.1} {x15.2})) →                 ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x2 x14 ∧ ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput {x13} {x14}) := by
  dsimp only at geometry finiteTests ⊢
  let S := fun (l : Fin 13) => Finset.univ.filter fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
  intro C F hm hc cost terms privateFlags negative cross
  apply finiteTests C F hm hc cost terms privateFlags _ cross
  intro k U
  constructor
  · intro sub
    obtain ⟨hmax, hdeg⟩ := (geometry U (missLines S U)).mp (Or.inl ⟨⟨k, sub⟩, rfl⟩)
    exact negative U (missLines S U) hmax hdeg
  · intro sub
    obtain ⟨hmax, hdeg⟩ := (geometry (zeroSet S U) U).mp (Or.inr ⟨⟨k, sub⟩, rfl⟩)
    exact negative (zeroSet S U) U hmax hdeg
