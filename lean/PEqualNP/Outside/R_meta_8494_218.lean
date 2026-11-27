import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-8494`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_8494_218 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ)} → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (29 : ℕ) ≤ (List.foldl (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) => x6 ++ [(List.map (fun (x8 : ℕ) => x6.getD x8 (0 : ℕ)) x7.inputs).sum]) (List.replicate (14 : ℕ) (1 : ℕ)) x1.gates).getD x1.output (0 : ℕ)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ)} → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (29 : ℕ) ≤ (List.foldl (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) => x6 ++ [(List.map (fun (x8 : ℕ) => x6.getD x8 (0 : ℕ)) x7.inputs).sum]) (List.replicate (14 : ℕ) (1 : ℕ)) x1.gates).getD x1.output (0 : ℕ)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ)} → (29 : ℕ) ≤ (List.foldl (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) => x6 ++ [(List.map (fun (x8 : ℕ) => x6.getD x8 (0 : ℕ)) x7.inputs).sum]) (List.replicate (14 : ℕ) (1 : ℕ)) x1.gates).getD x1.output (0 : ℕ)) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
