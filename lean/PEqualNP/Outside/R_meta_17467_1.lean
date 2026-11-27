import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17467_1
    (hTranspose :
      ∀ (x1 x2 : ℕ),
        have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;
        have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;
        have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;
        have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>
          (6 : ℕ) ≤ x6.card ∧
            ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
              have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};
              x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧
                x4 x6 x7 ∧
                  (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧
                    ¬(x3 x6).IsAcyclic ∧
                      (∀ (x9 : Fin (x1 + x2)),
                          have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;
                          have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;
                          (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧
                        Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;
        have y3 : Finset (Fin x2 × Fin x1) → SimpleGraph (Fin (x2 + x1)) := fun (y3 : Finset (Fin x2 × Fin x1)) => SimpleGraph.fromRel fun (y4 y5 : Fin (x2 + x1)) => ∃ y6 ∈ y3, y4 = Fin.castAdd x1 y6.1 ∧ y5 = Fin.natAdd x2 y6.2;
        have y4 : Finset (Fin x2 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (y4 : Finset (Fin x2 × Fin x1)) (y5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x2 + x1) y5 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x1) y5 = PEqualNP.ReadTwo.fpl x2 fun (y6 : Fin x2) (y7 : Fin x1) => (y6, y7) ∈ y4;
        have y5 : Finset (Fin x2 × Fin x1) → Fin x2 × Fin x1 → Prop := fun (y5 : Finset (Fin x2 × Fin x1)) (y6 : Fin x2 × Fin x1) => (∀ y7 ∈ y5, y7.1 = y6.1 → y7 = y6) ∨ ∀ y7 ∈ y5, y7.2 = y6.2 → y7 = y6;
        have y6 : Finset (Fin x2 × Fin x1) → Prop := fun (y6 : Finset (Fin x2 × Fin x1)) =>
          (6 : ℕ) ≤ y6.card ∧
            ∃ (y7 : PEqualNP.CircuitLowerBounds.Circuit),
              have y8 : Set (Fin x2 × Fin x1) := {y8 : Fin x2 × Fin x1 | y8 ∈ y6 ∧ (y5 y6 y8 ∨ ∃ (y9 : PEqualNP.CircuitLowerBounds.Circuit), y9.size < y7.size ∧ y4 (y6.erase y8) y9)};
              y7.size + (3 : ℕ) ≤ (2 : ℕ) * y6.card ∧
                y4 y6 y7 ∧
                  (PEqualNP.ReadTwo.Lin fun (y9 : Fin x2) (y10 : Fin x1) => (y9, y10) ∈ y6) ∧
                    ¬(y3 y6).IsAcyclic ∧
                      (∀ (y9 : Fin (x2 + x1)),
                          have y10 : ℕ := ((y3 y6).neighborSet y9).ncard;
                          have y11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) y7 ↑y9;
                          (2 : ℕ) ≤ y10 → y11.card ≤ y10 ∧ (y10 = y11.card → ∀ y14 ∈ y11, (PEqualNP.MetaComplexity.NestedCover.gateAt y7 y14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x2 + x1) y7 y14 ⊆ y11)) ∧
                        Set.InjOn Prod.fst y8 ∧ Set.InjOn Prod.snd y8;
        ∀ (E : Finset (Fin x1 × Fin x2)), x6 E → y6 (E.image Prod.swap))
    (hLeftLeaf :
      ∀ (x1 x2 : ℕ),
        have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;
        have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;
        have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;
        have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>
          (6 : ℕ) ≤ x6.card ∧
            ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
              have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};
              x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧
                x4 x6 x7 ∧
                  (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧
                    ¬(x3 x6).IsAcyclic ∧
                      (∀ (x9 : Fin (x1 + x2)),
                          have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;
                          have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;
                          (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧
                        Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;
        ∀ (E : Finset (Fin x1 × Fin x2)), x6 E → (∃ e ∈ E, ∀ f ∈ E, f.1 = e.1 → f = e) → ∃ E' ⊂ E, x6 E') :
    (∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), x6 x7 → (∃ x9 ∈ x7, x5 x7 x9) → ∃ x10 ⊂ x7, x6 x10) := by
  intro x1 x2 x3 x4 x5 x6 E hE hLeaf
  exact Exists.elim hLeaf (fun e he =>
    Or.elim he.2
      (fun hL => hLeftLeaf x1 x2 E hE ⟨e, he.1, hL⟩)
      (fun hR =>
        have hESwap := hTranspose x1 x2 E hE
        have heSwapMem : Prod.swap e ∈ E.image Prod.swap := Finset.mem_image_of_mem Prod.swap he.1
        have heSwapLeft : ∀ f ∈ E.image Prod.swap, f.1 = (Prod.swap e).1 → f = Prod.swap e := by
          intro f hf hfst
          exact Exists.elim (Finset.mem_image.mp hf) (fun g hg => by
            have hgEq : g = e := hR g hg.1 (by rw [← hg.2] at hfst; exact hfst)
            rw [← hg.2, hgEq])
        Exists.elim (hLeftLeaf x2 x1 (E.image Prod.swap) hESwap ⟨Prod.swap e, heSwapMem, heSwapLeft⟩) (fun F hF =>
          have hFSub : F ⊆ E.image Prod.swap := hF.1.1
          have hFNot : ¬ E.image Prod.swap ⊆ F := hF.1.2
          have hSwapBack : F.image Prod.swap ⊆ E := by
            intro g hg
            exact Exists.elim (Finset.mem_image.mp hg) (fun p hp =>
              Exists.elim (Finset.mem_image.mp (hFSub hp.1)) (fun q hq => by
                have hgq : g = q := by rw [← hp.2, ← hq.2, Prod.swap_swap]
                rw [hgq]
                exact hq.1))
          have hNotSub : ¬ E ⊆ F.image Prod.swap := by
            intro hSub
            apply hFNot
            intro p hp
            exact Exists.elim (Finset.mem_image.mp hp) (fun q hq =>
              Exists.elim (Finset.mem_image.mp (hSub hq.1)) (fun r hr => by
                have hpr : p = r := by rw [← hq.2, ← hr.2, Prod.swap_swap]
                rw [hpr]
                exact hr.1))
          ⟨F.image Prod.swap, ⟨hSwapBack, hNotSub⟩, hTranspose x2 x1 F hF.2⟩)))
