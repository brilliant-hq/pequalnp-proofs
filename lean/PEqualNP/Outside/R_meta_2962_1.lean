import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      let M := PEqualNP.Core.maximalCores G C
      let D := M.biUnion (PEqualNP.TopForm.gammaE G C)
      let U := M.biUnion (PEqualNP.Core.coneSet n C)
      ∃ S : Finset (Fin n),
        (∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S) ∧
        D.card + S.card ≤ U.card + M.card) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (D : Finset (Sym2 (Fin n))) (S T T' : Finset (Fin n)),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover
        (G.deleteEdges (D : Set (Sym2 (Fin n)))) T' →
      (∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S) →
      T.card ≤ S.card + T'.card) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro packing augmentation n G _ C s T T' bipartite noFour ao correct fixed minCover minCover'
  obtain ⟨S, cover, bound⟩ := packing n G C s bipartite noFour ao correct fixed
  have augmented := augmentation n G
    ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C))
    S T T' minCover minCover' cover
  omega
