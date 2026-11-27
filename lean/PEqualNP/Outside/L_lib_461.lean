import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_461 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  (∃ C : Finset (Fin n), C.card ≤ k ∧ G.IsVertexCover (C : Set (Fin n))) ↔
  ∃ D : Finset (Fin n), D.card ≤ k ∧ ∀ x : Fin n,
    ¬ Relation.TransGen (fun a b : Fin n => a ∉ D ∧ b ∉ D ∧ G.Adj a b) x x := by
  intro n k G
  constructor
  · rintro ⟨C, hk, hC⟩
    refine ⟨C, hk, fun x h => ?_⟩
    obtain ⟨b, _, hbc⟩ := Relation.TransGen.tail'_iff.mp h
    rcases hC hbc.2.2 with h | h
    · exact hbc.1 h
    · exact hbc.2.1 h
  · rintro ⟨D, hk, hD⟩
    refine ⟨D, hk, fun v w hvw => ?_⟩
    by_contra h
    simp only [Finset.mem_coe, not_or] at h
    exact hD v (Relation.TransGen.tail (Relation.TransGen.single ⟨h.1, h.2, hvw⟩) ⟨h.2, h.1, hvw.symm⟩)
