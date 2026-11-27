import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_470 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  (∃ c : Fin n → Fin k, ∀ u v, G.Adj u v → c u ≠ c v) ↔
    ∃ F : Finset (Finset (Fin n)), F.card ≤ k ∧
      (∀ v, ∃ S ∈ F, v ∈ S) ∧ ∀ S ∈ F, Gᶜ.IsClique (↑S) := by
  intro n k G
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Finset.univ.image (fun i => Finset.univ.filter (c · = i)), ?_, ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simp)
    · intro v
      exact ⟨Finset.univ.filter (c · = c v), Finset.mem_image.2 ⟨c v, by simp, rfl⟩, by simp⟩
    · intro S hS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
      intro u hu v hv huv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
      rw [SimpleGraph.compl_adj]
      exact ⟨huv, fun h => hc u v h (hu.trans hv.symm)⟩
  · rintro ⟨F, hk, hcov, hcl⟩
    choose S hSF hvS using hcov
    refine ⟨fun v => Fin.castLE hk (F.equivFin ⟨S v, hSF v⟩), ?_⟩
    intro u v huv heq
    have h1 : F.equivFin ⟨S u, hSF u⟩ = F.equivFin ⟨S v, hSF v⟩ := Fin.castLE_injective hk heq
    have h2 : S u = S v := congrArg Subtype.val (F.equivFin.injective h1)
    have h3 := hcl (S u) (hSF u) (hvS u) (by rw [h2]; exact hvS v) (G.ne_of_adj huv)
    rw [SimpleGraph.compl_adj] at h3
    exact h3.2 huv
