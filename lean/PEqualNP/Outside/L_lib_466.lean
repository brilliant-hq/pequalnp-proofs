import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_466 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable k ↔
  ∃ I : Finset (Fin n × Fin k), I.card = n ∧
    ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.1 ≠ q.1 ∧ (G.Adj p.1 q.1 → p.2 ≠ q.2) := by
  intro n k G
  constructor
  · rintro ⟨c⟩
    refine ⟨Finset.univ.image (fun v => (v, c v)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective]
      · simp
      · intro a b h
        exact congrArg Prod.fst h
    · intro p hp q hq hne
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨v, rfl⟩ := hp
      obtain ⟨w, rfl⟩ := hq
      have hvw : v ≠ w := by
        rintro rfl
        exact hne rfl
      exact ⟨hvw, fun h => c.valid h⟩
  · rintro ⟨I, hcard, hI⟩
    have hinj : Set.InjOn Prod.fst (I : Set (Fin n × Fin k)) := by
      intro p hp q hq h
      by_contra hne
      exact (hI p hp q hq hne).1 h
    have himg : I.image Prod.fst = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_fin]
    have hex : ∀ v : Fin n, ∃ p ∈ I, p.1 = v := by
      intro v
      have hv : v ∈ I.image Prod.fst := by
        rw [himg]
        exact Finset.mem_univ v
      simpa using hv
    choose f hfI hf1 using hex
    refine ⟨SimpleGraph.Coloring.mk (fun v => (f v).2) ?_⟩
    intro v w hadj
    have hne : f v ≠ f w := by
      intro h
      apply G.ne_of_adj hadj
      rw [← hf1 v, ← hf1 w, h]
    apply (hI (f v) (hfI v) (f w) (hfI w) hne).2
    rw [hf1 v, hf1 w]
    exact hadj
