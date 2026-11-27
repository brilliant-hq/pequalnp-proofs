import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_427

theorem forward :
    ∀ n d : ℕ, (∃ (A B : Fin d → Finset (Fin n)),
      ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t) →
      n ≤ Nat.choose d (d / 2) := by
  classical
  rintro n d ⟨A, B, cover⟩
  let code (i : Fin n) : Finset (Fin d) := Finset.univ.filter fun t => i ∈ A t
  have comparable {i j : Fin n} (h : code i ⊆ code j) : i = j := by
    by_contra hij
    obtain ⟨t, hi, hj⟩ := (cover i j).mp hij
    have hit : t ∈ code i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hjA : j ∈ A t := (Finset.mem_filter.mp (h hit)).2
    exact (cover j j).mpr ⟨t, hjA, hj⟩ rfl
  have inj : Function.Injective code := fun _ _ h => comparable h.subset
  let family := Finset.univ.image code
  have anti : IsAntichain (· ⊆ ·) (family : Set (Finset (Fin d))) := by
    intro x hx y hy hxy hsub
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hxy (congrArg code (comparable hsub))
  simpa [family, Finset.card_image_of_injective _ inj] using anti.sperner

theorem backward : ∀ n d : ℕ, n ≤ Nat.choose d (d / 2) →
    (∃ (A B : Fin d → Finset (Fin n)),
      ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t) := by
  classical
  intro n d hn
  let layer := (Finset.univ : Finset (Fin d)).powersetCard (d / 2)
  have hc : Fintype.card ↥layer = Nat.choose d (d / 2) := by
    simp [layer]
  have he : n ≤ Fintype.card ↥layer := hc.symm ▸ hn
  let e : Fin n ↪ ↥layer := (Fin.castLEEmb he).trans (Fintype.equivFin ↥layer).symm.toEmbedding
  let code : Fin n → Finset (Fin d) := fun i => (e i).val
  have hsize (i : Fin n) : (code i).card = d / 2 :=
    (Finset.mem_powersetCard.mp (e i).property).2
  refine ⟨fun t => Finset.univ.filter (fun i => t ∈ code i),
    fun t => Finset.univ.filter (fun j => t ∉ code j), ?_⟩
  intro i j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hne
    by_contra h
    have hsub : code i ⊆ code j := by
      intro t ht
      by_contra hnot
      exact h ⟨t, ht, hnot⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hsize i, hsize j])
    exact hne (e.injective (Subtype.ext heq))
  · rintro ⟨t, ht, hnot⟩ rfl
    exact hnot ht

end PEqualNP.Outside.L_lib_427

theorem PEqualNP.Outside.L_lib_427 : (∀ n d : ℕ,
  (∃ (A B : Fin d → Finset (Fin n)),
    ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t) ↔
  n ≤ Nat.choose d (d / 2)) := by
  intro n d
  exact ⟨PEqualNP.Outside.L_lib_427.forward n d, PEqualNP.Outside.L_lib_427.backward n d⟩
