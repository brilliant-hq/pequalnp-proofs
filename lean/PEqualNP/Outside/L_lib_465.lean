import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_465_aux

theorem fwd {α : Type} [DecidableEq α] {n : ℕ} (M : Finset α) (f : α → Fin n)
    (hc : M.card = n) (hi : Set.InjOn f (M : Set α)) (i : Fin n) :
    ∃! e, e ∈ M ∧ f e = i := by
  have h1 : (M.image f).card = n := by rw [Finset.card_image_of_injOn hi, hc]
  have h2 : M.image f = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h1)
  have h3 : i ∈ M.image f := by rw [h2]; exact Finset.mem_univ _
  obtain ⟨e, he, hfe⟩ := Finset.mem_image.mp h3
  refine ⟨e, ⟨he, hfe⟩, ?_⟩
  rintro y ⟨hy, hfy⟩
  exact hi hy he (hfy.trans hfe.symm)

theorem bwd_inj {α : Type} {n : ℕ} (M : Finset α) (f : α → Fin n)
    (h : ∀ i, ∃! e, e ∈ M ∧ f e = i) : Set.InjOn f (M : Set α) := by
  intro a ha b hb hab
  obtain ⟨e, _, hu⟩ := h (f a)
  have h1 := hu a ⟨ha, rfl⟩
  have h2 := hu b ⟨hb, hab.symm⟩
  rw [h1, h2]

theorem bwd_card {α : Type} [DecidableEq α] {n : ℕ} (M : Finset α) (f : α → Fin n)
    (h : ∀ i, ∃! e, e ∈ M ∧ f e = i) : M.card = n := by
  have hi := bwd_inj M f h
  have h2 : M.image f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨e, ⟨he, hfe⟩, _⟩ := h i
    exact Finset.mem_image.mpr ⟨e, he, hfe⟩
  rw [← Finset.card_image_of_injOn hi, h2, Finset.card_univ, Fintype.card_fin]

end PEqualNP.Outside.L_lib_465_aux

open PEqualNP.Outside.L_lib_465_aux in
theorem PEqualNP.Outside.L_lib_465 : ∀ (n : ℕ) (T : Finset (Fin n × Fin n × Fin n)),
  (∃ M : Finset (Fin n × Fin n × Fin n), M ⊆ T ∧ M.card = n ∧
    Set.InjOn (fun e : Fin n × Fin n × Fin n => e.1) (M : Set _) ∧
    Set.InjOn (fun e : Fin n × Fin n × Fin n => e.2.1) (M : Set _) ∧ Set.InjOn (fun e : Fin n × Fin n × Fin n => e.2.2) (M : Set _)) ↔
  ∃ M : Finset (Fin n × Fin n × Fin n), M ⊆ T ∧
    ∀ u : Fin 3 × Fin n, ∃! e : Fin n × Fin n × Fin n, e ∈ M ∧
      ((u.1 = 0 ∧ e.1 = u.2) ∨ (u.1 = 1 ∧ e.2.1 = u.2) ∨
       (u.1 = 2 ∧ e.2.2 = u.2)) := by
  intro n T
  constructor
  · rintro ⟨M, hT, hc, h1, h2, h3⟩
    refine ⟨M, hT, ?_⟩
    rintro ⟨k, i⟩
    fin_cases k
    · simpa using fwd M (fun e : Fin n × Fin n × Fin n => e.1) hc h1 i
    · simpa using fwd M (fun e : Fin n × Fin n × Fin n => e.2.1) hc h2 i
    · simpa using fwd M (fun e : Fin n × Fin n × Fin n => e.2.2) hc h3 i
  · rintro ⟨M, hT, h⟩
    have g1 : ∀ i, ∃! e, e ∈ M ∧ (fun e : Fin n × Fin n × Fin n => e.1) e = i := by
      intro i; simpa using h (0, i)
    have g2 : ∀ i, ∃! e, e ∈ M ∧ (fun e : Fin n × Fin n × Fin n => e.2.1) e = i := by
      intro i; simpa using h (1, i)
    have g3 : ∀ i, ∃! e, e ∈ M ∧ (fun e : Fin n × Fin n × Fin n => e.2.2) e = i := by
      intro i; simpa using h (2, i)
    exact ⟨M, hT, bwd_card M _ g1, bwd_inj M _ g1, bwd_inj M _ g2, bwd_inj M _ g3⟩
