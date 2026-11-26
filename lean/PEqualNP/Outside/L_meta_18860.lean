import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18860_aux

theorem sat {α : Type} [DecidableEq (Set α)] (A : Set (Set α)) (T : Finset (Set α)) :
    ∀ (n : ℕ) (L : List (Set α)), L.Nodup → L.toFinset ⊆ T →
      (∀ (i : ℕ) (x : Set α), L[i]? = Option.some x →
        ∃ a ∈ A ∪ ↑(List.take i L).toFinset, ∃ b ∈ A ∪ ↑(List.take i L).toFinset,
          x = a ∩ b ∨ x = a ∪ b) →
      (T \ L.toFinset).card = n →
      ∃ L' : List (Set α), L'.Nodup ∧ L'.toFinset ⊆ T ∧
        (∀ (i : ℕ) (x : Set α), L'[i]? = Option.some x →
          ∃ a ∈ A ∪ ↑(List.take i L').toFinset, ∃ b ∈ A ∪ ↑(List.take i L').toFinset,
            x = a ∩ b ∨ x = a ∪ b) ∧
        ∀ x ∈ A ∪ ↑L'.toFinset, ∀ y ∈ A ∪ ↑L'.toFinset, ∀ z ∈ T,
          z = x ∩ y ∨ z = x ∪ y → z ∈ A ∪ ↑L'.toFinset := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hnd hsub hbuilt hcard
  by_cases hc : ∀ x ∈ A ∪ ↑L.toFinset, ∀ y ∈ A ∪ ↑L.toFinset, ∀ z ∈ T,
      z = x ∩ y ∨ z = x ∪ y → z ∈ A ∪ ↑L.toFinset
  · exact ⟨L, hnd, hsub, hbuilt, hc⟩
  · push Not at hc
    obtain ⟨x, hx, y, hy, z, hzT, hz, hzn⟩ := hc
    have hzL : z ∉ L := by
      intro h
      exact hzn (Or.inr (by simpa using h))
    refine ih _ ?_ (L ++ [z]) ?_ ?_ ?_ rfl
    · subst hcard
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨z, by simp [hzT, hzL], by simp⟩
      · intro w
        simp
        tauto
    · rw [List.nodup_append]
      simp only [hnd, List.nodup_singleton, List.mem_singleton, true_and]
      intro a ha b hb
      subst hb
      intro hab
      exact hzL (hab ▸ ha)
    · intro w hw
      simp at hw
      rcases hw with h | h
      · exact h ▸ hzT
      · exact hsub (by simpa using h)
    · intro i w hw
      rcases lt_trichotomy i L.length with h | h | h
      · rw [List.getElem?_append_left h] at hw
        rw [List.take_append_of_le_length h.le]
        exact hbuilt i w hw
      · subst h
        have ht : List.take L.length (L ++ [z]) = L := by simp
        rw [ht]
        simp at hw
        subst hw
        exact ⟨x, hx, y, hy, hz⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hw
        cases hw

end PEqualNP.Outside.L_meta_18860_aux

theorem PEqualNP.Outside.L_meta_18860 : ∀ (x1 : Set (Set (Fin (26 : ℕ) → Bool))) (x2 : Finset (Set (Fin (26 : ℕ) → Bool))), (∀ x3 ∈ x2, x3 ∉ x1) → ∃ (x4 : List (Set (Fin (26 : ℕ) → Bool))), x4.Nodup ∧ x4.toFinset ⊆ x2 ∧ (∀ (x5 : ℕ) (x6 : Set (Fin (26 : ℕ) → Bool)), x4[x5]? = Option.some x6 → ∃ x8 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, ∃ x9 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, x6 = x8 ∩ x9 ∨ x6 = x8 ∪ x9) ∧ ∀ x5 ∈ x1 ∪ ↑x4.toFinset, ∀ x7 ∈ x1 ∪ ↑x4.toFinset, ∀ x9 ∈ x2, x9 = x5 ∩ x7 ∨ x9 = x5 ∪ x7 → x9 ∈ x1 ∪ ↑x4.toFinset := by
  intro x1 x2 _
  exact PEqualNP.Outside.L_meta_18860_aux.sat x1 x2 _ [] List.nodup_nil (by simp) (by simp) rfl
