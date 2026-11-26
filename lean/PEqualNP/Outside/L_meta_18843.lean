import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18843_aux

abbrev inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

theorem k1 : ∀ q : Fin 13, 4 ≤ (Finset.univ.filter fun l => inc q l).card := by decide

theorem k2 : ∀ q q' : Fin 13, q ≠ q' → 7 ≤ (Finset.univ.filter fun l => inc q l ∨ inc q' l).card := by
  decide

theorem k3 : ∀ m : Fin 13, 4 ≤ (Finset.univ.filter fun p => inc p m).card := by decide

theorem k4 : ∀ m m' : Fin 13, m ≠ m' → 7 ≤ (Finset.univ.filter fun p => inc p m ∨ inc p m').card := by
  decide

theorem main (P L : Finset (Fin 13)) (hc : ∀ p l, inc p l → p ∈ P ∨ l ∈ L)
    (hP : P.Nonempty) (hL : L.Nonempty) : 14 ≤ P.card + L.card := by
  by_cases hA : ∀ q, q ∈ P
  · have : P = Finset.univ := Finset.eq_univ_iff_forall.mpr hA
    subst this
    have := hL.card_pos
    simp
    omega
  by_cases hB : ∀ m, m ∈ L
  · have : L = Finset.univ := Finset.eq_univ_iff_forall.mpr hB
    subst this
    have := hP.card_pos
    simp
    omega
  simp only [not_forall] at hA hB
  obtain ⟨q, hq⟩ := hA
  obtain ⟨m, hm⟩ := hB
  have hL4 : 4 ≤ L.card := by
    refine le_trans (k1 q) (Finset.card_le_card ?_)
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases hc q l hl with h | h
    · exact absurd h hq
    · exact h
  have hP4 : 4 ≤ P.card := by
    refine le_trans (k3 m) (Finset.card_le_card ?_)
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hc p m hp with h | h
    · exact h
    · exact absurd h hm
  have hX : 7 ≤ L.card ∨ 12 ≤ P.card := by
    by_cases h2 : ∃ a b, a ≠ b ∧ a ∉ P ∧ b ∉ P
    · obtain ⟨a, b, hab, ha, hb⟩ := h2
      left
      refine le_trans (k2 a b hab) (Finset.card_le_card ?_)
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rcases hl with hl | hl
      · rcases hc a l hl with h | h
        · exact absurd h ha
        · exact h
      · rcases hc b l hl with h | h
        · exact absurd h hb
        · exact h
    · right
      have h1 : Pᶜ.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        exact h2 ⟨a, b, hab, Finset.mem_compl.mp ha, Finset.mem_compl.mp hb⟩
      have := Finset.card_compl P
      simp at this
      omega
  have hY : 7 ≤ P.card ∨ 12 ≤ L.card := by
    by_cases h2 : ∃ a b, a ≠ b ∧ a ∉ L ∧ b ∉ L
    · obtain ⟨a, b, hab, ha, hb⟩ := h2
      left
      refine le_trans (k4 a b hab) (Finset.card_le_card ?_)
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with hp | hp
      · rcases hc p a hp with h | h
        · exact h
        · exact absurd h ha
      · rcases hc p b hp with h | h
        · exact h
        · exact absurd h hb
    · right
      have h1 : Lᶜ.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        exact h2 ⟨a, b, hab, Finset.mem_compl.mp ha, Finset.mem_compl.mp hb⟩
      have := Finset.card_compl L
      simp at this
      omega
  omega

end PEqualNP.Outside.L_meta_18843_aux

open PEqualNP.Outside.L_meta_18843_aux in
theorem PEqualNP.Outside.L_meta_18843 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : Finset (Fin (26 : ℕ))), (∀ (x5 x6 : Fin (26 : ℕ)), x1.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → (∃ (x6 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x6 ∈ x4) → (∃ (x7 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x7 ∈ x4) → (14 : ℕ) ≤ x4.card := by
  intro G _ hG S hS hp hl
  obtain ⟨p0, hp0⟩ := hp
  obtain ⟨l0, hl0⟩ := hl
  have hm := main (Finset.univ.filter fun (p : Fin 13) => Fin.castAdd 13 p ∈ S)
    (Finset.univ.filter fun (l : Fin 13) => Fin.natAdd 13 l ∈ S)
    (by
      intro p l h
      have := hS _ _ ((hG (Fin.castAdd 13 p) (Fin.natAdd 13 l)).mpr ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩)
      simpa using this)
    ⟨p0, by simpa using hp0⟩ ⟨l0, by simpa using hl0⟩
  have hd : Disjoint ((Finset.univ.filter fun (p : Fin 13) => Fin.castAdd 13 p ∈ S).image (Fin.castAdd 13))
      ((Finset.univ.filter fun (l : Fin 13) => Fin.natAdd 13 l ∈ S).image (Fin.natAdd 13)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hy
    have := congrArg Fin.val hb
    simp at this
    omega
  have hsub : (Finset.univ.filter fun (p : Fin 13) => Fin.castAdd 13 p ∈ S).image (Fin.castAdd 13) ∪
      (Finset.univ.filter fun (l : Fin 13) => Fin.natAdd 13 l ∈ S).image (Fin.natAdd 13) ⊆ S := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact ha
    · exact ha
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (Fin.castAdd_injective 13 13),
    Finset.card_image_of_injective _ (Fin.natAdd_injective 13 13)] at this
  omega
