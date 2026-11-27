import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25500
import PEqualNP.Outside.L_meta_25489

-- Combines the merged L-meta-25500 (residual reduction) and L-meta-25489 (half-size row bound);
-- the helpers lit, col, lit_col, col_inj and lit_sep come from L-meta-25500.

namespace PEqualNP.Outside.L_meta_25512
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_25500_aux

theorem col_cover {h : ℕ} (c : Fin (2 * h)) : ∃ (j : Fin h) (e : Bool), c = col j e := by
  have hj : c.val / 2 < h := by have := c.isLt; omega
  refine ⟨⟨c.val / 2, hj⟩, decide (c.val % 2 = 1), Fin.ext ?_⟩
  show c.val = 2 * (c.val / 2) + (decide (c.val % 2 = 1)).toNat
  rcases Nat.mod_two_eq_zero_or_one c.val with h0 | h1
  · simp [h0]; omega
  · simp [h1]; omega

theorem row_card {r h : ℕ} (b : Fin r → Fin h → Bool) (u : Fin r) :
    (Finset.univ.filter (fun c => lit b u c = true)).card = h := by
  have heq : Finset.univ.filter (fun c => lit b u c = true) =
      Finset.univ.image (fun j => col j (b u j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    obtain ⟨j, e, rfl⟩ := col_cover c
    rw [lit_col]
    constructor
    · intro he
      refine ⟨j, ?_⟩
      have : b u j = e := by simpa using he
      rw [this]
    · rintro ⟨j', hj'⟩
      obtain ⟨h1, h2⟩ := col_inj hj'
      subst h1; subst h2; simp
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro j j' hjj
    exact (col_inj hjj).1

theorem lit_inj {r h : ℕ} (b : Fin r → Fin h → Bool) (hb : Function.Injective b) :
    Function.Injective (lit b) := by
  intro u v e
  by_contra huv
  obtain ⟨c, h1, h2⟩ := lit_sep b hb u v huv
  have := congrFun e c
  rw [h1, h2] at this
  exact Bool.noConfusion this

theorem col_miss {r h : ℕ} (b : Fin r → Fin h → Bool)
    (hnc : ∀ i, ∃ u v, b u i = false ∧ b v i = true) (c : Fin (2 * h)) :
    ∃ v, lit b v c = false := by
  obtain ⟨j, e, rfl⟩ := col_cover c
  obtain ⟨u, v, hu, hv⟩ := hnc j
  cases e
  · exact ⟨v, by rw [lit_col, hv]; rfl⟩
  · exact ⟨u, by rw [lit_col, hu]; rfl⟩

end PEqualNP.Outside.L_meta_25512

open PEqualNP.Outside.L_meta_25512 PEqualNP.Outside.L_meta_25500_aux in
theorem PEqualNP.Outside.L_meta_25512 : ∀ (k m s : ℕ) (name : Fin m → Fin (2 ^ k)),
  2 ≤ k → 2 ≤ m → Function.Injective name →
  PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin m) (c : Fin (2 * k)) =>
      (name u).val.testBit (c.val / 2) == c.val.testBit 0) s →
  2 * m ≤ s := by
  intro k m s name hk hm hinj hrep
  by_contra hlt
  have hlt' : s < 2 * m := by omega
  have H := PEqualNP.Outside.L_meta_25500 k m s name hk hm hinj hrep hlt'
  obtain ⟨r, h, row, coord, D, hrow, hcoord, hb, hh, hhr, hnc, hmono, hback, hRD, hsz, hlt2,
    hreads⟩ := H
  have hRD' : PEqualNP.Represents.Represents
      (lit fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) D := hRD
  have H2 := PEqualNP.Outside.L_meta_25489 r h
    (lit fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) D hh
    (lit_inj _ hb) (fun u => row_card _ u) (col_miss _ hnc) hmono hback hRD' hreads
  omega
