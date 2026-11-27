import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_774

open Finset

/-- Neighbourhood of a set of rows. -/
def nb {n m : ℕ} (G : Fin n → Fin m → Bool) (S : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun b => ∃ a ∈ S, G a b = true)

theorem main (n m : ℕ) (G : Fin n → Fin m → Bool) :
  ∃ (k : ℕ) (r : Fin k → Fin n) (c : Fin k → Fin m) (R : Finset (Fin n)) (Cc : Finset (Fin m)),
    Function.Injective r ∧ Function.Injective c ∧ (∀ i, G (r i) (c i) = true) ∧
    (∀ a b, G a b = true → a ∈ R ∨ b ∈ Cc) ∧ R.card + Cc.card = k := by
  classical
  obtain ⟨S0, -, hS0⟩ := Finset.exists_max_image (univ : Finset (Finset (Fin n)))
    (fun S => (S.card : ℤ) - (nb G S).card) ⟨∅, mem_univ _⟩
  set δ : ℤ := (S0.card : ℤ) - (nb G S0).card with hδ
  have hδ0 : 0 ≤ δ := by
    have := hS0 ∅ (mem_univ _)
    simp [nb] at this
    omega
  set d : ℕ := δ.toNat with hd
  have hdδ : (d : ℤ) = δ := Int.toNat_of_nonneg hδ0
  let t : Fin n → Finset (Fin m ⊕ Fin d) := fun a =>
    (univ.filter (fun b => G a b = true)).map Function.Embedding.inl ∪
      (univ : Finset (Fin d)).map Function.Embedding.inr
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with hs | hs
    · simp [hs]
    have hsub : (nb G s).map Function.Embedding.inl ∪
        (univ : Finset (Fin d)).map Function.Embedding.inr ⊆ s.biUnion t := by
      intro x hx
      rw [mem_union] at hx
      obtain ⟨a0, ha0⟩ := hs
      rcases hx with hx | hx
      · obtain ⟨b, hb, rfl⟩ := mem_map.mp hx
        simp only [nb, mem_filter, mem_univ, true_and] at hb
        obtain ⟨a, ha, hab⟩ := hb
        exact mem_biUnion.mpr ⟨a, ha, mem_union_left _ (mem_map_of_mem _ (by simp [hab]))⟩
      · exact mem_biUnion.mpr ⟨a0, ha0, mem_union_right _ hx⟩
    have hc := card_le_card hsub
    rw [card_union_of_disjoint (by
      rw [disjoint_left]; intro x h1 h2
      obtain ⟨_, _, rfl⟩ := mem_map.mp h1
      obtain ⟨_, _, h⟩ := mem_map.mp h2
      simp at h), card_map, card_map, card_univ, Fintype.card_fin] at hc
    have := hS0 s (mem_univ _)
    omega
  obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hall
  let Mt : Finset (Fin n) := univ.filter (fun a => (f a).isLeft = true)
  have hun : (univ.filter (fun a => ¬ (f a).isLeft = true)).card ≤ d := by
    have := card_le_card_of_injOn (s := univ.filter (fun a => ¬ (f a).isLeft = true))
      (t := (univ : Finset (Fin d)).map Function.Embedding.inr) f (by
        intro a ha
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha
        simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range]
        cases h : f a with
        | inl b => rw [h] at ha; simp at ha
        | inr x => exact ⟨x, rfl⟩) (hf.injOn)
    simpa using this
  have hsum : Mt.card + (univ.filter (fun a => ¬ (f a).isLeft = true)).card = n := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hMt : n - d ≤ Mt.card := by omega
  obtain ⟨M', hM'sub, hM'card⟩ := exists_subset_card_eq hMt
  let e := M'.orderEmbOfFin hM'card
  have hmem : ∀ i, (f (e i)).isLeft = true := by
    intro i
    have := hM'sub (M'.orderEmbOfFin_mem hM'card i)
    simpa [Mt] using this
  let c : Fin (n - d) → Fin m := fun i => (f (e i)).getLeft (hmem i)
  have hc : ∀ i, f (e i) = Sum.inl (c i) := fun i => (Sum.inl_getLeft _ (hmem i)).symm
  refine ⟨n - d, fun i => e i, c, univ \ S0, nb G S0, e.injective, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have : f (e i) = f (e j) := by rw [hc, hc, hij]
    exact e.injective (hf this)
  · intro i
    have h1 := hft (e i)
    rw [hc] at h1
    simp only [t, mem_union, mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply] at h1
    rcases h1 with ⟨b, hb, hbe⟩ | ⟨x, hx⟩
    · rw [Sum.inl.inj hbe] at hb; exact hb
    · cases hx
  · intro a b hab
    by_cases ha : a ∈ S0
    · right
      simp only [nb, mem_filter, mem_univ, true_and]
      exact ⟨a, ha, hab⟩
    · left; simp [ha]
  · have h1 : (univ \ S0).card = n - S0.card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have h2 : S0.card ≤ n := by simpa using card_le_univ S0
    rw [h1]
    omega

end PEqualNP.Outside.L_lib_774

open PEqualNP.Outside.L_lib_774 in
theorem PEqualNP.Outside.L_lib_774 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool),
  ∃ (k : ℕ) (r : Fin k → Fin n) (c : Fin k → Fin m) (R : Finset (Fin n)) (Cc : Finset (Fin m)),
    Function.Injective r ∧ Function.Injective c ∧ (∀ i, G (r i) (c i) = true) ∧
    (∀ a b, G a b = true → a ∈ R ∨ b ∈ Cc) ∧ R.card + Cc.card = k :=
  main
