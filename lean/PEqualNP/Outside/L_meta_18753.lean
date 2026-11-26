import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18753_aux

open PEqualNP.BicliqueBlockCost

def nb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj v w ∧ (w ∈ S → v < w))

theorem sum_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    (∑ v ∈ S, (nb G S v).card) ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  apply Finset.card_le_card_of_injOn (fun x => s(x.1, x.2))
  · intro x hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, nb, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hx.2.1
  · intro x hx y hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, nb, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hy
    simp only [Sym2.eq_iff] at hxy
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    simp only at hx hy hxy
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2; rfl
    · subst h1 h2
      have := hx.2.2 hy.1
      have := hy.2.2 hx.1
      exact absurd (lt_trans ‹a < b› ‹b < a›) (lt_irrefl a)

end PEqualNP.Outside.L_meta_18753_aux

open PEqualNP.BicliqueBlockCost PEqualNP.Outside.L_meta_18753_aux in
theorem PEqualNP.Outside.L_meta_18753 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ)) := by
  intro n G _ S hS
  let T := S.filter (fun v => (nb G S v).Nonempty)
  let f : Fin n → Block n := fun v => ({v}, nb G S v)
  have finj : Set.InjOn f T := by
    intro a _ b _ h
    simpa [f] using congrArg Prod.fst h
  refine ⟨T.image f, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, T, Finset.mem_filter] at hp
    obtain ⟨v, ⟨_, hne⟩, rfl⟩ := hp
    refine ⟨?_, by simp [f], hne, ?_⟩
    · simp only [f, Finset.disjoint_singleton_left, nb, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      exact G.irrefl h.1
    · intro a ha b hb
      simp only [f, Finset.mem_singleton] at ha
      subst ha
      simp only [f, nb, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb.1
  · intro u v huv
    have hne : u ≠ v := G.ne_of_adj huv
    have key : ∀ a b, G.Adj a b → a ∈ S → (b ∈ S → a < b) →
        ∃ p ∈ T.image f, (a ∈ p.1 ∧ b ∈ p.2) := by
      intro a b hab ha hlt
      have hb : b ∈ nb G S a := by
        simp only [nb, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hab, hlt⟩
      refine ⟨f a, Finset.mem_image_of_mem f ?_, by simp [f], hb⟩
      simp only [T, Finset.mem_filter]
      exact ⟨ha, b, hb⟩
    rcases lt_or_gt_of_ne hne with h | h
    · by_cases hu : u ∈ S
      · obtain ⟨p, hp, hp2⟩ := key u v huv hu (fun _ => h)
        exact ⟨p, hp, Or.inl hp2⟩
      · have hv : v ∈ S := (hS u v huv).resolve_left hu
        obtain ⟨p, hp, hp2⟩ := key v u huv.symm hv (fun h' => absurd h' hu)
        exact ⟨p, hp, Or.inr hp2⟩
    · by_cases hv : v ∈ S
      · obtain ⟨p, hp, hp2⟩ := key v u huv.symm hv (fun _ => h)
        exact ⟨p, hp, Or.inr hp2⟩
      · have hu : u ∈ S := (hS u v huv).resolve_right hv
        obtain ⟨p, hp, hp2⟩ := key u v huv hu (fun h' => absurd h' hv)
        exact ⟨p, hp, Or.inl hp2⟩
  · unfold familyCost
    rw [Finset.sum_image finj, Finset.card_image_of_injOn finj]
    have h1 : ∀ v ∈ T, blockCost (f v) = (nb G S v).card := by
      intro v _
      simp [blockCost, f]
    rw [Finset.sum_congr rfl h1]
    have h2 : (∑ v ∈ T, (nb G S v).card) ≤ ∑ v ∈ S, (nb G S v).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h3 := sum_le G S
    have h4 : T.card ≤ S.card := Finset.card_filter_le _ _
    have h5 : S.card = 0 → (∑ v ∈ S, (nb G S v).card) = 0 := by
      intro h
      rw [Finset.card_eq_zero.mp h, Finset.sum_empty]
    omega
