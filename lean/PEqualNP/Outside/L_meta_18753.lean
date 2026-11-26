import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18753

open PEqualNP.BicliqueBlockCost

def nb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)) (t : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => G.Adj t v ∧ (v ∉ K ∨ t < v)

def fam {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)) :
    Finset (Block n) :=
  (K.filter fun t => (nb G K t).Nonempty).image fun t => (({t} : Finset (Fin n)), nb G K t)

theorem mem_nb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n))
    (t v : Fin n) : v ∈ nb G K t ↔ G.Adj t v ∧ (v ∉ K ∨ t < v) := by
  simp [nb]

theorem cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n))
    (hK : ∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K) : IsBlockCover G (fam G K) := by
  constructor
  · intro p hp
    simp only [fam, Finset.mem_image, Finset.mem_filter] at hp
    obtain ⟨t, ⟨_, hne⟩, rfl⟩ := hp
    refine ⟨?_, Finset.singleton_nonempty t, hne, ?_⟩
    · rw [Finset.disjoint_singleton_left]
      intro ht
      exact (G.ne_of_adj ((mem_nb G K t t).mp ht).1) rfl
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ((mem_nb G K a b).mp hb).1
  · intro u v huv
    have key : ∀ a b : Fin n, G.Adj a b → a ∈ K → (b ∉ K ∨ a < b) →
        ∃ p ∈ fam G K, a ∈ p.1 ∧ b ∈ p.2 := by
      intro a b hab ha hb
      have hmem : b ∈ nb G K a := (mem_nb G K a b).mpr ⟨hab, hb⟩
      refine ⟨(({a} : Finset (Fin n)), nb G K a), ?_, Finset.mem_singleton_self a, hmem⟩
      simp only [fam, Finset.mem_image, Finset.mem_filter]
      exact ⟨a, ⟨ha, ⟨b, hmem⟩⟩, rfl⟩
    by_cases hu : u ∈ K
    · by_cases hv : v ∈ K
      · rcases lt_or_gt_of_ne (G.ne_of_adj huv) with h | h
        · obtain ⟨p, hp, h1, h2⟩ := key u v huv hu (Or.inr h)
          exact ⟨p, hp, Or.inl ⟨h1, h2⟩⟩
        · obtain ⟨p, hp, h1, h2⟩ := key v u huv.symm hv (Or.inr h)
          exact ⟨p, hp, Or.inr ⟨h1, h2⟩⟩
      · obtain ⟨p, hp, h1, h2⟩ := key u v huv hu (Or.inl hv)
        exact ⟨p, hp, Or.inl ⟨h1, h2⟩⟩
    · have hv : v ∈ K := (hK u v huv).resolve_left hu
      obtain ⟨p, hp, h1, h2⟩ := key v u huv.symm hv (Or.inl hu)
      exact ⟨p, hp, Or.inr ⟨h1, h2⟩⟩

theorem pairs_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)) :
    ∑ t ∈ K, (nb G K t).card ≤ G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x : (Σ _ : Fin n, Fin n) => s(x.1, x.2))
  · intro x hx
    have hx' := Finset.mem_sigma.mp hx
    have h := (mem_nb G K x.1 x.2).mp hx'.2
    simpa [SimpleGraph.mem_edgeFinset] using h.1
  · intro x hx y hy hxy
    have hx' := Finset.mem_sigma.mp hx
    have hy' := Finset.mem_sigma.mp hy
    have hxn := (mem_nb G K x.1 x.2).mp hx'.2
    have hyn := (mem_nb G K y.1 y.2).mp hy'.2
    have hxy' : s(x.1, x.2) = s(y.1, y.2) := hxy
    rcases Sym2.eq_iff.mp hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Sigma.ext h1 (heq_of_eq h2)
    · exfalso
      have hx2K : x.2 ∈ K := h2 ▸ hy'.1
      have hy2K : y.2 ∈ K := h1 ▸ hx'.1
      have a1 : x.1 < x.2 := hxn.2.resolve_left (fun h => h hx2K)
      have a2 : y.1 < y.2 := hyn.2.resolve_left (fun h => h hy2K)
      rw [← h2, ← h1] at a2
      exact lt_asymm a1 a2

theorem cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)) :
    familyCost (fam G K) ≤ G.edgeSet.ncard + K.card - 1 := by
  have hinj : ∀ a ∈ K.filter (fun t => (nb G K t).Nonempty),
      ∀ b ∈ K.filter (fun t => (nb G K t).Nonempty),
      (({a} : Finset (Fin n)), nb G K a) = (({b} : Finset (Fin n)), nb G K b) → a = b := by
    intro a _ b _ h
    exact Finset.singleton_injective (congrArg Prod.fst h)
  have hcard : (fam G K).card = (K.filter fun t => (nb G K t).Nonempty).card :=
    Finset.card_image_of_injOn hinj
  have hsum : ∑ p ∈ fam G K, blockCost p =
      ∑ t ∈ K.filter (fun t => (nb G K t).Nonempty), (nb G K t).card := by
    unfold fam
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro t _
    simp [blockCost]
  have hle1 : ∑ t ∈ K.filter (fun t => (nb G K t).Nonempty), (nb G K t).card ≤
      ∑ t ∈ K, (nb G K t).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hle2 := pairs_le G K
  have hK' : (K.filter fun t => (nb G K t).Nonempty).card ≤ K.card := Finset.card_filter_le _ _
  have h0 : (K.filter fun t => (nb G K t).Nonempty).card = 0 →
      ∑ t ∈ K.filter (fun t => (nb G K t).Nonempty), (nb G K t).card = 0 := by
    intro h
    rw [Finset.card_eq_zero.mp h]
    simp
  have hE : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  unfold familyCost
  rw [hsum, hcard, hE]
  omega

end PEqualNP.Outside.L_meta_18753

theorem PEqualNP.Outside.L_meta_18753 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ))) := by
  intro n G _ K hK
  exact ⟨PEqualNP.Outside.L_meta_18753.fam G K, PEqualNP.Outside.L_meta_18753.cover G K hK,
    PEqualNP.Outside.L_meta_18753.cost G K⟩
