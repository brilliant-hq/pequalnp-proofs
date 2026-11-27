import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_658

open Finset

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The move map of the down compression at a site. -/
def mv (a : α) (G : Finset (Finset α)) (s : Finset α) : Finset α :=
  if s.erase a ∈ G then s else s.erase a

theorem mv_injOn (a : α) (G : Finset (Finset α)) : Set.InjOn (mv a G) G := by
  intro s hs t ht hst
  simp only [mv] at hst
  by_cases h1 : s.erase a ∈ G <;> by_cases h2 : t.erase a ∈ G <;> simp only [h1, h2, ite_true,
    ite_false] at hst
  · exact hst
  · exact absurd (hst ▸ (Finset.mem_coe.mp hs)) h2
  · exact absurd (hst ▸ (Finset.mem_coe.mp ht)) h1
  · have ha : a ∈ s := by
      by_contra h
      exact h1 (by rw [Finset.erase_eq_of_notMem h]; exact hs)
    have hb : a ∈ t := by
      by_contra h
      exact h2 (by rw [Finset.erase_eq_of_notMem h]; exact ht)
    rw [← Finset.insert_erase ha, ← Finset.insert_erase hb, hst]

theorem comp_eq (a : α) (G : Finset (Finset α)) : Down.compression a G = G.image (mv a G) := by
  ext u
  rw [Down.mem_compression, Finset.mem_image]
  constructor
  · rintro (⟨hu, he⟩ | ⟨hu, hi⟩)
    · exact ⟨u, hu, by simp [mv, he]⟩
    · refine ⟨insert a u, hi, ?_⟩
      have hau : a ∉ u := fun h => hu (by rw [Finset.insert_eq_of_mem h] at hi; exact hi)
      simp [mv, Finset.erase_insert hau, hu]
  · rintro ⟨s, hs, rfl⟩
    by_cases h : s.erase a ∈ G
    · left; simp [mv, h, hs]
    · right
      have ha : a ∈ s := by
        by_contra h'
        exact h (by rw [Finset.erase_eq_of_notMem h']; exact hs)
      rw [mv, if_neg h]
      exact ⟨h, by rw [Finset.insert_erase ha]; exact hs⟩

theorem proj_le (a : α) (T : Finset α) (G : Finset (Finset α)) :
    ((Down.compression a G).image (· ∩ T)).card ≤ (G.image (· ∩ T)).card := by
  by_cases haT : a ∈ T
  · calc ((Down.compression a G).image (· ∩ T)).card
        ≤ (Down.compression a (G.image (· ∩ T))).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_image] at hp
          obtain ⟨u, hu, rfl⟩ := hp
          rw [Down.mem_compression] at hu ⊢
          rcases hu with ⟨hu, he⟩ | ⟨hu, hi⟩
          · left
            refine ⟨Finset.mem_image_of_mem _ hu, ?_⟩
            rw [Finset.mem_image]
            exact ⟨u.erase a, he, by rw [Finset.erase_inter]⟩
          · have hau : a ∉ u := fun h => hu (by rw [Finset.insert_eq_of_mem h] at hi; exact hi)
            have hip : insert a (u ∩ T) ∈ G.image (· ∩ T) := by
              rw [Finset.mem_image]
              exact ⟨insert a u, hi, by rw [Finset.insert_inter_of_mem haT]⟩
            by_cases hp : u ∩ T ∈ G.image (· ∩ T)
            · left
              refine ⟨hp, ?_⟩
              have : a ∉ u ∩ T := fun h => hau (Finset.mem_inter.mp h).1
              rw [Finset.erase_eq_of_notMem this]; exact hp
            · right; exact ⟨hp, hip⟩
      _ = (G.image (· ∩ T)).card := Down.card_compression _ _
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_image] at hp ⊢
    obtain ⟨u, hu, rfl⟩ := hp
    rw [Down.mem_compression] at hu
    rcases hu with ⟨hu, _⟩ | ⟨_, hi⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨insert a u, hi, by rw [Finset.insert_inter_of_notMem haT]⟩

theorem weight_lt (a : α) (G : Finset (Finset α)) (s : Finset α) (hs : s ∈ G) (ha : a ∈ s)
    (he : s.erase a ∉ G) :
    ∑ u ∈ Down.compression a G, u.card < ∑ u ∈ G, u.card := by
  rw [comp_eq, Finset.sum_image (fun x hx y hy h => mv_injOn a G hx hy h)]
  apply Finset.sum_lt_sum
  · intro u _
    unfold mv
    split_ifs
    · exact le_rfl
    · exact Finset.card_erase_le
  · refine ⟨s, hs, ?_⟩
    rw [mv, if_neg he]
    rw [Finset.card_erase_of_mem ha]
    have : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega

theorem step_of_not_down (G : Finset (Finset α)) (x : Finset α) (hx : x ∈ G) :
    ∀ y : Finset α, y ⊆ x → y ∉ G → ∃ s ∈ G, ∃ a ∈ s, s.erase a ∉ G := by
  induction x using Finset.strongInduction with
  | H x ih =>
    intro y hy hyG
    have hne : x ≠ y := fun h => hyG (h ▸ hx)
    have : ∃ a ∈ x, a ∉ y := by
      by_contra h
      push_neg at h
      exact hne (Finset.Subset.antisymm h hy)
    obtain ⟨a, hax, hay⟩ := this
    by_cases he : x.erase a ∈ G
    · exact ih (x.erase a) (Finset.erase_ssubset hax) he y
        (fun z hz => Finset.mem_erase.mpr ⟨fun h => hay (h ▸ hz), hy hz⟩) hyG
    · exact ⟨x, hx, a, hax, he⟩

theorem exists_down : ∀ (N : ℕ) (G : Finset (Finset α)), ∑ u ∈ G, u.card = N →
    ∃ F : Finset (Finset α), F.card = G.card ∧ (∀ x ∈ F, ∀ y : Finset α, y ⊆ x → y ∈ F) ∧
      ∀ T : Finset α, (F.image (· ∩ T)).card ≤ (G.image (· ∩ T)).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G hN
    by_cases hd : ∀ x ∈ G, ∀ y : Finset α, y ⊆ x → y ∈ G
    · exact ⟨G, rfl, hd, fun T => le_rfl⟩
    · push_neg at hd
      obtain ⟨x, hx, y, hy, hyG⟩ := hd
      obtain ⟨s, hs, a, ha, he⟩ := step_of_not_down G x hx y hy hyG
      have hlt := weight_lt a G s hs ha he
      obtain ⟨F, hF1, hF2, hF3⟩ := ih _ (hN ▸ hlt) (Down.compression a G) rfl
      refine ⟨F, by rw [hF1, Down.card_compression], hF2, fun T => (hF3 T).trans (proj_le a T G)⟩

theorem shrink : ∀ (k : ℕ) (F : Finset (Finset α)) (t : ℕ), F.card = t + k →
    (∀ x ∈ F, ∀ y : Finset α, y ⊆ x → y ∈ F) →
    ∃ F' ⊆ F, F'.card = t ∧ ∀ x ∈ F', ∀ y : Finset α, y ⊆ x → y ∈ F' := by
  intro k
  induction k with
  | zero => intro F t hc hd; exact ⟨F, Finset.Subset.refl _, by omega, hd⟩
  | succ k ih =>
    intro F t hc hd
    have hne : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image F Finset.card hne
    have hd' : ∀ x ∈ F.erase s, ∀ y : Finset α, y ⊆ x → y ∈ F.erase s := by
      intro x hx y hy
      rw [Finset.mem_erase] at hx ⊢
      refine ⟨?_, hd x hx.2 y hy⟩
      rintro rfl
      have h1 := hmax x hx.2
      have h2 : y = x := Finset.eq_of_subset_of_card_le hy h1
      exact hx.1 h2.symm
    obtain ⟨F', hF', h1, h2⟩ := ih (F.erase s) t (by rw [Finset.card_erase_of_mem hs]; omega) hd'
    exact ⟨F', hF'.trans (Finset.erase_subset _ _), h1, h2⟩

end PEqualNP.Outside.L_lib_658

open PEqualNP.Outside.L_lib_658 in
theorem PEqualNP.Outside.L_lib_658 : ∀ (n r : Nat) (scope : Fin r → Finset (Fin n)) (cap : Fin r → Nat) (t : Nat),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let full := (Finset.univ : Finset Slot).filter (fun e => e.2 ⊆ scope e.1)
  let words := (Finset.univ : Finset (Finset Site))
  (∃ A ∈ full.powerset,
    t ≤ (words.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ A)).card ∧
    ∀ i : Fin r, (A.filter (fun e => e.1 = i)).card ≤ cap i) ↔
  ∃ F : Finset (Finset Site), F.card = t ∧
    (∀ x ∈ F, ∀ y : Finset Site, y ⊆ x → y ∈ F) ∧
    ∀ i : Fin r, (F.filter (fun a => a ⊆ scope i)).card ≤ cap i := by
  intro n r scope cap t Site Slot full words
  constructor
  · rintro ⟨A, _, ht, hcap⟩
    set G := words.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ A) with hG
    obtain ⟨F, hF1, hF2, hF3⟩ := exists_down _ G rfl
    obtain ⟨F', hF', h1, h2⟩ := shrink (G.card - t) F t (by omega) hF2
    refine ⟨F', h1, h2, fun i => ?_⟩
    calc (F'.filter (fun a => a ⊆ scope i)).card
        ≤ (F.filter (fun a => a ⊆ scope i)).card := Finset.card_le_card (Finset.filter_subset_filter _ hF')
      _ ≤ (F.image (· ∩ scope i)).card := by
          apply Finset.card_le_card
          intro a ha
          rw [Finset.mem_filter] at ha
          rw [Finset.mem_image]
          exact ⟨a, ha.1, Finset.inter_eq_left.mpr ha.2⟩
      _ ≤ (G.image (· ∩ scope i)).card := hF3 _
      _ ≤ (A.filter (fun e => e.1 = i)).card := by
          apply Finset.card_le_card_of_injOn (fun p => (i, p))
          · intro p hp
            rw [Finset.mem_coe, Finset.mem_image] at hp
            obtain ⟨x, hx, rfl⟩ := hp
            rw [hG, Finset.mem_filter] at hx
            rw [Finset.mem_coe, Finset.mem_filter]
            exact ⟨hx.2 i, rfl⟩
          · intro p _ q _ h
            simpa using h
      _ ≤ cap i := hcap i
  · rintro ⟨F, hF1, hF2, hF3⟩
    refine ⟨full.filter (fun e => e.2 ∈ F), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_,
      fun i => ?_⟩
    · rw [← hF1]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i => ?_⟩
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, Finset.inter_subset_right⟩, hF2 x hx _ Finset.inter_subset_left⟩
    · calc ((full.filter (fun e => e.2 ∈ F)).filter (fun e => e.1 = i)).card
          ≤ (F.filter (fun a => a ⊆ scope i)).card := by
            apply Finset.card_le_card_of_injOn Prod.snd
            · intro e he
              rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at he
              rw [Finset.mem_coe, Finset.mem_filter]
              refine ⟨he.1.2, ?_⟩
              rw [← he.2]; exact he.1.1.2
            · intro e he f hf h
              rw [Finset.mem_coe, Finset.mem_filter] at he hf
              exact Prod.ext (he.2.trans hf.2.symm) h
        _ ≤ cap i := hF3 i
