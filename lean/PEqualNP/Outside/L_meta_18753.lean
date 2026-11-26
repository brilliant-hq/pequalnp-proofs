import PEqualNP.Defs

open PEqualNP.BicliqueBlockCost in
theorem PEqualNP.Outside.L_meta_18753 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ)) := by
  classical
  intro n G _ T hT
  let S : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter fun v => G.Adj u v ∧ (v ∉ T ∨ u < v)
  let T' : Finset (Fin n) := T.filter fun u => (S u).Nonempty
  let mkStar : Fin n → Block n := fun u => ({u}, S u)
  have hmkInj : Function.Injective mkStar := by
    intro a b hab
    have h1 : ({a} : Finset (Fin n)) = {b} := congrArg Prod.fst hab
    exact Finset.singleton_injective h1
  let F : Finset (Block n) := T'.image mkStar
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    have huS : (S u).Nonempty := (Finset.mem_filter.mp hu).2
    refine ⟨?_, Finset.singleton_nonempty u, huS, ?_⟩
    · rw [Finset.disjoint_singleton_left]
      intro hmem
      exact G.loopless.irrefl u (Finset.mem_filter.mp hmem).2.1
    · intro a ha b hb
      rw [Finset.mem_singleton.mp ha]
      exact (Finset.mem_filter.mp hb).2.1
  · intro a b hab
    have hne : a ≠ b := G.ne_of_adj hab
    rcases hT a b hab with haT | hbT
    · by_cases hbT : b ∈ T
      · rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hbS : b ∈ S a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, Or.inr hlt⟩
          have haT' : a ∈ T' := Finset.mem_filter.mpr ⟨haT, ⟨b, hbS⟩⟩
          exact ⟨mkStar a, Finset.mem_image_of_mem mkStar haT', Or.inl ⟨Finset.mem_singleton_self a, hbS⟩⟩
        · have haS : a ∈ S b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm, Or.inr hgt⟩
          have hbT' : b ∈ T' := Finset.mem_filter.mpr ⟨hbT, ⟨a, haS⟩⟩
          exact ⟨mkStar b, Finset.mem_image_of_mem mkStar hbT', Or.inr ⟨Finset.mem_singleton_self b, haS⟩⟩
      · have hbS : b ∈ S a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, Or.inl hbT⟩
        have haT' : a ∈ T' := Finset.mem_filter.mpr ⟨haT, ⟨b, hbS⟩⟩
        exact ⟨mkStar a, Finset.mem_image_of_mem mkStar haT', Or.inl ⟨Finset.mem_singleton_self a, hbS⟩⟩
    · by_cases haT : a ∈ T
      · rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hbS : b ∈ S a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, Or.inr hlt⟩
          have haT' : a ∈ T' := Finset.mem_filter.mpr ⟨haT, ⟨b, hbS⟩⟩
          exact ⟨mkStar a, Finset.mem_image_of_mem mkStar haT', Or.inl ⟨Finset.mem_singleton_self a, hbS⟩⟩
        · have haS : a ∈ S b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm, Or.inr hgt⟩
          have hbT' : b ∈ T' := Finset.mem_filter.mpr ⟨hbT, ⟨a, haS⟩⟩
          exact ⟨mkStar b, Finset.mem_image_of_mem mkStar hbT', Or.inr ⟨Finset.mem_singleton_self b, haS⟩⟩
      · have haS : a ∈ S b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm, Or.inl haT⟩
        have hbT' : b ∈ T' := Finset.mem_filter.mpr ⟨hbT, ⟨a, haS⟩⟩
        exact ⟨mkStar b, Finset.mem_image_of_mem mkStar hbT', Or.inr ⟨Finset.mem_singleton_self b, haS⟩⟩
  · have hcardF : F.card = T'.card := Finset.card_image_of_injective T' hmkInj
    have hT'le : T'.card ≤ T.card := Finset.card_filter_le _ _
    have hsumF : ∑ p ∈ F, blockCost p = ∑ u ∈ T', (S u).card := by
      rw [Finset.sum_image (fun a _ b _ h => hmkInj h)]
      apply Finset.sum_congr rfl
      intro u _
      simp [mkStar, blockCost]
    have hsumLeT : ∑ u ∈ T', (S u).card ≤ ∑ u ∈ T, (S u).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    let P : Finset (Σ _ : Fin n, Fin n) := T.sigma S
    let f : (Σ _ : Fin n, Fin n) → Sym2 (Fin n) := fun p => s(p.1, p.2)
    have hfInj : Set.InjOn f (P : Set (Σ _ : Fin n, Fin n)) := by
      intro p1 hp1 p2 hp2 hfeq
      have hp1' := Finset.mem_sigma.mp hp1
      have hp2' := Finset.mem_sigma.mp hp2
      have h1 := (Finset.mem_filter.mp hp1'.2).2
      have h2 := (Finset.mem_filter.mp hp2'.2).2
      rcases Sym2.eq_iff.mp hfeq with ⟨h11, h22⟩ | ⟨h12, h21⟩
      · cases p1; cases p2; simp only at h11 h22; subst h11; subst h22; rfl
      · exfalso
        have hp1t : p1.1 ∈ T := hp1'.1
        have hp2t : p2.1 ∈ T := hp2'.1
        have hlt1 : p1.1 < p1.2 := h1.2.resolve_left (by rw [h21]; exact not_not.mpr hp2t)
        have hlt2 : p2.1 < p2.2 := h2.2.resolve_left (by rw [← h12]; exact not_not.mpr hp1t)
        rw [h12, h21] at hlt1
        exact lt_asymm hlt1 hlt2
    have hfSub : P.image f ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      have hp' := Finset.mem_sigma.mp hp
      exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hp'.2).2.1
    have hPcard : ∑ u ∈ T, (S u).card ≤ G.edgeSet.ncard := by
      calc
        ∑ u ∈ T, (S u).card = P.card := (Finset.card_sigma T S).symm
        _ = (P.image f).card := (Finset.card_image_of_injOn hfInj).symm
        _ ≤ G.edgeFinset.card := Finset.card_le_card hfSub
        _ = G.edgeSet.ncard := by
          rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    unfold familyCost
    rw [hsumF, hcardF]
    by_cases hT0 : T.card = 0
    · have hT'0 : T'.card = 0 := by omega
      have hT'e : T' = ∅ := Finset.card_eq_zero.mp hT'0
      rw [hT'e]
      simp
    · omega
