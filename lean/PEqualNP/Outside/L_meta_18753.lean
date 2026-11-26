import PEqualNP.Defs

open PEqualNP.BicliqueBlockCost in
theorem PEqualNP.Outside.L_meta_18753 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ)) := by
  classical
  intro n G dec T cover
  let outgoing (a : Fin n) : Finset (Fin n) :=
    Finset.univ.filter (fun b => G.Adj a b ∧ (b ∉ T ∨ a < b))
  let active := T.filter (fun a => (outgoing a).Nonempty)
  let star (a : Fin n) : Block n := ({a}, outgoing a)
  let family := active.image star
  have arc (a b : Fin n) : b ∈ outgoing a ↔ G.Adj a b ∧ (b ∉ T ∨ a < b) := by
    simp [outgoing]
  have centers (a : Fin n) : a ∈ active ↔ a ∈ T ∧ (outgoing a).Nonempty := by
    simp [active]
  have orient (a b : Fin n) (e : G.Adj a b) :
      (a ∈ T ∧ b ∈ outgoing a) ∨ (b ∈ T ∧ a ∈ outgoing b) := by
    rcases cover a b e with ha | hb
    · by_cases hb : b ∈ T
      · rcases lt_or_gt_of_ne e.ne with hab | hba
        · exact Or.inl ⟨ha, (arc a b).mpr ⟨e,Or.inr hab⟩⟩
        · exact Or.inr ⟨hb, (arc b a).mpr ⟨e.symm,Or.inr hba⟩⟩
      · exact Or.inl ⟨ha,(arc a b).mpr ⟨e,Or.inl hb⟩⟩
    · by_cases ha : a ∈ T
      · rcases lt_or_gt_of_ne e.ne with hab | hba
        · exact Or.inl ⟨ha,(arc a b).mpr ⟨e,Or.inr hab⟩⟩
        · exact Or.inr ⟨hb,(arc b a).mpr ⟨e.symm,Or.inr hba⟩⟩
      · exact Or.inr ⟨hb,(arc b a).mpr ⟨e.symm,Or.inl ha⟩⟩
  have inFam (a b : Fin n) (ha : a ∈ T) (hb : b ∈ outgoing a) : star a ∈ family :=
    Finset.mem_image.mpr ⟨a,(centers a).mpr ⟨ha,b,hb⟩,rfl⟩
  refine ⟨family, ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨?_,by simp [star],((centers a).mp ha).2,?_⟩
    · simp only [star,Finset.disjoint_singleton_left]
      intro h
      exact G.irrefl ((arc a a).mp h).1
    · intro v hv w hw
      have e : v = a := Finset.mem_singleton.mp hv
      subst v
      exact ((arc a w).mp hw).1
  · intro a b e
    rcases orient a b e with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact ⟨star a,inFam a b ha hb,Or.inl ⟨by simp [star],hb⟩⟩
    · exact ⟨star b,inFam b a hb ha,Or.inr ⟨by simp [star],ha⟩⟩
  · have starInj : Function.Injective star := by
      intro a b e
      simpa [star] using congrArg Prod.fst e
    have cardF : family.card ≤ T.card :=
      (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    let S := active.sigma outgoing
    have sCard : S.card = ∑ i ∈ active, (outgoing i).card := Finset.card_sigma _ _
    let f (p : Σ _ : Fin n, Fin n) : Sym2 (Fin n) := s(p.1,p.2)
    have cond (a b : Fin n) (ha : a ∈ active) (hb : b ∈ outgoing a)
        (hbA : b ∈ active) (haB : a ∈ outgoing b) : False := by
      have haT := ((centers a).mp ha).1
      have hbT := ((centers b).mp hbA).1
      have e1 := ((arc a b).mp hb).2.resolve_left (not_not.mpr hbT)
      have e2 := ((arc b a).mp haB).2.resolve_left (not_not.mpr haT)
      exact lt_asymm e1 e2
    have count : S.card ≤ G.edgeFinset.card := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        rw [SetLike.mem_coe] at hx ⊢
        exact G.mem_edgeFinset.mpr (((arc x.1 x.2).mp (Finset.mem_sigma.mp hx).2).1)
      · intro x hx y hy eq
        obtain ⟨a,b⟩ := x
        obtain ⟨c,d⟩ := y
        have eq' : s(a,b) = s(c,d) := eq
        rcases Sym2.eq_iff.mp eq' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · obtain ⟨ha,hb⟩ := Finset.mem_sigma.mp hx
          obtain ⟨hbA,haB⟩ := Finset.mem_sigma.mp hy
          exact (cond _ _ ha hb hbA haB).elim
    rw [sCard] at count
    change (∑ p ∈ family, blockCost p) + (family.card - 1) ≤ _ 
    have total : (∑ p ∈ family, blockCost p) = ∑ a ∈ active, (outgoing a).card := by
      unfold family
      rw [Finset.sum_image starInj.injOn]
      simp [star,blockCost]
    rw [total]
    have en : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard]
    rw [en]
    by_cases z : family.card = 0
    · have em : family = ∅ := Finset.card_eq_zero.mp z
      rw [← total,em]
      simp
    · omega

