import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_554_aux

lemma hall_marriage {α β : Type*} [DecidableEq α] [DecidableEq β] :
    ∀ (n : ℕ) (I : Finset α) (N : α → Finset β),
      I.card = n →
      (∀ S ⊆ I, S.card ≤ (S.biUnion N).card) →
      ∃ f : {i : α // i ∈ I} → β, Function.Injective f ∧ ∀ i, f i ∈ N i.val := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro I N hI hhall
    by_cases hn0 : n = 0
    · subst hn0
      have hIe : I = ∅ := Finset.card_eq_zero.mp hI
      refine ⟨fun i => False.elim (by rw [hIe] at i; exact Finset.notMem_empty i.val i.property), ?_, ?_⟩
      · intro a; rw [hIe] at a; exact False.elim (Finset.notMem_empty a.val a.property)
      · intro a; rw [hIe] at a; exact False.elim (Finset.notMem_empty a.val a.property)
    · by_cases htight : ∃ T ⊆ I, T.Nonempty ∧ T.card < I.card ∧ (T.biUnion N).card = T.card
      · rcases htight with ⟨T, hTI, hTne, hTlt, hTeq⟩
        let U := T.biUnion N
        let I' := I \ T
        let N' : α → Finset β := fun i => N i \ U
        have hTlt_n : T.card < n := by omega
        have hhallT : ∀ S ⊆ T, S.card ≤ (S.biUnion N).card :=
          fun S hST => hhall S (Finset.Subset.trans hST hTI)
        obtain ⟨f1, hf1_inj, hf1_mem⟩ := ih T.card hTlt_n T N rfl hhallT
        have hI'_card : I'.card = n - T.card := by
          dsimp only [I']
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTI, hI]
        have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
        have hI'lt_n : I'.card < n := by omega
        have hhall' : ∀ S ⊆ I', S.card ≤ (S.biUnion N').card := by
          intro S hSI'
          have hdisjST : Disjoint S T := by
            rw [Finset.disjoint_left]
            intro a haS haT
            exact (Finset.mem_sdiff.mp (hSI' haS)).2 haT
          have hsub : S ∪ T ⊆ I := Finset.union_subset (Finset.Subset.trans hSI' Finset.sdiff_subset) hTI
          have h1 := hhall (S ∪ T) hsub
          rw [Finset.card_union_of_disjoint hdisjST] at h1
          have hbiu : (S ∪ T).biUnion N = (S.biUnion N') ∪ U := by
            ext b
            simp only [Finset.mem_biUnion, Finset.mem_union, N', U, Finset.mem_sdiff]
            constructor
            · rintro ⟨a, haS | haT, hba⟩
              · by_cases hbU : b ∈ T.biUnion N
                · right; exact Finset.mem_biUnion.mp hbU
                · left; exact ⟨a, haS, hba, fun h => hbU (Finset.mem_biUnion.mpr h)⟩
              · right; exact ⟨a, haT, hba⟩
            · rintro (⟨a, haS, hba, _⟩ | ⟨a, haT, hba⟩)
              · exact ⟨a, Or.inl haS, hba⟩
              · exact ⟨a, Or.inr haT, hba⟩
          have hdisjU : Disjoint (S.biUnion N') U := by
            rw [Finset.disjoint_left]
            intro b hb1 hb2
            rcases Finset.mem_biUnion.mp hb1 with ⟨a, _, hba⟩
            exact (Finset.mem_sdiff.mp hba).2 hb2
          rw [hbiu, Finset.card_union_of_disjoint hdisjU] at h1
          dsimp only [U] at h1
          omega
        obtain ⟨f2, hf2_inj, hf2_mem⟩ := ih I'.card hI'lt_n I' N' rfl hhall'
        let f : {i : α // i ∈ I} → β := fun i =>
          if h : i.val ∈ T then f1 ⟨i.val, h⟩
          else f2 ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, h⟩⟩
        have hf1_inU : ∀ i : {i : α // i ∈ T}, f1 i ∈ U := by
          intro i
          exact Finset.mem_biUnion.mpr ⟨i.val, i.property, hf1_mem i⟩
        have hf2_notU : ∀ i : {i : α // i ∈ I'}, f2 i ∉ U := by
          intro i
          exact (Finset.mem_sdiff.mp (hf2_mem i)).2
        refine ⟨f, ?_, ?_⟩
        · intro a b hab
          dsimp only [f] at hab
          by_cases ha : a.val ∈ T <;> by_cases hb : b.val ∈ T
          · simp only [ha, hb, ↓reduceDIte] at hab
            have h := hf1_inj hab
            have hv := congrArg Subtype.val h
            exact Subtype.ext hv
          · simp only [ha, hb, ↓reduceDIte] at hab
            exact False.elim (hf2_notU ⟨b.val, Finset.mem_sdiff.mpr ⟨b.property, hb⟩⟩
              (hab ▸ hf1_inU ⟨a.val, ha⟩))
          · simp only [ha, hb, ↓reduceDIte] at hab
            exact False.elim (hf2_notU ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩
              (hab.symm ▸ hf1_inU ⟨b.val, hb⟩))
          · simp only [ha, hb, ↓reduceDIte] at hab
            have h := hf2_inj hab
            have hv := congrArg Subtype.val h
            exact Subtype.ext hv
        · intro a
          dsimp only [f]
          by_cases ha : a.val ∈ T
          · simp only [ha, ↓reduceDIte]
            exact hf1_mem ⟨a.val, ha⟩
          · simp only [ha, ↓reduceDIte]
            exact (Finset.mem_sdiff.mp (hf2_mem ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩)).1
      · have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
        rcases hIne with ⟨i0, hi0⟩
        have hN0_pos : 0 < (N i0).card := by
          have h1 := hhall {i0} (Finset.singleton_subset_iff.mpr hi0)
          simp only [Finset.card_singleton, Finset.singleton_biUnion] at h1
          omega
        rcases Finset.card_pos.mp hN0_pos with ⟨j0, hj0⟩
        let I' := I.erase i0
        let N' : α → Finset β := fun i => (N i).erase j0
        have hI'_card : I'.card = n - 1 := by
          dsimp only [I']
          rw [Finset.card_erase_of_mem hi0, hI]
        have hI'lt_n : I'.card < n := by omega
        have hhall' : ∀ S ⊆ I', S.card ≤ (S.biUnion N').card := by
          intro S hSI'
          by_cases hSne : S.Nonempty
          · have hSI : S ⊆ I := Finset.Subset.trans hSI' (Finset.erase_subset i0 I)
            have hSlt : S.card < I.card := by
              have hle := Finset.card_le_card hSI'
              omega
            have hle_biu := hhall S hSI
            have hne_eq : (S.biUnion N).card ≠ S.card := fun heq =>
              htight ⟨S, hSI, hSne, hSlt, heq⟩
            have hbiu_eq : S.biUnion N' = (S.biUnion N).erase j0 := by
              ext b
              simp only [Finset.mem_biUnion, Finset.mem_erase, N']
              constructor
              · rintro ⟨a, haS, hne, hba⟩
                exact ⟨hne, a, haS, hba⟩
              · rintro ⟨hne, a, haS, hba⟩
                exact ⟨a, haS, hne, hba⟩
            rw [hbiu_eq]
            have hcard_er : (S.biUnion N).card - 1 ≤ ((S.biUnion N).erase j0).card := by
              by_cases hj : j0 ∈ S.biUnion N
              · rw [Finset.card_erase_of_mem hj]
              · rw [Finset.erase_eq_of_notMem hj]; omega
            omega
          · rw [Finset.not_nonempty_iff_eq_empty.mp hSne]
            simp
        obtain ⟨f', hf'_inj, hf'_mem⟩ := ih I'.card hI'lt_n I' N' rfl hhall'
        let f : {i : α // i ∈ I} → β := fun i =>
          if h : i.val = i0 then j0
          else f' ⟨i.val, Finset.mem_erase.mpr ⟨h, i.property⟩⟩
        refine ⟨f, ?_, ?_⟩
        · intro a b hab
          dsimp only [f] at hab
          by_cases ha : a.val = i0 <;> by_cases hb : b.val = i0
          · exact Subtype.ext (ha.trans hb.symm)
          · simp only [ha, hb, ↓reduceDIte] at hab
            have hne := (Finset.mem_erase.mp (hf'_mem ⟨b.val, Finset.mem_erase.mpr ⟨hb, b.property⟩⟩)).1
            exact False.elim (hne hab.symm)
          · simp only [ha, hb, ↓reduceDIte] at hab
            have hne := (Finset.mem_erase.mp (hf'_mem ⟨a.val, Finset.mem_erase.mpr ⟨ha, a.property⟩⟩)).1
            exact False.elim (hne hab)
          · simp only [ha, hb, ↓reduceDIte] at hab
            have h := hf'_inj hab
            have hv := congrArg Subtype.val h
            exact Subtype.ext hv
        · intro a
          dsimp only [f]
          by_cases ha : a.val = i0
          · simp only [ha, ↓reduceDIte]
            exact hj0
          · simp only [ha, ↓reduceDIte]
            exact (Finset.mem_erase.mp (hf'_mem ⟨a.val, Finset.mem_erase.mpr ⟨ha, a.property⟩⟩)).2

lemma depends_on_common {m k p : ℕ} (need : Fin m → Finset (Fin p)) (view : Fin p → Finset (Fin k))
    (D : (Fin k → Bool) → Fin m → Bool)
    (hdec : ∀ (i : Fin m) (o : Fin p), o ∈ need i →
      ∀ x y : Fin k → Bool, (∀ j ∈ view o, x j = y j) → D x i = D y i)
    (i : Fin m) :
    ∀ (s : Finset (Fin k)) (x y : Fin k → Bool),
      (∀ j, x j ≠ y j → j ∈ s) →
      (∀ j ∈ s, j ∉ Finset.univ.filter (fun j : Fin k => ∀ o ∈ need i, j ∈ view o)) →
      D x i = D y i := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hdiff _
    have hxy : x = y := by
      funext j
      by_contra hne
      exact Finset.notMem_empty j (hdiff j hne)
    rw [hxy]
  | insert a s ha ih =>
    intro x y hdiff hnot
    let z : Fin k → Bool := fun j => if j = a then y a else x j
    have ha_not : a ∉ Finset.univ.filter (fun j : Fin k => ∀ o ∈ need i, j ∈ view o) :=
      hnot a (Finset.mem_insert_self a s)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at ha_not
    rcases ha_not with ⟨o, ho_need, ha_not_view⟩
    have hxz : D x i = D z i := by
      apply hdec i o ho_need x z
      intro j hj
      have hja : j ≠ a := fun h => ha_not_view (h ▸ hj)
      simp [z, hja]
    have hzy : D z i = D y i := by
      apply ih z y
      · intro j hne
        have hja : j ≠ a := by
          intro h; subst h; exact hne (by simp [z])
        have hxyj : x j ≠ y j := by
          simpa [z, hja] using hne
        rcases Finset.mem_insert.mp (hdiff j hxyj) with rfl | hjs
        · exact False.elim (hja rfl)
        · exact hjs
      · intro j hjs
        exact hnot j (Finset.mem_insert_of_mem hjs)
    exact hxz.trans hzy

end PEqualNP.Outside.L_lib_554_aux

theorem PEqualNP.Outside.L_lib_554 : (∀ (m k p : ℕ) (need : Fin m → Finset (Fin p)) (view : Fin p → Finset (Fin k)),
  let common := fun i : Fin m => Finset.univ.filter
    (fun j : Fin k => ∀ o ∈ need i, j ∈ view o)
  let same := fun (S : Finset (Fin k)) (x y : Fin k → Bool) => ∀ j ∈ S, x j = y j
  let decodable := fun D : (Fin k → Bool) → Fin m → Bool =>
    ∀ (i : Fin m) (o : Fin p), o ∈ need i → ∀ x y, same (view o) x y → D x i = D y i
  (∀ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D → decodable D →
    (∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i) ∧
    ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card) ∧
  ((∃ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D ∧ decodable D) ↔
    ∃ f : Fin m ↪ Fin k, ∀ i, f i ∈ common i)) := by
  intro m k p need view common same decodable
  have hpart1 : ∀ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D → decodable D →
      (∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i) ∧
      ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card := by
    intro D hsurj hdec
    have hdep : ∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i := by
      intro i x y hsame
      let s := Finset.univ.filter (fun j : Fin k => x j ≠ y j)
      refine PEqualNP.Outside.L_lib_554_aux.depends_on_common need view D hdec i s x y ?_ ?_
      · intro j hne
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
      · intro j hjs hjc
        exact (Finset.mem_filter.mp hjs).2 (hsame j hjc)
    refine ⟨hdep, ?_⟩
    intro S
    let U := S.biUnion common
    let evalS : ({j : Fin k // j ∈ U} → Bool) → ({i : Fin m // i ∈ S} → Bool) :=
      fun g i => D (fun j => if h : j ∈ U then g ⟨j, h⟩ else false) i.val
    have hsurjS : Function.Surjective evalS := by
      intro target
      let y : Fin m → Bool := fun i => if h : i ∈ S then target ⟨i, h⟩ else false
      obtain ⟨x, hx⟩ := hsurj y
      refine ⟨fun j => x j.val, ?_⟩
      funext i
      dsimp only [evalS]
      have hsame : same (common i.val) (fun j => if h : j ∈ U then x j else false) x := by
        intro j hj
        have hjU : j ∈ U := Finset.mem_biUnion.mpr ⟨i.val, i.property, hj⟩
        simp [hjU]
      rw [hdep i.val _ x hsame, hx]
      simp [y, i.property]
    have hcard_le : Fintype.card ({i : Fin m // i ∈ S} → Bool) ≤
        Fintype.card ({j : Fin k // j ∈ U} → Bool) :=
      Fintype.card_le_of_surjective evalS hsurjS
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hcard_le
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard_le
  refine ⟨hpart1, ?_⟩
  constructor
  · rintro ⟨D, hsurj, hdec⟩
    have hhall : ∀ S ⊆ (Finset.univ : Finset (Fin m)), S.card ≤ (S.biUnion common).card :=
      fun S _ => (hpart1 D hsurj hdec).2 S
    obtain ⟨f, hf_inj, hf_mem⟩ :=
      PEqualNP.Outside.L_lib_554_aux.hall_marriage m (Finset.univ : Finset (Fin m)) common
        (by simp) hhall
    refine ⟨⟨fun i => f ⟨i, Finset.mem_univ i⟩, ?_⟩, fun i => hf_mem ⟨i, Finset.mem_univ i⟩⟩
    intro i1 i2 h
    exact congrArg Subtype.val (hf_inj h)
  · rintro ⟨f, hf⟩
    let D : (Fin k → Bool) → Fin m → Bool := fun x i => x (f i)
    refine ⟨D, ?_, ?_⟩
    · intro target
      classical
      let x : Fin k → Bool := fun j =>
        if h : ∃ i : Fin m, f i = j then target (Classical.choose h) else false
      refine ⟨x, ?_⟩
      funext i
      have hex : ∃ i' : Fin m, f i' = f i := ⟨i, rfl⟩
      have hch : Classical.choose hex = i := f.injective (Classical.choose_spec hex)
      change x (f i) = target i
      dsimp only [x]
      simp only [hex, ↓reduceDIte, hch]
    · intro i o ho x y hsame
      have hfi : f i ∈ view o := (Finset.mem_filter.mp (hf i)).2 o ho
      exact hsame (f i) hfi
