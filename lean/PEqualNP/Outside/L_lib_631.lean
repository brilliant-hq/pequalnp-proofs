import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_631_aux

lemma trim_buckets {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (g : ℕ) :
    ∀ (S : Finset α),
      (∀ i ∈ S, 2 ≤ (B i).card) →
      g ≤ ∑ i ∈ S, ((B i).card - 1) →
      ∃ (I : Finset α) (B' : α → Finset β),
        I ⊆ S ∧
        (∀ i ∈ I, B' i ⊆ B i ∧ 2 ≤ (B' i).card) ∧
        ∑ i ∈ I, ((B' i).card - 1) = g := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ hg
    simp only [Finset.sum_empty, Nat.le_zero] at hg
    exact ⟨∅, B, Finset.Subset.refl _, by simp, by simp [hg]⟩
  | insert a s ha ih =>
    intro h2 hg
    rw [Finset.sum_insert ha] at hg
    by_cases hle : g ≤ ∑ i ∈ s, ((B i).card - 1)
    · obtain ⟨I, B', hIs, hsub, hsum⟩ :=
        ih (fun i hi => h2 i (Finset.mem_insert_of_mem hi)) hle
      exact ⟨I, B', Finset.Subset.trans hIs (Finset.subset_insert a s), hsub, hsum⟩
    · let rem := ∑ i ∈ s, ((B i).card - 1)
      let need := g - rem
      have hBa : 2 ≤ (B a).card := h2 a (Finset.mem_insert_self a s)
      have hneed_le : need + 1 ≤ (B a).card := by dsimp only [need, rem] at *; omega
      obtain ⟨Ba', hBa'_sub, hBa'_card⟩ := Finset.exists_subset_card_eq hneed_le
      let B' : α → Finset β := fun i => if i = a then Ba' else B i
      refine ⟨insert a s, B', Finset.Subset.refl _, ?_, ?_⟩
      · intro i hi
        dsimp only [B']
        rcases Finset.mem_insert.mp hi with rfl | his
        · simp only [↓reduceIte]
          exact ⟨hBa'_sub, by dsimp only [need, rem] at hBa'_card ⊢; omega⟩
        · have hne : i ≠ a := fun h => ha (h ▸ his)
          simp only [hne, ↓reduceIte]
          exact ⟨Finset.Subset.refl _, h2 i (Finset.mem_insert_of_mem his)⟩
      · rw [Finset.sum_insert ha]
        have hBa' : (B' a).card = need + 1 := by simp [B', hBa'_card]
        have hrest : (∑ i ∈ s, ((B' i).card - 1)) = rem := by
          dsimp only [rem]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hne : i ≠ a := fun h => ha (h ▸ hi)
          simp [B', hne]
        rw [hBa', hrest]
        dsimp only [need, rem] at *
        omega

end PEqualNP.Outside.L_lib_631_aux

theorem PEqualNP.Outside.L_lib_631 : (∀ (q m h t : Nat), 0 < q →
  let A := Fin (m+h)
  let W := Fin m → Fin q
  ∀ label : Fin m → A → Fin q,
    let live := fun (x : W) =>
      ((Finset.univ : Finset A).filter (fun a => ∀ i, x i ≠ label i a)).card
    let cert := fun (w : W) (I : Finset (Fin m)) (bucket : Fin m → Finset A) =>
      I.card ≤ h-t ∧ (I.biUnion bucket).card = I.card + (h-t) ∧
      (∀ i ∈ I, 2 ≤ (bucket i).card ∧ ∀ a ∈ bucket i, label i a = w i) ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (bucket i) (bucket j)
    (∀ x : W, live x ≤ t → ∃ I bucket, cert x I bucket) ∧
    ∀ (word : W) I bucket, cert word I bucket →
      ∃ y : W, (∀ j ∈ I, y j = word j) ∧ live y ≤ t) := by
  intro q m h t hq A W label live cert
  constructor
  · intro x hlive
    by_cases hg0 : h - t = 0
    · refine ⟨∅, fun _ => ∅, ?_, ?_, ?_, ?_⟩
      · simp [hg0]
      · simp [hg0]
      · simp
      · simp
    · classical
      let killed := (Finset.univ : Finset A).filter (fun a => ∃ i : Fin m, x i = label i a)
      let liveSet := (Finset.univ : Finset A).filter (fun a => ∀ i : Fin m, x i ≠ label i a)
      have hdisj_kl : Disjoint killed liveSet := by
        rw [Finset.disjoint_left]
        intro a hk hl
        rcases (Finset.mem_filter.mp hk).2 with ⟨i, hi⟩
        exact (Finset.mem_filter.mp hl).2 i hi
      have hun_kl : killed ∪ liveSet = Finset.univ := by
        ext a
        simp only [killed, liveSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hex : ∃ i : Fin m, x i = label i a
        · exact iff_true_intro (Or.inl hex)
        · exact iff_true_intro (Or.inr fun i hi => hex ⟨i, hi⟩)
      have hcard_kl : killed.card + liveSet.card = m + h := by
        rw [← Finset.card_union_of_disjoint hdisj_kl, hun_kl, Finset.card_univ, Fintype.card_fin]
      have hkilled_ge : m + (h - t) ≤ killed.card := by
        change liveSet.card ≤ t at hlive
        omega
      let hit : A → Fin m := fun a =>
        if h : ∃ i : Fin m, x i = label i a then Classical.choose h
        else ⟨0, by
          by_contra hm0
          have hm : m = 0 := by omega
          subst hm
          have hk0 : killed = ∅ := by
            ext b
            simp only [killed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            rintro ⟨i, _⟩
            exact Fin.elim0 i
          rw [hk0, Finset.card_empty] at hkilled_ge
          omega⟩
      have hhit_spec : ∀ a ∈ killed, label (hit a) a = x (hit a) := by
        intro a ha
        have hex : ∃ i : Fin m, x i = label i a := (Finset.mem_filter.mp ha).2
        dsimp only [hit]
        simp only [hex, ↓reduceDIte]
        exact (Classical.choose_spec hex).symm
      let B0 : Fin m → Finset A := fun i => killed.filter (fun a => hit a = i)
      have hB0_disj : ∀ i j : Fin m, i ≠ j → Disjoint (B0 i) (B0 j) := by
        intro i j hij
        rw [Finset.disjoint_left]
        intro a hi hj
        have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hj).2
        exact hij (h1.symm.trans h2)
      have hB0_sum : (∑ i : Fin m, (B0 i).card) = killed.card := by
        have hbiu : (Finset.univ : Finset (Fin m)).biUnion B0 = killed := by
          ext a
          simp only [B0, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          constructor
          · rintro ⟨_, ha, _⟩; exact ha
          · intro ha; exact ⟨hit a, ha, rfl⟩
        rw [← hbiu, Finset.card_biUnion (fun i _ j _ hij => hB0_disj i j hij)]
      let J := (Finset.univ : Finset (Fin m)).filter (fun i => 2 ≤ (B0 i).card)
      have hJ_sum : h - t ≤ ∑ i ∈ J, ((B0 i).card - 1) := by
        have h1 : (∑ i : Fin m, (B0 i).card) ≤ (∑ i : Fin m, ((B0 i).card - 1)) + m := by
          have hle : ∑ i : Fin m, (B0 i).card ≤ ∑ i : Fin m, (((B0 i).card - 1) + 1) :=
            Finset.sum_le_sum (fun i _ => by omega)
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
              mul_one] at hle
          exact hle
        have h2 : (∑ i : Fin m, ((B0 i).card - 1)) = ∑ i ∈ J, ((B0 i).card - 1) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ J)
          intro i _ hiJ
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hiJ
          omega
        omega
      obtain ⟨I, B', hIJ, hB'_spec, hB'_sum⟩ :=
        PEqualNP.Outside.L_lib_631_aux.trim_buckets B0 (h - t) J
          (fun i hi => (Finset.mem_filter.mp hi).2) hJ_sum
      have hB'_disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B' i) (B' j) := by
        intro i hi j hj hij
        exact Disjoint.mono (hB'_spec i hi).1 (hB'_spec j hj).1 (hB0_disj i j hij)
      refine ⟨I, B', ?_, ?_, ?_, hB'_disj⟩
      · have hle : I.card ≤ ∑ i ∈ I, ((B' i).card - 1) := by
          calc I.card = ∑ _i ∈ I, 1 := by simp
            _ ≤ ∑ i ∈ I, ((B' i).card - 1) :=
              Finset.sum_le_sum (fun i hi => by have := (hB'_spec i hi).2; omega)
        omega
      · rw [Finset.card_biUnion (fun i hi j hj hij => hB'_disj i hi j hj hij)]
        have hsplit : (∑ i ∈ I, (B' i).card) = (∑ i ∈ I, ((B' i).card - 1)) + I.card := by
          have heq : ∑ i ∈ I, (B' i).card = ∑ i ∈ I, (((B' i).card - 1) + 1) :=
            Finset.sum_congr rfl (fun i hi => by have := (hB'_spec i hi).2; omega)
          rw [heq, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        omega
      · intro i hi
        refine ⟨(hB'_spec i hi).2, fun a ha => ?_⟩
        have ha0 := (hB'_spec i hi).1 ha
        rcases Finset.mem_filter.mp ha0 with ⟨hak, hhit⟩
        rw [← hhit]
        exact hhit_spec a hak
  · intro word I bucket hcert
    rcases hcert with ⟨_, hU_card, hB_spec, _⟩
    let U := I.biUnion bucket
    let RemI := (Finset.univ : Finset (Fin m)) \ I
    let RemA := (Finset.univ : Finset A) \ U
    have hRemI_card : RemI.card = m - I.card := by
      dsimp only [RemI]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hRemA_card : RemA.card = m + h - U.card := by
      dsimp only [RemA]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    let k := min RemI.card RemA.card
    obtain ⟨SI, hSI_sub, hSI_card⟩ := Finset.exists_subset_card_eq (Nat.min_le_left RemI.card RemA.card)
    obtain ⟨SA, hSA_sub, hSA_card⟩ := Finset.exists_subset_card_eq (Nat.min_le_right RemI.card RemA.card)
    have hcard_eq : Fintype.card {i : Fin m // i ∈ SI} = Fintype.card {a : A // a ∈ SA} := by
      simp [Fintype.card_coe, hSI_card, hSA_card]
    obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard_eq
    let y : W := fun j =>
      if j ∈ I then word j
      else if hj : j ∈ SI then label j (e ⟨j, hj⟩).val
      else ⟨0, hq⟩
    refine ⟨y, ?_, ?_⟩
    · intro j hj; simp [y, hj]
    · have hsub_live : (Finset.univ : Finset A).filter (fun a => ∀ i : Fin m, y i ≠ label i a) ⊆ RemA \ SA := by
        intro a ha
        have hall := (Finset.mem_filter.mp ha).2
        have ha_notU : a ∉ U := by
          intro haU
          rcases Finset.mem_biUnion.mp haU with ⟨i, hiI, hai⟩
          have hlab := (hB_spec i hiI).2 a hai
          have hyi : y i = word i := by simp [y, hiI]
          exact hall i (hyi.trans hlab.symm)
        have ha_notSA : a ∉ SA := by
          intro haSA
          let p := e.symm ⟨a, haSA⟩
          have hp_notI : p.val ∉ I := (Finset.mem_sdiff.mp (hSI_sub p.property)).2
          have hyp : y p.val = label p.val a := by
            dsimp only [y]
            simp only [hp_notI, ↓reduceIte, p.property, ↓reduceDIte]
            have heq : (e p).val = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, haSA⟩)
            rw [heq]
          exact hall p.val hyp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha_notU⟩, ha_notSA⟩
      have hcard_diff : (RemA \ SA).card = RemA.card - k := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSA_sub, hSA_card]
      have hle := Finset.card_le_card hsub_live
      rw [hcard_diff] at hle
      change ((Finset.univ : Finset A).filter (fun a => ∀ i : Fin m, y i ≠ label i a)).card ≤ t
      dsimp only [U] at hRemA_card
      dsimp only [k] at hle
      omega
