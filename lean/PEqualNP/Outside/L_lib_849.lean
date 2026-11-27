import Mathlib

namespace PEqualNP.Outside.L_lib_849_aux

open scoped BigOperators

private noncomputable def partsClass {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (v : (↑S : Set V)) : Finset V := by
  classical
  exact (S.attach.filter (fun u => (G.induce (↑S : Set V)).Reachable v u)).image Subtype.val

private noncomputable def parts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact S.attach.image (fun v =>
    (S.attach.filter (fun u => (G.induce (↑S : Set V)).Reachable v u)).image Subtype.val)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem mem_partsClass {S : Finset V} {v : (↑S : Set V)} {x : V} :
    x ∈ partsClass G S v ↔ ∃ hx : x ∈ S, (G.induce (↑S : Set V)).Reachable v ⟨x, hx⟩ := by
  classical
  simp only [partsClass, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨_, h⟩, rfl⟩
    exact ⟨hu, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, ⟨Finset.mem_attach _ _, h⟩, rfl⟩

private theorem self_mem_partsClass {S : Finset V} (v : (↑S : Set V)) :
    v.val ∈ partsClass G S v :=
  mem_partsClass.mpr ⟨v.property, .rfl⟩

private theorem mem_parts {S C : Finset V} :
    C ∈ parts G S ↔ ∃ v : (↑S : Set V), partsClass G S v = C := by
  classical
  change C ∈ S.attach.image (partsClass G S) ↔ _
  rw [Finset.mem_image]
  exact ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩, fun ⟨v, h⟩ => ⟨v, Finset.mem_attach _ _, h⟩⟩

private theorem partsClass_eq {S : Finset V} {v w : (↑S : Set V)}
    (h : (G.induce (↑S : Set V)).Reachable v w) : partsClass G S v = partsClass G S w := by
  ext x
  simp only [mem_partsClass]
  exact ⟨fun ⟨hx, hvx⟩ => ⟨hx, h.symm.trans hvx⟩,
    fun ⟨hx, hwx⟩ => ⟨hx, h.trans hwx⟩⟩

private theorem parts_subset {S C : Finset V} (hC : C ∈ parts G S) : C ⊆ S := by
  obtain ⟨v, rfl⟩ := mem_parts.mp hC
  intro x hx
  exact (mem_partsClass.mp hx).choose

private theorem parts_nonempty {S C : Finset V} (hC : C ∈ parts G S) : C.Nonempty := by
  obtain ⟨v, rfl⟩ := mem_parts.mp hC
  exact ⟨v.val, self_mem_partsClass v⟩

private theorem parts_disjoint {S C D : Finset V} (hC : C ∈ parts G S) (hD : D ∈ parts G S)
    (hCD : C ≠ D) : Disjoint C D := by
  obtain ⟨v, rfl⟩ := mem_parts.mp hC
  obtain ⟨w, rfl⟩ := mem_parts.mp hD
  refine Finset.disjoint_left.mpr fun x hx hy => hCD ?_
  obtain ⟨_, hvx⟩ := mem_partsClass.mp hx
  obtain ⟨_, hwx⟩ := mem_partsClass.mp hy
  exact partsClass_eq (hvx.trans hwx.symm)

private theorem parts_cover (G : SimpleGraph V) (S : Finset V) : (parts G S).biUnion id = S := by
  ext x
  simp only [Finset.mem_biUnion, id_eq]
  exact ⟨fun ⟨_, hC, hx⟩ => parts_subset hC hx, fun hx =>
    ⟨partsClass G S ⟨x, hx⟩, mem_parts.mpr ⟨⟨x, hx⟩, rfl⟩, self_mem_partsClass ⟨x, hx⟩⟩⟩

omit [DecidableEq V] in
private theorem induced_reachable_mono {A B : Finset V} (hAB : A ⊆ B)
    {a b : (↑A : Set V)} (h : (G.induce (↑A : Set V)).Reachable a b) :
    (G.induce (↑B : Set V)).Reachable ⟨a.val, hAB a.property⟩ ⟨b.val, hAB b.property⟩ :=
  h.map (G.induceHomOfLE (show (↑A : Set V) ⊆ ↑B from hAB)).toHom

-- A class does not change when the walk is restricted to a set containing its entire support.
private theorem partsClass_eq_of_closed {A B : Finset V} (hAB : A ⊆ B)
    {v : V} (hv : v ∈ A)
    (hclosed : ∀ u : (↑B : Set V),
      (G.induce (↑B : Set V)).Reachable ⟨v, hAB hv⟩ u → u.val ∈ A) :
    partsClass G A ⟨v, hv⟩ = partsClass G B ⟨v, hAB hv⟩ := by
  ext x
  rw [mem_partsClass, mem_partsClass]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hAB hx, induced_reachable_mono hAB h⟩
  · rintro ⟨hx, ⟨p⟩⟩
    refine ⟨hclosed ⟨x, hx⟩ p.reachable, ?_⟩
    let f : G.induce (↑B : Set V) →g G := (SimpleGraph.Embedding.induce _).toHom
    refine ⟨(p.map f).induce (↑A : Set V) ?_⟩
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact hclosed w (p.reachable_of_mem_support p.start_mem_support hw)

private theorem partsClass_outside {S C : Finset V} (hC : C ∈ parts G S)
    {v : V} (hv : v ∈ S \ C) :
    partsClass G (S \ C) ⟨v, hv⟩ = partsClass G S ⟨v, (Finset.mem_sdiff.mp hv).1⟩ := by
  obtain ⟨w, rfl⟩ := mem_parts.mp hC
  apply partsClass_eq_of_closed (fun _ h => (Finset.mem_sdiff.mp h).1) hv
  intro u h
  refine Finset.mem_sdiff.mpr ⟨u.property, fun hu => (Finset.mem_sdiff.mp hv).2 ?_⟩
  obtain ⟨_, hwu⟩ := mem_partsClass.mp hu
  exact mem_partsClass.mpr ⟨_, hwu.trans h.symm⟩

private theorem parts_sdiff {S C : Finset V} (hC : C ∈ parts G S) :
    parts G (S \ C) = (parts G S).erase C := by
  ext D
  rw [Finset.mem_erase]
  constructor
  · intro hD
    obtain ⟨v, rfl⟩ := mem_parts.mp hD
    refine ⟨?_, mem_parts.mpr ⟨⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩,
      (partsClass_outside hC v.property).symm⟩⟩
    intro he
    apply (Finset.mem_sdiff.mp v.property).2
    exact Eq.mp (congrArg (fun E : Finset V => v.val ∈ E) he) (self_mem_partsClass v)
  · rintro ⟨hDC, hD⟩
    have hd := parts_disjoint hD hC hDC
    obtain ⟨v, rfl⟩ := mem_parts.mp hD
    have hv : v.val ∈ S \ C := Finset.mem_sdiff.mpr
      ⟨v.property, fun hc => Finset.disjoint_left.mp hd (self_mem_partsClass v) hc⟩
    exact mem_parts.mpr ⟨⟨v.val, hv⟩, partsClass_outside hC hv⟩

private theorem parts_replace {V : Type*} [DecidableEq V] (G : SimpleGraph V) {S C T : Finset V}
    (hC : C ∈ parts G S) (hT : T ⊆ C) :
    parts G ((S \ C) ∪ T) = ((parts G S).erase C) ∪ parts G T := by
  let A := S \ C
  let R := A ∪ T
  have hAR : A ⊆ R := fun _ h => Finset.mem_union_left _ h
  have hTR : T ⊆ R := fun _ h => Finset.mem_union_right _ h
  have hRS : R ⊆ S := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (Finset.mem_sdiff.mp h).1
    · exact parts_subset hC (hT h)
  have hstay {v u : (↑R : Set V)} (h : (G.induce (↑R : Set V)).Reachable v u) :
      v.val ∈ C ↔ u.val ∈ C := by
    obtain ⟨w, rfl⟩ := mem_parts.mp hC
    have h' := induced_reachable_mono hRS h
    constructor
    · intro hv
      obtain ⟨_, hwv⟩ := mem_partsClass.mp hv
      exact mem_partsClass.mpr ⟨_, hwv.trans h'⟩
    · intro hu
      obtain ⟨_, hwu⟩ := mem_partsClass.mp hu
      exact mem_partsClass.mpr ⟨_, hwu.trans h'.symm⟩
  have hA {v : V} (hv : v ∈ A) :
      partsClass G A ⟨v, hv⟩ = partsClass G R ⟨v, hAR hv⟩ := by
    apply partsClass_eq_of_closed hAR hv
    intro u hu
    exact Finset.mem_sdiff.mpr ⟨hRS u.property, fun hc =>
      (Finset.mem_sdiff.mp hv).2 ((hstay hu).mpr hc)⟩
  have hT' {v : V} (hv : v ∈ T) :
      partsClass G T ⟨v, hv⟩ = partsClass G R ⟨v, hTR hv⟩ := by
    apply partsClass_eq_of_closed hTR hv
    intro u hu
    rcases Finset.mem_union.mp u.property with ha | ht
    · exact False.elim ((Finset.mem_sdiff.mp ha).2 ((hstay hu).mp (hT hv)))
    · exact ht
  change parts G R = ((parts G S).erase C) ∪ parts G T
  rw [← parts_sdiff hC]
  ext D
  rw [Finset.mem_union]
  constructor
  · intro hD
    obtain ⟨v, rfl⟩ := mem_parts.mp hD
    rcases Finset.mem_union.mp v.property with ha | ht
    · exact Or.inl (mem_parts.mpr ⟨⟨v.val, ha⟩, hA ha⟩)
    · exact Or.inr (mem_parts.mpr ⟨⟨v.val, ht⟩, hT' ht⟩)
  · rintro (hD | hD)
    · obtain ⟨v, rfl⟩ := mem_parts.mp hD
      exact mem_parts.mpr ⟨⟨v.val, hAR v.property⟩, (hA v.property).symm⟩
    · obtain ⟨v, rfl⟩ := mem_parts.mp hD
      exact mem_parts.mpr ⟨⟨v.val, hTR v.property⟩, (hT' v.property).symm⟩

private lemma rank_le_add_card {ι V : Type*} [DecidableEq V] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (D W : Submodule (ZMod 2) V)
    (B : Finset ι) (f : ι → V)
    (hle : W ≤ D ⊔ Submodule.span (ZMod 2) (↑(B.image f) : Set V)) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) D + B.card := by
  classical
  let E := Submodule.span (ZMod 2) (↑(B.image f) : Set V)
  have hE : Module.finrank (ZMod 2) E ≤ B.card := by
    have hr := finrank_span_le_card (R := ZMod 2) (↑(B.image f) : Set V)
    exact (by simpa [E] using hr : Module.finrank (ZMod 2) E ≤ (B.image f).card).trans
      Finset.card_image_le
  exact (Submodule.finrank_mono hle).trans
    ((Submodule.finrank_add_le_finrank_add_finrank D E).trans (Nat.add_le_add_left hE _))

private lemma distinguished_mem {ι V : Type*} [DecidableEq ι] [DecidableEq V] [AddCommGroup V]
    [Module (ZMod 2) V] (D : Submodule (ZMod 2) V) (B : Finset ι) (f : ι → V)
    {b : ι} (hb : b ∈ B) (hsum : ∑ i ∈ B, f i ∈ D) :
    f b ∈ D ⊔ Submodule.span (ZMod 2) (↑((B.erase b).image f) : Set V) := by
  classical
  let E := Submodule.span (ZMod 2) (↑((B.erase b).image f) : Set V)
  have hrest : ∑ i ∈ B.erase b, f i ∈ E := by
    apply E.sum_mem
    intro i hi
    exact Submodule.subset_span (Finset.mem_image_of_mem f hi)
  have hD : D ≤ D ⊔ E := le_sup_left
  have hE : E ≤ D ⊔ E := le_sup_right
  have hsub := (D ⊔ E : Submodule (ZMod 2) V).sub_mem (hD hsum) (hE hrest)
  rw [← Finset.sum_erase_add B f hb, add_comm, add_sub_cancel_right] at hsub
  exact hsub

private lemma optimum {ι V : Type*} [DecidableEq ι] [DecidableEq V] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (P : Finset ι → Finset (Finset ι)) (h : ι → V)
    (hsubset : ∀ X B : Finset ι, B ∈ P X → B ⊆ X)
    (hnonempty : ∀ X B : Finset ι, B ∈ P X → B.Nonempty)
    (hdisjoint : ∀ X B C : Finset ι, B ∈ P X → C ∈ P X → B ≠ C → Disjoint B C)
    (hcover : ∀ X : Finset ι, (P X).biUnion id = X)
    (hreplace : ∀ {X B T : Finset ι}, B ∈ P X → T ⊆ B →
      P ((X \ B) ∪ T) = ((P X).erase B) ∪ P T) :
    let total := fun T : Finset ι => ∑ i ∈ T, h i
    let space := fun X => Submodule.span (ZMod 2) (↑((P X).image total) : Set V)
    let score := fun X => (P X).card - Module.finrank (ZMod 2) (space X)
    ∀ S : Finset ι, (∀ T, score T ≤ score S) →
      (∀ T : Finset ι, score T = score S → S.card ≤ T.card) →
      ∀ C ∈ P S,
        total C ∈ Submodule.span (ZMod 2) (↑(((P S).erase C).image total) : Set V) ∧
        (∀ T : Finset ι, T ⊆ C → T ≠ C → T.Nonempty → total T ∉ space S) := by
  classical
  intro total space score S hmax hmin C hC
  have strict_score (R : Finset ι) (hR : R.card < S.card) : score R < score S :=
    lt_of_le_of_ne (hmax R) (fun he => (Nat.not_le_of_lt hR) (hmin R he))
  have hCS : C ⊆ S := hsubset S C hC
  have smaller (T : Finset ι) (hT : T ⊆ C) (hne : T ≠ C) :
      ((S \ C) ∪ T).card < S.card := by
    obtain ⟨x, hxC, hxT⟩ : ∃ x ∈ C, x ∉ T := by
      by_contra! hn
      exact hne (le_antisymm hT hn)
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset Finset.sdiff_subset (hT.trans hCS), ?_⟩
    intro he
    have hxR : x ∈ (S \ C) ∪ T := he.symm ▸ hCS hxC
    exact (Finset.mem_union.mp hxR).elim (fun hh => (Finset.mem_sdiff.mp hh).2 hxC) hxT
  have hcardE := Finset.card_erase_of_mem hC
  constructor
  · have hp0 : P ∅ = ∅ := by
      by_contra hn
      obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      obtain ⟨x, hx⟩ := hnonempty ∅ B hB
      simpa using hsubset ∅ B hB hx
    have hre : P (S \ C) = (P S).erase C := by
      simpa [hp0] using hreplace hC (Finset.empty_subset C)
    have hempty : (∅ : Finset ι) ≠ C :=
      Ne.symm (Finset.nonempty_iff_ne_empty.mp (hnonempty S C hC))
    have hs := strict_score (S \ C) (by simpa using smaller ∅ (Finset.empty_subset C) hempty)
    by_contra hmiss
    have hle : space (S \ C) ≤ space S := by
      apply Submodule.span_mono
      rw [hre]
      exact Finset.coe_subset.mpr (Finset.image_subset_image (Finset.erase_subset C (P S)))
    have hlt : space (S \ C) < space S := by
      apply lt_of_le_of_ne hle
      intro he
      apply hmiss
      have hm : total C ∈ space S :=
        Submodule.subset_span (Finset.mem_image_of_mem total hC)
      rw [← he] at hm
      dsimp [space] at hm
      rwa [hre] at hm
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    dsimp [score] at hs
    rw [hre, hcardE] at hs
    omega
  · intro T hT hne htE hsum
    let R := (S \ C) ∪ T
    let B := P T
    have hR : P R = (P S).erase C ∪ B := hreplace hC hT
    have hdiff : Disjoint ((P S).erase C) B := by
      apply Finset.disjoint_left.mpr
      intro U hU hU'
      obtain ⟨x, hx⟩ := hnonempty T U hU'
      have hen := Finset.mem_erase.mp hU
      exact Finset.disjoint_left.mp (hdisjoint S U C hen.2 hC hen.1) hx
        (hT (hsubset T U hU' hx))
    have hcard : (P R).card = (P S).card - 1 + B.card := by
      rw [hR, Finset.card_union_of_disjoint hdiff, hcardE]
    have hsumB : ∑ U ∈ B, total U ∈ space S := by
      have hd : Set.PairwiseDisjoint (↑B : Set (Finset ι)) id := by
        intro U hU W hW hne'
        exact hdisjoint T U W hU hW hne'
      have hb := Finset.sum_biUnion (f := h) hd
      change (∑ i ∈ B.biUnion id, h i) = ∑ U ∈ B, total U at hb
      rw [← hb, show B.biUnion id = T from hcover T]
      exact hsum
    obtain ⟨x, hx⟩ := htE
    have hx' : x ∈ B.biUnion id := (hcover T).symm ▸ hx
    obtain ⟨b, hb, _⟩ := Finset.mem_biUnion.mp hx'
    let E := Submodule.span (ZMod 2) (↑((B.erase b).image total) : Set V)
    have hleft : space S ≤ space S ⊔ E := le_sup_left
    have hright : E ≤ space S ⊔ E := le_sup_right
    have hle : space R ≤ space S ⊔ E := by
      apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hy
      rw [hR, Finset.mem_union] at hU
      rcases hU with hU | hU
      · exact hleft (Submodule.subset_span (Finset.mem_image_of_mem total (Finset.mem_of_mem_erase hU)))
      · by_cases he : U = b
        · subst U
          exact distinguished_mem (space S) B total hb hsumB
        · exact hright (Submodule.subset_span (Finset.mem_image_of_mem total (Finset.mem_erase.mpr ⟨he, hU⟩)))
    have hr := rank_le_add_card (space S) (space R) (B.erase b) total hle
    rw [Finset.card_erase_of_mem hb] at hr
    have hB := Finset.card_pos.mpr ⟨b, hb⟩
    have hs := strict_score R (smaller T hT hne)
    dsimp [score] at hs
    rw [hcard] at hs
    omega

private theorem binary_card_bound {V Q : Type*} [DecidableEq V] [AddCommGroup Q]
    [Module (ZMod 2) Q] [FiniteDimensional (ZMod 2) Q] (C : Finset V) (v : V → Q)
    (h : ∀ T : Finset V, T ⊆ C → T ≠ C → T.Nonempty → ∑ i ∈ T, v i ≠ 0) :
    C.card ≤ Module.finrank (ZMod 2) Q + 1 := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  let ι := {i // i ∈ C.erase x}
  let e : ι ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have binary (z : ZMod 2) : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  classical
  have hind : LinearIndependent (ZMod 2) (fun i : ι => v i.val) := by
    apply linearIndependent_iff'.2
    intro s g hs i hi
    by_contra hgi
    let t := s.filter (fun j => g j ≠ 0)
    let T := t.map e
    have hTsub : T ⊆ C := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp ha
      exact Finset.mem_of_mem_erase j.property
    have hTne : T ≠ C := by
      intro heq
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp (heq.symm ▸ hx : x ∈ T)
      exact (Finset.mem_erase.mp j.property).1 hj
    have hTnon : T.Nonempty :=
      ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩, rfl⟩⟩
    apply h T hTsub hTne hTnon
    calc
      ∑ j ∈ T, v j = ∑ j ∈ t, v j.val := Finset.sum_map t e v
      _ = ∑ j ∈ t, g j • v j.val := by
        apply Finset.sum_congr rfl
        intro j hj
        have hg : g j = 1 := (binary (g j)).resolve_left (Finset.mem_filter.mp hj).2
        simp [hg]
      _ = ∑ j ∈ s, g j • v j.val := by
        dsimp [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hg : g j = 0 <;> simp [hg]
      _ = 0 := hs
  have hcard := hind.fintype_card_le_finrank
  have hc : Fintype.card ι = (C.erase x).card := Fintype.card_coe _
  rw [hc] at hcard
  rw [← Finset.card_erase_add_one hx]
  exact Nat.add_le_add_right hcard 1

end PEqualNP.Outside.L_lib_849_aux

open PEqualNP.Outside.L_lib_849_aux

theorem PEqualNP.Outside.L_lib_849 :
    ∀ (n m : ℕ) (G : SimpleGraph (Fin n)),
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let A := Fin m → F
      ∀ h : Fin n → A,
        let parts := fun S : Finset (Fin n) =>
          S.attach.image (fun v =>
            (S.attach.filter (fun u => (G.induce (↑S : Set (Fin n))).Reachable v u)).image Subtype.val)
        let total := fun T : Finset (Fin n) => ∑ i ∈ T, h i
        let space := fun S => Submodule.span F (↑((parts S).image total) : Set A)
        let score := fun S => (parts S).card - Module.finrank F (space S)
        ∀ S : Finset (Fin n), (∀ T, score T ≤ score S) →
          (∀ T : Finset (Fin n), score T = score S → S.card ≤ T.card) →
          ∀ C ∈ parts S,
            total C ∈ Submodule.span F (↑(((parts S).erase C).image total) : Set A) ∧
            (∀ T : Finset (Fin n), T ⊆ C → T ≠ C → T.Nonempty → total T ∉ space S) ∧
            C.card ≤ (m - Module.finrank F (space S)) + 1 := by
  intro n m G F A h parts total space score S hmax hmin C hC
  classical
  let P := PEqualNP.Outside.L_lib_849_aux.parts G
  have hp : parts = P := by
    funext R
    ext B
    simp only [parts, P, PEqualNP.Outside.L_lib_849_aux.parts, Finset.mem_image,
      Finset.ext_iff, Finset.mem_filter]
  let spanOf (B : Finset (Finset (Fin n))) := Submodule.span F (↑(B.image total) : Set A)
  let rankOf (B : Finset (Finset (Fin n))) := Module.finrank F (spanOf B)
  have hspace (R : Finset (Fin n)) : space R = spanOf (P R) := by
    simp only [space, spanOf, Finset.coe_image, hp]
  have hscore (R : Finset (Fin n)) : score R = (P R).card - rankOf (P R) :=
    congrArg₂ (fun a b : ℕ => a - b) (congrArg (fun Q => (Q R).card) hp)
      (congrArg (fun D : Submodule F A => Module.finrank F D) (hspace R))
  have hmaxP (T : Finset (Fin n)) : (P T).card - rankOf (P T) ≤ (P S).card - rankOf (P S) := by
    rw [← hscore T, ← hscore S]
    exact hmax T
  have hminP (T : Finset (Fin n)) :
      (P T).card - rankOf (P T) = (P S).card - rankOf (P S) → S.card ≤ T.card := by
    rw [← hscore T, ← hscore S]
    exact hmin T
  rw [hp] at hC
  obtain ⟨hredundant, hnosub⟩ := optimum P h
    (fun _ _ hB => parts_subset hB) (fun _ _ hB => parts_nonempty hB)
    (fun _ _ _ hB hD hne => parts_disjoint hB hD hne) (parts_cover G)
    (fun hB hT => parts_replace G hB hT) S hmaxP hminP C hC
  have hnot (T : Finset (Fin n)) (hs : T ⊆ C) (hn : T ≠ C) (ht : T.Nonempty) :
      total T ∉ space S := by
    rw [hspace S]
    exact hnosub T hs hn ht
  refine ⟨?_, hnot, ?_⟩
  · simpa only [Finset.coe_image, Finset.coe_erase, hp] using hredundant
  let D := space S
  have hproper : ∀ T : Finset (Fin n), T ⊆ C → T ≠ C → T.Nonempty →
      ∑ i ∈ T, D.mkQ (h i) ≠ 0 := by
    intro T hsub hne hne' hz
    rw [← map_sum, D.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    exact hnot T hsub hne hne' hz
  have hc := binary_card_bound C (fun i => D.mkQ (h i)) hproper
  have hdim := Submodule.finrank_quotient (R := ZMod 2) D
  have hm : Module.finrank (ZMod 2) A = m := Module.finrank_fin_fun (R := ZMod 2)
  rw [hm] at hdim
  change C.card ≤ m - Module.finrank (ZMod 2) D + 1
  rw [← hdim]
  exact hc
