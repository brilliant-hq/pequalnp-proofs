import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1119

abbrev miss {n : Nat} (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) : Prop :=
  ∀ e ∈ H, ¬e ⊆ X

abbrev maximal {n : Nat} (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))

theorem exists_maximal_superset {n : Nat} (H : Finset (Finset (Fin n)))
    (X : Finset (Fin n)) (hX : miss H X) :
    ∃ M ∈ maximal H Finset.univ, X ⊆ M := by
  let s : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun Y => X ⊆ Y ∧ miss H Y)
  have hs : s.Nonempty := ⟨X, Finset.mem_filter.2 ⟨Finset.mem_univ X, Finset.Subset.rfl, hX⟩⟩
  obtain ⟨M, hMs, hMmax⟩ := Finset.exists_max_image s Finset.card hs
  obtain ⟨_, hXM, hMissM⟩ := Finset.mem_filter.1 hMs
  refine ⟨M, Finset.mem_filter.2 ⟨Finset.mem_univ M, Finset.subset_univ M, hMissM, ?_⟩, hXM⟩
  intro i hi hmi
  have hiM : i ∉ M := (Finset.mem_sdiff.1 hi).2
  have hins : insert i M ∈ s :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hXM.trans (Finset.subset_insert i M), hmi⟩
  have hle : (insert i M).card ≤ M.card := hMmax (insert i M) hins
  have hlt : M.card < (insert i M).card := Finset.card_lt_card (Finset.ssubset_insert hiM)
  omega

theorem maximal_del_mem_bank {n : Nat} (E : Finset (Finset (Fin n))) (D : Finset (Fin n))
    (v : Fin n) (hvD : v ∈ D) (M : Finset (Fin n))
    (hM : M ∈ maximal (E.filter (fun e => v ∉ e)) Finset.univ) :
    M ∈ E ∪ maximal E Finset.univ ∪
      D.biUnion (fun w => ((maximal E Finset.univ).filter (fun X => w ∉ X)).image (insert w)) := by
  let Ev := E.filter (fun e => v ∉ e)
  have hMf : M ∈ maximal Ev Finset.univ := hM
  obtain ⟨_, _, hMissEv, hMaxEv⟩ := Finset.mem_filter.1 hMf
  have hvM : v ∈ M := by
    by_contra hvM
    apply hMaxEv v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvM⟩)
    intro e he heins
    have hve : v ∉ e := (Finset.mem_filter.1 he).2
    have heM : e ⊆ M := by
      intro x hx
      rcases Finset.mem_insert.1 (heins hx) with rfl | hxM
      · exact absurd hx hve
      · exact hxM
    exact hMissEv e he heM
  by_cases hMissE : miss E M
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    refine Finset.mem_filter.2 ⟨Finset.mem_univ M, Finset.subset_univ M, hMissE, ?_⟩
    intro i hi hmE
    exact hMaxEv i hi (fun e he => hmE e (Finset.mem_filter.1 he).1)
  · let Y := M.erase v
    have hvY : v ∉ Y := by simp [Y]
    have hinsY : insert v Y = M := Finset.insert_erase hvM
    have hYbase : Y ∈ maximal E Finset.univ := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ Y, Finset.subset_univ Y, ?_, ?_⟩
      · intro e he heY
        by_cases hve : v ∈ e
        · exact hvY (heY hve)
        · exact hMissEv e (Finset.mem_filter.2 ⟨he, hve⟩) (heY.trans (Finset.erase_subset v M))
      · intro i hi hmE
        have hiY : i ∉ Y := (Finset.mem_sdiff.1 hi).2
        by_cases hiv : i = v
        · subst hiv
          rw [hinsY] at hmE
          exact hMissE hmE
        · have hiM : i ∉ M := fun h => hiY (Finset.mem_erase.2 ⟨hiv, h⟩)
          apply hMaxEv i (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hiM⟩)
          intro e he heins
          have hve : v ∉ e := (Finset.mem_filter.1 he).2
          have heinsY : e ⊆ insert i Y := by
            intro x hx
            rcases Finset.mem_insert.1 (heins hx) with rfl | hxM
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (Finset.mem_erase.2 ⟨fun hxv => hve (hxv ▸ hx), hxM⟩)
          exact hmE e (Finset.mem_filter.1 he).1 heinsY
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.2
      ⟨v, hvD, Finset.mem_image.2 ⟨Y, Finset.mem_filter.2 ⟨hYbase, hvY⟩, hinsY⟩⟩

theorem family_subset_E {n : Nat} (E : Finset (Finset (Fin n))) (D : Finset (Fin n))
    {H : Finset (Finset (Fin n))}
    (hH : H ∈ insert E (D.image (fun v => E.filter (fun e => v ∉ e)))) : H ⊆ E := by
  rcases Finset.mem_insert.1 hH with rfl | hH'
  · exact Finset.Subset.rfl
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hH'
    exact Finset.filter_subset _ _

theorem f_mono_X {n : Nat} {H : Finset (Finset (Fin n))} {X Y : Finset (Fin n)}
    [Decidable (miss H X)] [Decidable (miss H Y)]
    (hXY : X ⊆ Y) (hf : (!decide (miss H X)) = true) : (!decide (miss H Y)) = true := by
  have h1 : ¬miss H X := by simpa using hf
  have h2 : ¬miss H Y := fun hm => h1 (fun e he heX => hm e he (heX.trans hXY))
  simp [h2]

theorem f_mono_H {n : Nat} {H J : Finset (Finset (Fin n))} {X : Finset (Fin n)}
    [Decidable (miss H X)] [Decidable (miss J X)]
    (hHJ : H ⊆ J) (hf : (!decide (miss H X)) = true) : (!decide (miss J X)) = true := by
  have h1 : ¬miss H X := by simpa using hf
  have h2 : ¬miss J X := fun hm => h1 (fun e he heX => hm e (hHJ he) heX)
  simp [h2]

theorem main_proof : ∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
  let sets := (Finset.univ : Finset (Finset (Fin n)))
  let miss := fun (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) => ∀ e ∈ H, ¬e ⊆ X
  let maximal := fun (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) =>
    sets.filter (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))
  let base := maximal E Finset.univ
  ∀ D : Finset (Fin n),
  let family := insert E (D.image (fun v => E.filter (fun e => v ∉ e)))
  let bank := E ∪ base ∪ D.biUnion (fun v => (base.filter (fun X => v ∉ X)).image (insert v))
  let determines := fun (ord : Bool) (Q : Finset (Finset (Fin n))) =>
    ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q := by
  intro n E hE2 sets miss0 maximal0 base D family bank determines ord Q
  constructor
  · intro hdet Z hZbank
    by_contra hZQ
    rcases Finset.mem_union.1 hZbank with hZ1 | hZdel
    · rcases Finset.mem_union.1 hZ1 with hZE | hZbase
      · let C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool :=
          fun H X => if X ⊆ Z then false else !decide (miss0 H X)
        have hmono : ∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true := by
          intro H _ X Y hXY hCX
          by_cases hXZ : X ⊆ Z
          · simp [C, hXZ] at hCX
          · simp only [C, hXZ, ↓reduceIte] at hCX
            have hYZ : ¬Y ⊆ Z := fun h => hXZ (hXY.trans h)
            simp only [C, hYZ, ↓reduceIte]
            exact f_mono_X hXY hCX
        have hord : ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true := by
          intro _ H _ J _ hHJ X hCX
          by_cases hXZ : X ⊆ Z
          · simp [C, hXZ] at hCX
          · simp only [C, hXZ, ↓reduceIte] at hCX ⊢
            exact f_mono_H hHJ hCX
        have hagree : ∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss0 H X) := by
          intro H hH X hXQ
          by_cases hXZ : X ⊆ Z
          · have hCHX : C H X = false := by simp [C, hXZ]
            rw [hCHX]
            have hss : X ⊂ Z := Finset.ssubset_iff_subset_ne.2 ⟨hXZ, fun h => hZQ (h ▸ hXQ)⟩
            have hlt : X.card < Z.card := Finset.card_lt_card hss
            have hZ2 : Z.card = 2 := hE2 Z hZE
            have hmHX : miss0 H X := by
              intro e he heX
              have he2 : e.card = 2 := hE2 e (family_subset_E E D hH he)
              have hle : e.card ≤ X.card := Finset.card_le_card heX
              omega
            simp [hmHX]
          · simp [C, hXZ]
        have hres := hdet C hmono hord hagree E (Finset.mem_insert_self _ _) Z
        have hCEZ : C E Z = false := by simp [C]
        have hnmEZ : ¬miss0 E Z := fun hm => hm Z hZE Finset.Subset.rfl
        rw [hCEZ] at hres
        simp [hnmEZ] at hres
      · let C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool :=
          fun H X => if H = E ∧ Z ⊆ X then true else !decide (miss0 H X)
        have hmono : ∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true := by
          intro H _ X Y hXY hCX
          by_cases h1 : H = E ∧ Z ⊆ X
          · simp [C, h1.1, h1.2.trans hXY]
          · simp only [C, h1, ↓reduceIte] at hCX
            by_cases h2 : H = E ∧ Z ⊆ Y
            · simp [C, h2]
            · simp only [C, h2, ↓reduceIte]
              exact f_mono_X hXY hCX
        have hord : ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true := by
          intro _ H _ J hJ hHJ X hCX
          by_cases h1 : H = E ∧ Z ⊆ X
          · have hJE : J = E := Finset.Subset.antisymm (family_subset_E E D hJ) (h1.1 ▸ hHJ)
            simp [C, hJE, h1.2]
          · simp only [C, h1, ↓reduceIte] at hCX
            by_cases h2 : J = E ∧ Z ⊆ X
            · simp [C, h2]
            · simp only [C, h2, ↓reduceIte]
              exact f_mono_H hHJ hCX
        have hZbase' : Z ∈ maximal E Finset.univ := hZbase
        obtain ⟨_, _, hMissEZ, hMaxEZ⟩ := Finset.mem_filter.1 hZbase'
        have hagree : ∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss0 H X) := by
          intro H _ X hXQ
          by_cases h1 : H = E ∧ Z ⊆ X
          · have hCHX : C H X = true := by simp [C, h1]
            rw [hCHX]
            have hHE : H = E := h1.1
            have hZX : Z ⊆ X := h1.2
            have hss : Z ⊂ X := Finset.ssubset_iff_subset_ne.2 ⟨hZX, fun h => hZQ (h ▸ hXQ)⟩
            obtain ⟨i, hiX, hiZ⟩ := Finset.exists_of_ssubset hss
            have hnm : ¬miss0 H X := by
              rw [hHE]
              intro hmX
              apply hMaxEZ i (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hiZ⟩)
              intro e he heins
              exact hmX e he (heins.trans (Finset.insert_subset hiX hZX))
            simp [hnm]
          · simp [C, h1]
        have hres := hdet C hmono hord hagree E (Finset.mem_insert_self _ _) Z
        have hCEZ : C E Z = true := by simp [C]
        have hMissEZ0 : miss0 E Z := hMissEZ
        rw [hCEZ] at hres
        simp [hMissEZ0] at hres
    · obtain ⟨v, hvD, hZimg⟩ := Finset.mem_biUnion.1 hZdel
      obtain ⟨Y, hYf, rfl⟩ := Finset.mem_image.1 hZimg
      obtain ⟨hYbase, hvY⟩ := Finset.mem_filter.1 hYf
      have hYbase' : Y ∈ maximal E Finset.univ := hYbase
      obtain ⟨_, _, hMissEY, hMaxEY⟩ := Finset.mem_filter.1 hYbase'
      let Ev := E.filter (fun e => v ∉ e)
      have hEvFam : Ev ∈ family := Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨v, hvD, rfl⟩)
      have hMissEvZ : miss0 Ev (insert v Y) := by
        intro e he heins
        obtain ⟨heE, hve⟩ := Finset.mem_filter.1 he
        have heY : e ⊆ Y := by
          intro x hx
          rcases Finset.mem_insert.1 (heins hx) with rfl | hxY
          · exact absurd hx hve
          · exact hxY
        exact hMissEY e heE heY
      let C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool :=
        fun H X => if Ev ⊆ H ∧ insert v Y ⊆ X then true else !decide (miss0 H X)
      have hmono : ∀ H ∈ family, ∀ X Y' : Finset (Fin n), X ⊆ Y' → C H X = true → C H Y' = true := by
        intro H _ X Y' hXY' hCX
        by_cases h1 : Ev ⊆ H ∧ insert v Y ⊆ X
        · simp [C, h1.1, h1.2.trans hXY']
        · simp only [C, h1, ↓reduceIte] at hCX
          by_cases h2 : Ev ⊆ H ∧ insert v Y ⊆ Y'
          · simp [C, h2]
          · simp only [C, h2, ↓reduceIte]
            exact f_mono_X hXY' hCX
      have hord : ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true := by
        intro _ H _ J _ hHJ X hCX
        by_cases h1 : Ev ⊆ H ∧ insert v Y ⊆ X
        · simp [C, h1.1.trans hHJ, h1.2]
        · simp only [C, h1, ↓reduceIte] at hCX
          by_cases h2 : Ev ⊆ J ∧ insert v Y ⊆ X
          · simp [C, h2]
          · simp only [C, h2, ↓reduceIte]
            exact f_mono_H hHJ hCX
      have hagree : ∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss0 H X) := by
        intro H _ X hXQ
        by_cases h1 : Ev ⊆ H ∧ insert v Y ⊆ X
        · have hCHX : C H X = true := by simp [C, h1]
          rw [hCHX]
          have hEvH : Ev ⊆ H := h1.1
          have hZX : insert v Y ⊆ X := h1.2
          have hss : insert v Y ⊂ X :=
            Finset.ssubset_iff_subset_ne.2 ⟨hZX, fun h => hZQ (h ▸ hXQ)⟩
          obtain ⟨i, hiX, hiZ⟩ := Finset.exists_of_ssubset hss
          have hiv : i ≠ v := fun h => hiZ (h ▸ Finset.mem_insert_self v Y)
          have hiY : i ∉ Y := fun h => hiZ (Finset.mem_insert_of_mem h)
          have hnm : ¬miss0 H X := by
            intro hmH
            apply hMaxEY i (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hiY⟩)
            intro e heE heiY
            have hve : v ∉ e := by
              intro hve
              rcases Finset.mem_insert.1 (heiY hve) with hvi | hvY'
              · exact hiv hvi.symm
              · exact hvY hvY'
            have heEv : e ∈ Ev := Finset.mem_filter.2 ⟨heE, hve⟩
            have heX : e ⊆ X := heiY.trans
              (Finset.insert_subset hiX ((Finset.subset_insert v Y).trans hZX))
            exact hmH e (hEvH heEv) heX
          simp [hnm]
        · simp [C, h1]
      have hres := hdet C hmono hord hagree Ev hEvFam (insert v Y)
      have hCEvZ : C Ev (insert v Y) = true := by simp [C]
      rw [hCEvZ] at hres
      simp [hMissEvZ] at hres
  · intro hQ C hmono _ hagree H hH X
    by_cases hm : miss0 H X
    · obtain ⟨M, hM, hXM⟩ := exists_maximal_superset H X hm
      have hMbank : M ∈ bank := by
        rcases Finset.mem_insert.1 hH with rfl | hH'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hM)
        · obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.1 hH'
          exact maximal_del_mem_bank E D v hvD M hM
      have hCM : C H M = false := by
        have h1 := hagree H hH M (hQ hMbank)
        have hMissM : miss0 H M := (Finset.mem_filter.1 hM).2.2.1
        simpa [hMissM] using h1
      have hCX : C H X = false := by
        cases hval : C H X
        · rfl
        · have := hmono H hH X M hXM hval
          rw [hCM] at this
          cases this
      simp [hm, hCX]
    · have hex : ∃ e ∈ H, e ⊆ X := by
        by_contra hno
        apply hm
        intro e he heX
        exact hno ⟨e, he, heX⟩
      obtain ⟨e, heH, heX⟩ := hex
      have hebank : e ∈ bank :=
        Finset.mem_union_left _ (Finset.mem_union_left _ (family_subset_E E D hH heH))
      have hCe : C H e = true := by
        have h1 := hagree H hH e (hQ hebank)
        have hnm : ¬miss0 H e := fun h => h e heH Finset.Subset.rfl
        simpa [hnm] using h1
      have hCX : C H X = true := hmono H hH e X heX hCe
      simp [hm, hCX]

end PEqualNP.Outside.L_lib_1119

theorem PEqualNP.Outside.L_lib_1119 : ∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
  let sets := (Finset.univ : Finset (Finset (Fin n)))
  let miss := fun (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) => ∀ e ∈ H, ¬e ⊆ X
  let maximal := fun (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) =>
    sets.filter (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))
  let base := maximal E Finset.univ
  ∀ D : Finset (Fin n),
  let family := insert E (D.image (fun v => E.filter (fun e => v ∉ e)))
  let bank := E ∪ base ∪ D.biUnion (fun v => (base.filter (fun X => v ∉ X)).image (insert v))
  let determines := fun (ord : Bool) (Q : Finset (Finset (Fin n))) =>
    ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q :=
  PEqualNP.Outside.L_lib_1119.main_proof
