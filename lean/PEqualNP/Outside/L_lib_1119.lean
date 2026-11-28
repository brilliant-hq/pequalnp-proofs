import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1119 : (∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
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
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q) := by
  intro n E hE sets miss maximal base D family bank determines ord Q

  have hf : ∀ H X, (!decide (miss H X)) = true ↔ ∃ e ∈ H, e ⊆ X := by
    intro H X
    simp [miss]
  have hf' : ∀ H X, (!decide (miss H X)) = false ↔ ∀ e ∈ H, ¬ e ⊆ X := by
    intro H X
    simp [miss]

  have hfam : ∀ H ∈ family, H = E ∨ ∃ v ∈ D, H = E.filter (fun e => v ∉ e) := by
    intro H hH
    simp only [family, Finset.mem_insert, Finset.mem_image] at hH
    rcases hH with h | ⟨v, hv, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, h.symm⟩
  have hsub : ∀ H ∈ family, H ⊆ E := by
    intro H hH
    rcases hfam H hH with h | ⟨v, -, h⟩
    · rw [h]
    · rw [h]
      exact Finset.filter_subset _ _
  have hEfam : E ∈ family := Finset.mem_insert_self _ _
  have hvfam : ∀ v ∈ D, E.filter (fun e => v ∉ e) ∈ family := fun v hv =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv)

  have hbase : ∀ B, B ∈ base ↔ (∀ e ∈ E, ¬ e ⊆ B) ∧ ∀ i, i ∉ B → ∃ e ∈ E, e ⊆ insert i B := by
    intro B
    simp [base, maximal, sets, miss]
  have hbank : ∀ Z, Z ∈ bank ↔
      Z ∈ E ∨ Z ∈ base ∨ ∃ v ∈ D, ∃ B ∈ base, v ∉ B ∧ insert v B = Z := by
    intro Z
    simp only [bank, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      and_assoc, or_assoc]

  have hext : ∀ X, (∀ e ∈ E, ¬ e ⊆ X) → ∃ B ∈ base, X ⊆ B := by
    intro X hX
    obtain ⟨B, hXB, hmax⟩ := Finset.exists_le_maximal
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun Y => X ⊆ Y ∧ ∀ e ∈ E, ¬ e ⊆ Y))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.Subset.refl _, hX⟩)
    have hB := (Finset.mem_filter.1 hmax.1).2
    refine ⟨B, (hbase B).2 ⟨hB.2, ?_⟩, hXB⟩
    intro i hi
    by_contra hno
    push Not at hno
    have hmem : insert i B ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun Y => X ⊆ Y ∧ ∀ e ∈ E, ¬ e ⊆ Y) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hB.1.trans (Finset.subset_insert _ _), hno⟩
    exact hi (hmax.2 hmem (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  constructor
  ·
    intro hdet Z hZ
    by_contra hZQ
    rcases (hbank Z).1 hZ with hZE | hZb | ⟨v, hvD, B, hB, hvB, rfl⟩
    ·
      have key := hdet (fun H X => (!decide (miss H X)) && decide (X ≠ Z))
        (by
          intro H hH X Y hXY hC
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hC ⊢
          obtain ⟨e, he, heX⟩ := (hf H X).1 hC.1
          refine ⟨(hf H Y).2 ⟨e, he, heX.trans hXY⟩, ?_⟩
          rintro rfl
          have heZ : e = Y := Finset.eq_of_subset_of_card_le (heX.trans hXY)
            (by rw [hE e (hsub H hH he), hE Y hZE])
          exact hC.2 (Finset.Subset.antisymm hXY (heZ ▸ heX)))
        (by
          intro _ H hH J hJ hHJ X hC
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hC ⊢
          obtain ⟨e, he, heX⟩ := (hf H X).1 hC.1
          exact ⟨(hf J X).2 ⟨e, hHJ he, heX⟩, hC.2⟩)
        (by
          intro H hH X hXQ
          have hXZ : X ≠ Z := fun h => hZQ (h ▸ hXQ)
          simp [hXZ])
        E hEfam Z
      have h1 : (!decide (miss E Z)) = true := (hf E Z).2 ⟨Z, hZE, Finset.Subset.refl _⟩
      rw [h1] at key
      simp at key
    ·
      have key := hdet (fun H X => (!decide (miss H X)) || decide (X = Z ∧ E ⊆ H))
        (by
          intro H hH X Y hXY hC
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hC ⊢
          rcases hC with hC | ⟨hXZ, hEH⟩
          · obtain ⟨e, he, heX⟩ := (hf H X).1 hC
            exact Or.inl ((hf H Y).2 ⟨e, he, heX.trans hXY⟩)
          · by_cases hYZ : Y = Z
            · exact Or.inr ⟨hYZ, hEH⟩
            · rw [hXZ] at hXY
              obtain ⟨i, hiY, hiZ⟩ := Finset.exists_of_ssubset
                (Finset.ssubset_iff_subset_ne.2 ⟨hXY, Ne.symm hYZ⟩)
              obtain ⟨e, he, hei⟩ := ((hbase Z).1 hZb).2 i hiZ
              exact Or.inl ((hf H Y).2 ⟨e, hEH he, hei.trans (Finset.insert_subset hiY hXY)⟩))
        (by
          intro _ H hH J hJ hHJ X hC
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hC ⊢
          rcases hC with hC | ⟨hXZ, hEH⟩
          · obtain ⟨e, he, heX⟩ := (hf H X).1 hC
            exact Or.inl ((hf J X).2 ⟨e, hHJ he, heX⟩)
          · exact Or.inr ⟨hXZ, hEH.trans hHJ⟩)
        (by
          intro H hH X hXQ
          have hXZ : X ≠ Z := fun h => hZQ (h ▸ hXQ)
          simp [hXZ])
        E hEfam Z
      have h1 : (!decide (miss E Z)) = false := (hf' E Z).2 ((hbase Z).1 hZb).1
      rw [h1] at key
      simp at key
    ·
      have hfZ : (!decide (miss (E.filter (fun e => v ∉ e)) (insert v B))) = false := by
        refine (hf' _ _).2 ?_
        intro e he heZ
        obtain ⟨heE, hve⟩ := Finset.mem_filter.1 he
        exact ((hbase B).1 hB).1 e heE ((Finset.subset_insert_iff_of_notMem hve).1 heZ)
      have key := hdet (fun H X => (!decide (miss H X)) ||
          decide (X = insert v B ∧ E.filter (fun e => v ∉ e) ⊆ H))
        (by
          intro H hH X Y hXY hC
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hC ⊢
          rcases hC with hC | ⟨hXZ, hEH⟩
          · obtain ⟨e, he, heX⟩ := (hf H X).1 hC
            exact Or.inl ((hf H Y).2 ⟨e, he, heX.trans hXY⟩)
          · by_cases hYZ : Y = insert v B
            · exact Or.inr ⟨hYZ, hEH⟩
            · rw [hXZ] at hXY
              obtain ⟨i, hiY, hiZ⟩ := Finset.exists_of_ssubset
                (Finset.ssubset_iff_subset_ne.2 ⟨hXY, Ne.symm hYZ⟩)
              rw [Finset.mem_insert, not_or] at hiZ
              obtain ⟨e, he, hei⟩ := ((hbase B).1 hB).2 i hiZ.2
              have hve : v ∉ e := by
                intro hve
                have := hei hve
                rw [Finset.mem_insert] at this
                rcases this with h | h
                · exact hiZ.1 h.symm
                · exact hvB h
              have hBY : B ⊆ Y := (Finset.subset_insert _ _).trans hXY
              exact Or.inl ((hf H Y).2 ⟨e, hEH (Finset.mem_filter.2 ⟨he, hve⟩),
                hei.trans (Finset.insert_subset hiY hBY)⟩))
        (by
          intro _ H hH J hJ hHJ X hC
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hC ⊢
          rcases hC with hC | ⟨hXZ, hEH⟩
          · obtain ⟨e, he, heX⟩ := (hf H X).1 hC
            exact Or.inl ((hf J X).2 ⟨e, hHJ he, heX⟩)
          · exact Or.inr ⟨hXZ, hEH.trans hHJ⟩)
        (by
          intro H hH X hXQ
          have hXZ : X ≠ insert v B := fun h => hZQ (h ▸ hXQ)
          simp [hXZ])
        (E.filter (fun e => v ∉ e)) (hvfam v hvD) (insert v B)
      rw [hfZ] at key
      simp at key
  ·
    intro hbQ C hmono _ hagree H hH X
    by_cases hX : ∃ e ∈ H, e ⊆ X
    · obtain ⟨e, he, heX⟩ := hX
      have heQ : e ∈ Q := hbQ ((hbank e).2 (Or.inl (hsub H hH he)))
      have h1 : C H e = true := by
        rw [hagree H hH e heQ]
        exact (hf H e).2 ⟨e, he, Finset.Subset.refl _⟩
      rw [hmono H hH e X heX h1]
      exact ((hf H X).2 ⟨e, he, heX⟩).symm
    · push Not at hX
      rw [(hf' H X).2 hX]
      suffices hY : ∃ Y ∈ Q, X ⊆ Y ∧ ∀ e ∈ H, ¬ e ⊆ Y by
        obtain ⟨Y, hYQ, hXY, hYm⟩ := hY
        by_contra hC
        have hCX : C H X = true := by simpa using hC
        have h2 := hmono H hH X Y hXY hCX
        rw [hagree H hH Y hYQ, (hf' H Y).2 hYm] at h2
        exact Bool.false_ne_true h2
      by_cases hXE : ∀ e ∈ E, ¬ e ⊆ X
      · obtain ⟨B, hB, hXB⟩ := hext X hXE
        exact ⟨B, hbQ ((hbank B).2 (Or.inr (Or.inl hB))), hXB,
          fun e he heB => ((hbase B).1 hB).1 e (hsub H hH he) heB⟩
      · push Not at hXE
        obtain ⟨e, heE, heX⟩ := hXE
        have heH : e ∉ H := fun h => hX e h heX
        rcases hfam H hH with h | ⟨v, hvD, rfl⟩
        · rw [h] at heH
          exact absurd heE heH
        · have hve : v ∈ e := by
            by_contra hve
            exact heH (Finset.mem_filter.2 ⟨heE, hve⟩)
          have hX' : ∀ e' ∈ E, ¬ e' ⊆ X.erase v := by
            intro e' he' hsub'
            have hve' : v ∉ e' := fun h => by
              have := hsub' h
              simp at this
            exact hX e' (Finset.mem_filter.2 ⟨he', hve'⟩) (hsub'.trans (Finset.erase_subset _ _))
          obtain ⟨B, hB, hXB⟩ := hext _ hX'
          have hvB : v ∉ B := by
            intro hvB
            apply ((hbase B).1 hB).1 e heE
            intro w hw
            by_cases hwv : w = v
            · rw [hwv]
              exact hvB
            · exact hXB (Finset.mem_erase.2 ⟨hwv, heX hw⟩)
          refine ⟨insert v B, hbQ ((hbank _).2 (Or.inr (Or.inr ⟨v, hvD, B, hB, hvB, rfl⟩))), ?_, ?_⟩
          · intro w hw
            by_cases hwv : w = v
            · rw [hwv]
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hXB (Finset.mem_erase.2 ⟨hwv, hw⟩))
          · intro e' he' hsub'
            obtain ⟨he'E, hve'⟩ := Finset.mem_filter.1 he'
            exact ((hbase B).1 hB).1 e' he'E ((Finset.subset_insert_iff_of_notMem hve').1 hsub')
