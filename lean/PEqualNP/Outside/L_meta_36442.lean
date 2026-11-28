import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36442

theorem pair_eq {n : Nat} {e : Finset (Fin n)} (h : e.card = 2) {a b : Fin n}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [h, Finset.card_pair hab]

theorem not_old_single {n : Nat} {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    (i : Fin n) : ¬ ∃ e ∈ E, e ⊆ ({i} : Finset (Fin n)) := by
  rintro ⟨e, he, hs⟩
  have := Finset.card_le_card hs
  rw [hE e he] at this
  simp at this

theorem key {n : Nat} {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    (center : Finset (Fin n) → Fin n) (uC : Bool) (uL : Fin n → Bool) (y : Fin n)
    (hcen : ∀ e ∈ E, center e ∈ e) (X : Finset (Fin n)) (z : Bool) :
    ((∃ e ∈ E,
          (center e ∈ X ∨ (z = true ∧ center e = y ∧ uC = true)) ∧
          ∃ j ∈ e, j ≠ center e ∧
            (j ∈ X ∨ (z = true ∧ j = y ∧ uL (center e) = true))) ↔
      ((∃ e ∈ E, e ⊆ X) ∨ (z = true ∧ ∃ i ∈ X, i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E ∧
        ((center {y, i} = y ∧ uC = true) ∨ (center {y, i} = i ∧ uL i = true))))) := by
  constructor
  · rintro ⟨e, he, hc, j, hj, hjc, hl⟩
    have hce := hcen e he
    have he2 : e = {center e, j} := pair_eq (hE e he) hce hj hjc.symm
    generalize hcdef : center e = c at *
    subst he2
    rcases hc with hc | ⟨hz, hcy, huc⟩
    · rcases hl with hl | ⟨hz, hjy, hul⟩
      · left
        exact ⟨_, he, Finset.insert_subset hc (Finset.singleton_subset_iff.2 hl)⟩
      · right
        have hp : ({y, c} : Finset (Fin n)) = {c, j} := by
          rw [hjy]; exact Finset.pair_comm _ _
        refine ⟨hz, c, hc, fun h => hjc (hjy.trans h.symm), ?_, Or.inr ⟨?_, hul⟩⟩
        · rw [hp]; exact he
        · rw [hp]; exact hcdef
    · rcases hl with hl | ⟨hz', hjy, hul⟩
      · right
        have hp : ({y, j} : Finset (Fin n)) = {c, j} := by rw [hcy]
        refine ⟨hz, j, hl, fun h => hjc (h.trans hcy.symm), ?_, Or.inl ⟨?_, huc⟩⟩
        · rw [hp]; exact he
        · rw [hp]; exact hcdef.trans hcy
      · exact absurd (hjy.trans hcy.symm) hjc
  · rintro (⟨e, he, hsub⟩ | ⟨hz, i, hiX, hiy, hiE, h⟩)
    · have hce := hcen e he
      have hcard : 1 < e.card := by rw [hE e he]; norm_num
      obtain ⟨j, hj, hjc⟩ := Finset.exists_mem_ne hcard (center e)
      exact ⟨e, he, Or.inl (hsub hce), j, hj, hjc, Or.inl (hsub hj)⟩
    · rcases h with ⟨hc, huc⟩ | ⟨hc, hul⟩
      · refine ⟨{y, i}, hiE, Or.inr ⟨hz, hc, huc⟩, i, by simp, ?_, Or.inl hiX⟩
        rw [hc]; exact hiy
      · refine ⟨{y, i}, hiE, Or.inl (by rw [hc]; exact hiX), y, by simp, ?_,
          Or.inr ⟨hz, rfl, by rw [hc]; exact hul⟩⟩
        rw [hc]; exact hiy.symm

end PEqualNP.Outside.L_meta_36442

theorem PEqualNP.Outside.L_meta_36442 : ∀ (n : Nat) (E : Finset (Finset (Fin n))) (C S : Finset (Fin n)),
  (∀ e ∈ E, e.card = 2) → S.Nonempty →
  let cover := fun (K : Finset (Fin n)) => ∀ e ∈ E, ∃ v ∈ e, v ∈ K
  cover C → (∀ v ∈ C, ¬cover (C.erase v)) →
  let N := fun (y : Fin n) =>
    (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)
  let old := fun (X : Finset (Fin n)) => ∃ e ∈ E, e ⊆ X
  ∀ y : Fin n,
    (∃ (center : Finset (Fin n) → Fin n) (useCenter : Bool) (useLeaf : Fin n → Bool),
      (∀ e ∈ E, center e ∈ e ∧ center e ∈ C) ∧
      ∀ (X : Finset (Fin n)) (z : Bool),
        ((∃ e ∈ E,
          (center e ∈ X ∨ (z = true ∧ center e = y ∧ useCenter = true)) ∧
          ∃ j ∈ e, j ≠ center e ∧
            (j ∈ X ∨ (z = true ∧ j = y ∧ useLeaf (center e) = true))) ↔
         old X ∨ (z = true ∧ ∃ i ∈ S, i ∈ X))) ↔
    S ⊆ N y ∧ (y ∉ C ∨ Disjoint S (N y \ C) ∨ N y \ C ⊆ S) := by
  classical
  intro n E C S hE _hS
  dsimp only
  intro hcov _hmin y
  have hNm : ∀ i, i ∈ (Finset.univ : Finset (Fin n)).filter
      (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E) ↔ i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E := by
    intro i; simp
  constructor
  · rintro ⟨center, uC, uL, hcen, h⟩
    have hc' : ∀ e ∈ E, center e ∈ e := fun e he => (hcen e he).1
    have hk := fun X z => (PEqualNP.Outside.L_meta_36442.key hE center uC uL y hc' X z).symm.trans
      (h X z)
    have hact : ∀ i, i ∈ S ↔ (i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E ∧
        ((center {y, i} = y ∧ uC = true) ∨ (center {y, i} = i ∧ uL i = true))) := by
      intro i
      constructor
      · intro hi
        rcases (hk {i} true).2 (Or.inr ⟨rfl, i, hi, Finset.mem_singleton_self i⟩) with hold | ⟨_, i', hi', ha⟩
        · exact absurd hold (PEqualNP.Outside.L_meta_36442.not_old_single hE i)
        · have := Finset.mem_singleton.1 hi'
          subst this
          exact ha
      · intro ha
        rcases (hk {i} true).1 (Or.inr ⟨rfl, i, Finset.mem_singleton_self i, ha⟩) with hold | ⟨_, i', hiS, hi'⟩
        · exact absurd hold (PEqualNP.Outside.L_meta_36442.not_old_single hE i)
        · have := Finset.mem_singleton.1 hi'
          subst this
          exact hiS
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨hiy, hiE, _⟩ := (hact i).1 hi
      exact (hNm i).2 ⟨hiy, hiE⟩
    · by_cases hyC : y ∈ C
      · right
        by_cases hu : uC = true
        · right
          intro i hi
          obtain ⟨hiN, hiC⟩ := Finset.mem_sdiff.1 hi
          obtain ⟨hiy, hiE⟩ := (hNm i).1 hiN
          have hcm := hcen _ hiE
          have hmem := hcm.1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h1 | h1
          · exact (hact i).2 ⟨hiy, hiE, Or.inl ⟨h1, hu⟩⟩
          · exact absurd (h1 ▸ hcm.2) hiC
        · left
          refine Finset.disjoint_left.2 fun i hiS hiN => ?_
          obtain ⟨hiN', hiC⟩ := Finset.mem_sdiff.1 hiN
          obtain ⟨hiy, hiE, h2⟩ := (hact i).1 hiS
          rcases h2 with h2 | h2
          · exact hu h2.2
          · exact hiC (h2.1 ▸ (hcen _ hiE).2)
      · left; exact hyC
  · rintro ⟨hSN, hcond⟩
    have hex : ∃ cen : Finset (Fin n) → Fin n, (∀ e ∈ E, cen e ∈ e ∧ cen e ∈ C) ∧
        (∀ i, i ≠ y → i ∈ C → cen {y, i} = i) ∧ (∀ i, i ∉ C → cen {y, i} = y) := by
      refine ⟨fun e => if h : ∃ v ∈ e, v ∈ C ∧ v ≠ y then h.choose else y, ?_, ?_, ?_⟩
      · intro e he
        by_cases h : ∃ v ∈ e, v ∈ C ∧ v ≠ y
        · beta_reduce
          rw [dif_pos h]
          exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
        · beta_reduce
          rw [dif_neg h]
          obtain ⟨v, hv, hvC⟩ := hcov e he
          by_cases hvy : v = y
          · subst hvy; exact ⟨hv, hvC⟩
          · exact absurd ⟨v, hv, hvC, hvy⟩ h
      · intro i hiy hiC
        have h : ∃ v ∈ ({y, i} : Finset (Fin n)), v ∈ C ∧ v ≠ y := ⟨i, by simp, hiC, hiy⟩
        beta_reduce
        rw [dif_pos h]
        have aux : ∀ h' : ∃ v ∈ ({y, i} : Finset (Fin n)), v ∈ C ∧ v ≠ y, h'.choose = i := by
          intro h'
          have hs := h'.choose_spec
          rcases Finset.mem_insert.1 hs.1 with hm | hm
          · exact absurd hm hs.2.2
          · exact Finset.mem_singleton.1 hm
        exact aux _
      · intro i hiC
        have h : ¬ ∃ v ∈ ({y, i} : Finset (Fin n)), v ∈ C ∧ v ≠ y := by
          rintro ⟨v, hv, hvC, hvy⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with hv | hv
          · exact hvy hv
          · exact hiC (hv ▸ hvC)
        beta_reduce
        rw [dif_neg h]
    obtain ⟨cen, hP1, hP2, hP3⟩ := hex
    obtain ⟨uC, huC⟩ : ∃ u : Bool, u = true ↔
        (((Finset.univ : Finset (Fin n)).filter
          (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)) \ C ⊆ S) :=
      ⟨decide ((((Finset.univ : Finset (Fin n)).filter
          (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)) \ C ⊆ S)), decide_eq_true_iff⟩
    obtain ⟨uL, huL⟩ : ∃ u : Fin n → Bool, ∀ i, u i = true ↔ i ∈ S :=
      ⟨fun i => decide (i ∈ S), by simp⟩
    refine ⟨cen, uC, uL, hP1, fun X z => ?_⟩
    refine (PEqualNP.Outside.L_meta_36442.key hE cen uC uL y (fun e he => (hP1 e he).1) X z).trans ?_
    have hact : ∀ i, (i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E ∧
        ((cen {y, i} = y ∧ uC = true) ∨ (cen {y, i} = i ∧ uL i = true))) ↔ i ∈ S := by
      intro i
      constructor
      · rintro ⟨hiy, hiE, h⟩
        by_cases hiC : i ∈ C
        · rcases h with h | h
          · exact absurd ((hP2 i hiy hiC).symm.trans h.1) hiy
          · exact (huL i).1 h.2
        · rcases h with h | h
          · exact (huC.1 h.2) (Finset.mem_sdiff.2 ⟨(hNm i).2 ⟨hiy, hiE⟩, hiC⟩)
          · exact absurd (h.1 ▸ (hP1 _ hiE).2) hiC
      · intro hiS
        have hiN := hSN hiS
        obtain ⟨hiy, hiE⟩ := (hNm i).1 hiN
        by_cases hiC : i ∈ C
        · exact ⟨hiy, hiE, Or.inr ⟨hP2 i hiy hiC, (huL i).2 hiS⟩⟩
        · refine ⟨hiy, hiE, Or.inl ⟨hP3 i hiC, huC.2 ?_⟩⟩
          rcases hcond with hyC | hdis | hsub
          · obtain ⟨v, hv, hvC⟩ := hcov _ hiE
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with hv | hv
            · exact absurd (hv ▸ hvC) hyC
            · exact absurd (hv ▸ hvC) hiC
          · exact absurd (Finset.mem_sdiff.2 ⟨hiN, hiC⟩) (Finset.disjoint_left.1 hdis hiS)
          · exact hsub
    constructor
    · rintro (h | ⟨hz, i, hiX, ha⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hz, i, (hact i).1 ha, hiX⟩
    · rintro (h | ⟨hz, i, hiS, hiX⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hz, i, hiX, (hact i).2 hiS⟩
