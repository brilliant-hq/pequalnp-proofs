import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1129

open Finset

abbrev hd {m : ℕ} (x : Finset (Fin m)) (C : Finset (Fin m × Bool)) : Prop :=
  ∃ l ∈ C, decide (l.1 ∈ x) = l.2

abbrev sm {m : ℕ} (A : Finset (Fin m) → ℕ) (p : Finset (Fin m) → Prop) [DecidablePred p] : ℕ :=
  ((univ : Finset (Finset (Fin m))).filter p).sum A

theorem sm_congr {m : ℕ} (A : Finset (Fin m) → ℕ) (p q : Finset (Fin m) → Prop)
    [DecidablePred p] [DecidablePred q] (h : ∀ x, p x ↔ q x) : sm A p = sm A q := by
  unfold sm
  rw [filter_congr (fun x _ => h x)]

theorem sm_split {m : ℕ} (A : Finset (Fin m) → ℕ) (p q : Finset (Fin m) → Prop)
    [DecidablePred p] [DecidablePred q] :
    sm A (fun x => p x ∧ q x) + sm A (fun x => p x ∧ ¬ q x) = sm A p := by
  unfold sm
  rw [← sum_filter_add_sum_filter_not (univ.filter p) q A, filter_filter, filter_filter]

theorem sm_pos {m : ℕ} (A : Finset (Fin m) → ℕ) (p : Finset (Fin m) → Prop) [DecidablePred p] :
    0 < sm A p ↔ ∃ x, p x ∧ 0 < A x := by
  unfold sm
  rw [Nat.pos_iff_ne_zero, Ne, sum_eq_zero_iff]
  simp only [mem_filter, mem_univ, true_and]
  push Not
  simp only [Nat.pos_iff_ne_zero]

theorem pin_iff {m : ℕ} (x S B : Finset (Fin m)) (hB : B ⊆ S) :
    x ∩ S = B ↔ ∀ i ∈ S, (i ∈ x ↔ i ∈ B) := by
  constructor
  · rintro rfl i hi
    simp [hi]
  · intro h
    ext i
    simp only [mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      exact (h i h2).1 h1
    · intro hi
      exact ⟨(h i (hB hi)).2 hi, hB hi⟩

theorem dec_ne_iff (p q : Prop) [Decidable p] [Decidable q] :
    (decide p ≠ !decide q) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem unit_formula {m : ℕ} (S B : Finset (Fin m)) (hB : B ⊆ S) (x : Finset (Fin m)) :
    (∀ C ∈ S.image (fun i => ({(i, decide (i ∈ B))} : Finset (Fin m × Bool))), hd x C) ↔
      x ∩ S = B := by
  rw [pin_iff x S B hB]
  constructor
  · intro h i hi
    obtain ⟨l, hl, h'⟩ := h _ (mem_image_of_mem _ hi)
    rw [mem_singleton] at hl
    subst hl
    exact decide_eq_decide.1 h'
  · intro h C hC
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hC
    exact ⟨_, mem_singleton_self _, decide_eq_decide.2 (h i hi)⟩

theorem sat_back {m : ℕ} (T : Finset (Fin m)) (t : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S,
      0 < sm A (fun x => x ∩ S = B) → 0 < sm D (fun x => x ∩ S = B))
    (F : Finset (Finset (Fin m × Bool))) (hF : F.card ≤ t) (hT : ∀ C ∈ F, ∀ l ∈ C, l.1 ∈ T)
    (hA : 0 < sm A (fun x => ∀ C ∈ F, hd x C)) : 0 < sm D (fun x => ∀ C ∈ F, hd x C) := by
  obtain ⟨x, hx, hAx⟩ := (sm_pos _ _).1 hA
  choose f hfC hfP using hx
  let S : Finset (Fin m) := F.attach.image (fun C => (f C.1 C.2).1)
  have hST : S ⊆ T := by
    intro i hi
    obtain ⟨C, _, rfl⟩ := mem_image.1 hi
    exact hT C.1 C.2 _ (hfC C.1 C.2)
  have hSc : S.card ≤ t := card_image_le.trans ((le_of_eq card_attach).trans hF)
  have hpA : 0 < sm A (fun y => y ∩ S = x ∩ S) := (sm_pos _ _).2 ⟨x, rfl, hAx⟩
  obtain ⟨y, hy, hDy⟩ := (sm_pos _ _).1 (H S hST hSc (x ∩ S) inter_subset_right hpA)
  refine (sm_pos _ _).2 ⟨y, fun C hC => ⟨f C hC, hfC C hC, ?_⟩, hDy⟩
  have hiS : (f C hC).1 ∈ S := mem_image.2 ⟨⟨C, hC⟩, mem_attach _ _, rfl⟩
  have h1 := Finset.ext_iff.1 hy (f C hC).1
  simp only [mem_inter, hiS, and_true] at h1
  rw [← hfP C hC]
  exact decide_eq_decide.2 h1

theorem fwd_ind {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ F : Finset (Finset (Fin m × Bool)), F.card ≤ t →
      (∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      sm A (fun x => ∀ C ∈ F, hd x C) = sm D (fun x => ∀ C ∈ F, hd x C))
    (G : Finset (Finset (Fin m × Bool))) :
    ∀ F : Finset (Finset (Fin m × Bool)), F.card + G.card ≤ t →
      (∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) → (∀ C ∈ G, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      sm A (fun x => (∀ C ∈ F, hd x C) ∧ ∀ C ∈ G, ¬ hd x C) =
      sm D (fun x => (∀ C ∈ F, hd x C) ∧ ∀ C ∈ G, ¬ hd x C) := by
  induction G using Finset.induction_on with
  | empty =>
    intro F hc hF _
    have e : ∀ E : Finset (Fin m) → ℕ, sm E (fun x => (∀ C ∈ F, hd x C) ∧
        ∀ C ∈ (∅ : Finset (Finset (Fin m × Bool))), ¬ hd x C) =
        sm E (fun x => ∀ C ∈ F, hd x C) := fun E => sm_congr _ _ _ (fun x => by simp)
    rw [e, e]
    exact H F (by simpa using hc) hF
  | insert C G hCG ih =>
    intro F hc hF hG
    have hC := hG C (mem_insert_self C G)
    have hG' : ∀ C' ∈ G, C'.card ≤ w ∧ ∀ l ∈ C', l.1 ∈ T :=
      fun C' h => hG C' (mem_insert_of_mem h)
    have e1 : ∀ E : Finset (Fin m) → ℕ,
        sm E (fun x => ((∀ C' ∈ F, hd x C') ∧ ∀ C' ∈ G, ¬ hd x C') ∧ hd x C) =
        sm E (fun x => (∀ C' ∈ insert C F, hd x C') ∧ ∀ C' ∈ G, ¬ hd x C') :=
      fun E => sm_congr _ _ _ (fun x => by simp only [forall_mem_insert]; tauto)
    have e2 : ∀ E : Finset (Fin m) → ℕ,
        sm E (fun x => ((∀ C' ∈ F, hd x C') ∧ ∀ C' ∈ G, ¬ hd x C') ∧ ¬ hd x C) =
        sm E (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ C' ∈ insert C G, ¬ hd x C') :=
      fun E => sm_congr _ _ _ (fun x => by simp only [forall_mem_insert]; tauto)
    have sA := sm_split A (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ C' ∈ G, ¬ hd x C') (fun x => hd x C)
    have sD := sm_split D (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ C' ∈ G, ¬ hd x C') (fun x => hd x C)
    beta_reduce at sA sD
    rw [e1, e2] at sA sD
    have hcard := card_insert_of_notMem hCG
    have hle := card_insert_le C F
    have i1 := ih F (by omega) hF hG'
    have i2 := ih (insert C F) (by omega) (by
      intro C' h
      rcases mem_insert.1 h with rfl | h
      · exact hC
      · exact hF C' h) hG'
    omega

theorem packets {m : ℕ} (w : ℕ) (B : Finset (Fin m)) : ∀ (t : ℕ) (S : Finset (Fin m)),
    S.card ≤ t * w →
    ∃ G : Finset (Finset (Fin m × Bool)), G.card ≤ t ∧
      (∀ C ∈ G, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ S) ∧
      ∀ x, (∀ C ∈ G, ¬ hd x C) ↔ ∀ i ∈ S, (i ∈ x ↔ i ∈ B) := by
  intro t
  induction t with
  | zero =>
    intro S hS
    have : S = ∅ := card_eq_zero.1 (by simpa using hS)
    subst this
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ t ih =>
    intro S hS
    obtain ⟨P, hPS, hPc⟩ := exists_subset_card_eq (min_le_right w S.card)
    have hmul : (t + 1) * w = t * w + w := by ring
    obtain ⟨G, hGc, hG, hGx⟩ := ih (S \ P) (by
      rw [card_sdiff_of_subset hPS]
      omega)
    refine ⟨insert (P.image (fun i => (i, !decide (i ∈ B)))) G, ?_, ?_, ?_⟩
    · exact (card_insert_le _ _).trans (by omega)
    · intro C hC
      rcases mem_insert.1 hC with rfl | hC
      · refine ⟨card_image_le.trans (by omega), ?_⟩
        intro l hl
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hl
        exact hPS hi
      · obtain ⟨h1, h2⟩ := hG C hC
        exact ⟨h1, fun l hl => (mem_sdiff.1 (h2 l hl)).1⟩
    · intro x
      rw [forall_mem_insert, hGx x]
      have e : (¬ hd x (P.image (fun i => (i, !decide (i ∈ B))))) ↔
          ∀ i ∈ P, (i ∈ x ↔ i ∈ B) := by
        constructor
        · intro h i hi
          refine (dec_ne_iff _ _).1 ?_
          intro h'
          exact h ⟨(i, !decide (i ∈ B)), mem_image_of_mem _ hi, h'⟩
        · rintro h ⟨l, hl, h'⟩
          obtain ⟨i, hi, rfl⟩ := mem_image.1 hl
          exact (dec_ne_iff _ _).2 (h i hi) h'
      rw [e]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        by_cases hiP : i ∈ P
        · exact h1 i hiP
        · exact h2 i (mem_sdiff.2 ⟨hi, hiP⟩)
      · intro h
        exact ⟨fun i hi => h i (hPS hi), fun i hi => h i (mem_sdiff.1 hi).1⟩

theorem lit_eq {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S,
      sm A (fun x => x ∩ S = B) = sm D (fun x => x ∩ S = B))
    (L : Finset (Fin m × Bool)) (hL : ∀ l ∈ L, l.1 ∈ T) (hc : L.card ≤ t * w) :
    sm A (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
      sm D (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) := by
  by_cases hcomp : ∃ i, (i, true) ∈ L ∧ (i, false) ∈ L
  · obtain ⟨i, h1, h2⟩ := hcomp
    have e : ∀ E : Finset (Fin m) → ℕ, sm E (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
        sm E (fun _ => False) := by
      intro E
      apply sm_congr
      intro x
      constructor
      · intro h
        by_cases hx : i ∈ x
        · exact h _ h1 (by simp [hx])
        · exact h _ h2 (by simp [hx])
      · intro h
        exact h.elim
    rw [e, e]
    simp [sm]
  · push Not at hcomp
    let S : Finset (Fin m) := L.image Prod.fst
    let B : Finset (Fin m) := (L.filter (fun l => l.2 = false)).image Prod.fst
    have hB : B ⊆ S := image_subset_image (filter_subset _ _)
    have hST : S ⊆ T := by
      intro i hi
      obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
      exact hL l hl
    have hSc : S.card ≤ t * w := card_image_le.trans hc
    have memB : ∀ i, i ∈ B ↔ (i, false) ∈ L := by
      intro i
      constructor
      · intro hi
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
        rw [mem_filter] at hl
        have : l = (l.1, false) := Prod.ext rfl hl.2
        rw [← this]
        exact hl.1
      · intro hi
        exact mem_image.2 ⟨(i, false), mem_filter.2 ⟨hi, rfl⟩, rfl⟩
    have e : ∀ E : Finset (Fin m) → ℕ, sm E (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
        sm E (fun x => x ∩ S = B) := by
      intro E
      apply sm_congr
      intro x
      rw [pin_iff x S B hB]
      constructor
      · intro h i hi
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
        obtain ⟨j, b⟩ := l
        cases b
        · have := h _ hl
          simp at this
          exact ⟨fun _ => (memB j).2 hl, fun _ => this⟩
        · have := h _ hl
          simp at this
          exact ⟨fun hj => (this hj).elim, fun hj => ((hcomp j hl) ((memB j).1 hj)).elim⟩
      · intro h l hl
        obtain ⟨j, b⟩ := l
        have hj : j ∈ S := mem_image.2 ⟨(j, b), hl, rfl⟩
        cases b
        · have : j ∈ x := (h j hj).2 ((memB j).2 hl)
          simp [this]
        · have : j ∉ x := fun hx => hcomp j hl ((memB j).1 ((h j hj).1 hx))
          simp [this]
    rw [e, e]
    exact H S hST hSc B hB

theorem bwd_ind {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ L : Finset (Fin m × Bool), (∀ l ∈ L, l.1 ∈ T) → L.card ≤ t * w →
      sm A (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
        sm D (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2))
    (F : Finset (Finset (Fin m × Bool))) :
    ∀ L : Finset (Fin m × Bool), (∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      (∀ l ∈ L, l.1 ∈ T) → L.card + w * F.card ≤ t * w →
      sm A (fun x => (∀ C ∈ F, hd x C) ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
      sm D (fun x => (∀ C ∈ F, hd x C) ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) := by
  induction F using Finset.induction_on with
  | empty =>
    intro L _ hL hc
    have e : ∀ E : Finset (Fin m) → ℕ,
        sm E (fun x => (∀ C ∈ (∅ : Finset (Finset (Fin m × Bool))), hd x C) ∧
          ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) =
        sm E (fun x => ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) :=
      fun E => sm_congr _ _ _ (fun x => by simp)
    rw [e, e]
    exact H L hL (by simpa using hc)
  | insert C F hCF ih =>
    intro L hF hL hc
    have hC := hF C (mem_insert_self C F)
    have hF' : ∀ C' ∈ F, C'.card ≤ w ∧ ∀ l ∈ C', l.1 ∈ T :=
      fun C' h => hF C' (mem_insert_of_mem h)
    have e1 : ∀ E : Finset (Fin m) → ℕ,
        sm E (fun x => ((∀ C' ∈ F, hd x C') ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) ∧ hd x C) =
        sm E (fun x => (∀ C' ∈ insert C F, hd x C') ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) :=
      fun E => sm_congr _ _ _ (fun x => by simp only [forall_mem_insert]; tauto)
    have e2 : ∀ E : Finset (Fin m) → ℕ,
        sm E (fun x => ((∀ C' ∈ F, hd x C') ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) ∧ ¬ hd x C) =
        sm E (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ l ∈ L ∪ C, decide (l.1 ∈ x) ≠ l.2) := by
      intro E
      apply sm_congr
      intro x
      have hn : ¬ hd x C ↔ ∀ l ∈ C, decide (l.1 ∈ x) ≠ l.2 := by simp [hd]
      rw [hn]
      simp only [mem_union]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun l hl => hl.elim (h2 l) (h3 l)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun l hl => h2 l (Or.inl hl)⟩, fun l hl => h2 l (Or.inr hl)⟩
    have sA := sm_split A (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2)
      (fun x => hd x C)
    have sD := sm_split D (fun x => (∀ C' ∈ F, hd x C') ∧ ∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2)
      (fun x => hd x C)
    beta_reduce at sA sD
    rw [e1, e2] at sA sD
    have hcard := card_insert_of_notMem hCF
    have hu := card_union_le L C
    have hmul : w * (insert C F).card = w * F.card + w := by rw [hcard, mul_add, mul_one]
    have i1 := ih L hF' hL (by omega)
    have i2 := ih (L ∪ C) hF' (by
      intro l hl
      rcases mem_union.1 hl with h | h
      · exact hL l h
      · exact hC.2 l h) (by omega)
    omega

theorem sat_fwd {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (hw : 0 < w) (A D : Finset (Fin m) → ℕ)
    (H : ∀ F : Finset (Finset (Fin m × Bool)),
      (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      (0 < sm A (fun x => ∀ C ∈ F, hd x C) ↔ 0 < sm D (fun x => ∀ C ∈ F, hd x C))) :
    ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S,
      (0 < sm A (fun x => x ∩ S = B) ↔ 0 < sm D (fun x => x ∩ S = B)) := by
  intro S hST hSc B hB
  have hv := H (S.image (fun i => ({(i, decide (i ∈ B))} : Finset (Fin m × Bool))))
    ⟨card_image_le.trans hSc, by
      intro C hC
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hC
      refine ⟨by rw [card_singleton]; exact hw, ?_⟩
      intro l hl
      rw [mem_singleton] at hl
      subst hl
      exact hST hi⟩
  have e : ∀ E : Finset (Fin m) → ℕ,
      sm E (fun x => ∀ C ∈ S.image (fun i => ({(i, decide (i ∈ B))} : Finset (Fin m × Bool))),
        hd x C) = sm E (fun x => x ∩ S = B) :=
    fun E => sm_congr _ _ _ (fun x => unit_formula S B hB x)
  rw [← e A, ← e D]
  exact hv

theorem sat_bwd {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S,
      (0 < sm A (fun x => x ∩ S = B) ↔ 0 < sm D (fun x => x ∩ S = B))) :
    ∀ F : Finset (Finset (Fin m × Bool)),
      (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      (0 < sm A (fun x => ∀ C ∈ F, hd x C) ↔ 0 < sm D (fun x => ∀ C ∈ F, hd x C)) :=
  fun F hF => ⟨sat_back T t A D (fun S h1 h2 B h3 => (H S h1 h2 B h3).1) F hF.1
      (fun C hC => (hF.2 C hC).2),
    sat_back T t D A (fun S h1 h2 B h3 => (H S h1 h2 B h3).2) F hF.1
      (fun C hC => (hF.2 C hC).2)⟩

theorem cnt_fwd {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ F : Finset (Finset (Fin m × Bool)),
      (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      sm A (fun x => ∀ C ∈ F, hd x C) = sm D (fun x => ∀ C ∈ F, hd x C)) :
    ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S,
      sm A (fun x => x ∩ S = B) = sm D (fun x => x ∩ S = B) := by
  intro S hST hSc B hB
  obtain ⟨G, hGc, hG, hGx⟩ := packets w B t S hSc
  have key := fwd_ind T t w A D (fun F h1 h2 => H F ⟨h1, h2⟩) G ∅ (by simpa using hGc)
    (by simp) (fun C hC => ⟨(hG C hC).1, fun l hl => hST ((hG C hC).2 l hl)⟩)
  have e : ∀ E : Finset (Fin m) → ℕ,
      sm E (fun x => (∀ C ∈ (∅ : Finset (Finset (Fin m × Bool))), hd x C) ∧
        ∀ C ∈ G, ¬ hd x C) = sm E (fun x => x ∩ S = B) :=
    fun E => sm_congr _ _ _ (fun x => by rw [pin_iff x S B hB, ← hGx x]; simp)
  rw [e, e] at key
  exact key

theorem cnt_bwd {m : ℕ} (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (H : ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S,
      sm A (fun x => x ∩ S = B) = sm D (fun x => x ∩ S = B)) :
    ∀ F : Finset (Finset (Fin m × Bool)),
      (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      sm A (fun x => ∀ C ∈ F, hd x C) = sm D (fun x => ∀ C ∈ F, hd x C) := by
  intro F hF
  have key := bwd_ind T t w A D (lit_eq T t w A D H) F ∅ hF.2 (by simp) (by
    rw [card_empty, zero_add, Nat.mul_comm t w]
    exact Nat.mul_le_mul_left w hF.1)
  have e : ∀ E : Finset (Fin m) → ℕ,
      sm E (fun x => (∀ C ∈ F, hd x C) ∧
        ∀ l ∈ (∅ : Finset (Fin m × Bool)), decide (l.1 ∈ x) ≠ l.2) =
      sm E (fun x => ∀ C ∈ F, hd x C) := fun E => sm_congr _ _ _ (fun x => by simp)
  rw [e, e] at key
  exact key

end PEqualNP.Outside.L_lib_1129

open PEqualNP.Outside.L_lib_1129 in
theorem PEqualNP.Outside.L_lib_1129 : ∀ (m : Nat) (T : Finset (Fin m)) (t w : Nat), 0 < w →

  let Clause := Finset (Fin m × Bool)
  let holds := fun (x : Finset (Fin m)) (C : Clause) =>
    ∃ l ∈ C, decide (l.1 ∈ x) = l.2
  let valid := fun (F : Finset Clause) =>
    F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T

  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let total := fun (A : Finset (Fin m) → Nat) (F : Finset Clause) =>
    (cube.filter (fun x => ∀ C ∈ F, holds x C)).sum A
  let pin := fun (A : Finset (Fin m) → Nat) (S B : Finset (Fin m)) =>
    (cube.filter (fun x => x ∩ S = B)).sum A
  ∀ A D : Finset (Fin m) → Nat,
    ((∀ F, valid F → (0 < total A F ↔ 0 < total D F)) ↔
      ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S, (0 < pin A S B ↔ 0 < pin D S B)) ∧
    ((∀ F, valid F → total A F = total D F) ↔
      ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S, pin A S B = pin D S B)
 := by
  intro m T t w hw Clause holds valid cube total pin A D
  exact ⟨⟨sat_fwd T t w hw A D, sat_bwd T t w A D⟩, ⟨cnt_fwd T t w A D, cnt_bwd T t w A D⟩⟩
