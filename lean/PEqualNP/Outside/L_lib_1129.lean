import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1129_aux

open Finset

variable {m : ℕ}

def Mx (A : Finset (Fin m) → ℕ) (L : Finset (Fin m × Bool))
    (H : Finset (Finset (Fin m × Bool))) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter (fun x =>
    (∀ l ∈ L, decide (l.1 ∈ x) ≠ l.2) ∧ ∀ C ∈ H, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A

theorem Mx_step (A : Finset (Fin m) → ℕ) (L C : Finset (Fin m × Bool))
    (H : Finset (Finset (Fin m × Bool))) :
    Mx A L (insert C H) + Mx A (L ∪ C) H = Mx A L H := by
  simp only [Mx, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.forall_mem_insert, Finset.forall_mem_union]
  have e3 : (∀ l ∈ C, decide (l.1 ∈ x) ≠ l.2) ↔ ¬ ∃ l ∈ C, decide (l.1 ∈ x) = l.2 := by
    simp only [ne_eq, not_exists, not_and]
  simp only [e3]
  split_ifs <;> first | (exfalso; tauto) | simp

theorem total_eq (A : Finset (Fin m) → ℕ) (F : Finset (Finset (Fin m × Bool))) :
    ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A = Mx A ∅ F := by
  unfold Mx
  congr 1
  apply Finset.filter_congr
  intro x _
  simp

theorem pin_eq (A : Finset (Fin m) → ℕ) (S B : Finset (Fin m)) (hB : B ⊆ S) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A =
      Mx A (S.image (fun i => (i, decide (i ∉ B)))) ∅ := by
  unfold Mx
  congr 1
  apply Finset.filter_congr
  intro x _
  have e : ∀ C ∈ (∅ : Finset (Finset (Fin m × Bool))), ∃ l ∈ C, decide (l.1 ∈ x) = l.2 := by
    simp
  refine Iff.trans ?_ (and_iff_left e).symm
  simp only [Finset.forall_mem_image]
  constructor
  · intro h i hi
    subst h
    simp [hi]
  · intro h
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      have := @h i h2
      by_contra hc
      simp [h1, hc] at this
    · intro hi
      have := @h i (hB hi)
      refine ⟨?_, hB hi⟩
      by_contra hc
      simp [hi, hc] at this

theorem base_eq (A : Finset (Fin m) → ℕ) (L : Finset (Fin m × Bool)) :
    (∃ i, (i, true) ∈ L ∧ (i, false) ∈ L ∧ Mx A L ∅ = 0) ∨
    Mx A L ∅ = ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun x => x ∩ L.image Prod.fst = (L.filter (fun l => l.2 = false)).image Prod.fst)).sum A := by
  by_cases hc : ∃ i, (i, true) ∈ L ∧ (i, false) ∈ L
  · obtain ⟨i, h1, h2⟩ := hc
    left
    refine ⟨i, h1, h2, ?_⟩
    unfold Mx
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter] at hx
    have a1 := hx.2.1 _ h1
    have a2 := hx.2.1 _ h2
    simp at a1 a2
    exact absurd a2 a1
  · right
    push Not at hc
    unfold Mx
    congr 1
    apply Finset.filter_congr
    intro x _
    have e : ∀ C ∈ (∅ : Finset (Finset (Fin m × Bool))), ∃ l ∈ C, decide (l.1 ∈ x) = l.2 := by
      simp
    refine Iff.trans (and_iff_left e) ?_
    constructor
    · intro h
      ext i
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Prod.exists,
        exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨hi, b, hb⟩
        have := h _ hb
        cases b
        · exact hb
        · simp [hi] at this
      · intro hi
        have := h _ hi
        simp at this
        exact ⟨this, false, hi⟩
    · intro h l hl
      obtain ⟨i, b⟩ := l
      have hm : i ∈ x ∩ L.image Prod.fst ↔ i ∈ (L.filter (fun l => l.2 = false)).image Prod.fst := by
        rw [h]
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Prod.exists,
        exists_and_right, exists_eq_right] at hm
      cases b
      · simp
        exact (hm.2 hl).1
      · simp
        intro hix
        exact hc i hl (hm.1 ⟨hix, true, hl⟩)

theorem base_zero (A : Finset (Fin m) → ℕ) (L : Finset (Fin m × Bool)) (i : Fin m)
    (h1 : (i, true) ∈ L) (h2 : (i, false) ∈ L) : Mx A L ∅ = 0 := by
  unfold Mx
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter] at hx
  have a1 := hx.2.1 _ h1
  have a2 := hx.2.1 _ h2
  simp at a1 a2
  exact absurd a2 a1

theorem from_pin (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (hp : ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S,
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A =
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum D) :
    ∀ H : Finset (Finset (Fin m × Bool)), ∀ L : Finset (Fin m × Bool), (∀ l ∈ L, l.1 ∈ T) →
      (∀ C ∈ H, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) → L.card + H.card * w ≤ t * w →
      Mx A L H = Mx D L H := by
  intro H
  induction H using Finset.induction_on with
  | empty =>
    intro L hL _ hc
    by_cases hi : ∃ i, (i, true) ∈ L ∧ (i, false) ∈ L
    · obtain ⟨i, h1, h2⟩ := hi
      rw [base_zero A L i h1 h2, base_zero D L i h1 h2]
    · have eA := (base_eq A L).resolve_left (fun ⟨i, h1, h2, _⟩ => hi ⟨i, h1, h2⟩)
      have eD := (base_eq D L).resolve_left (fun ⟨i, h1, h2, _⟩ => hi ⟨i, h1, h2⟩)
      rw [eA, eD]
      apply hp
      · intro i hi'
        simp only [Finset.mem_image] at hi'
        obtain ⟨l, hl, rfl⟩ := hi'
        exact hL l hl
      · simp only [Finset.card_empty, zero_mul, add_zero] at hc
        exact le_trans Finset.card_image_le hc
      · exact Finset.image_subset_image (Finset.filter_subset _ _)
  | insert C H hCH ih =>
    intro L hL hH hc
    have sA := Mx_step A L C H
    have sD := Mx_step D L C H
    have hH' : ∀ C ∈ H, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T := fun C' hC' =>
      hH C' (Finset.mem_insert_of_mem hC')
    have hC := hH C (Finset.mem_insert_self C H)
    rw [Finset.card_insert_of_notMem hCH] at hc
    have e1 := ih L hL hH' (by nlinarith)
    have e2 := ih (L ∪ C) (by
      intro l hl
      rcases Finset.mem_union.1 hl with h | h
      · exact hL l h
      · exact hC.2 l h) hH' (by
        have := Finset.card_union_le L C
        nlinarith)
    omega

theorem to_pin (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (htot : ∀ F : Finset (Finset (Fin m × Bool)), F.card ≤ t →
      (∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) → Mx A ∅ F = Mx D ∅ F) :
    ∀ k : ℕ, ∀ L : Finset (Fin m × Bool), ∀ H : Finset (Finset (Fin m × Bool)),
      (∀ l ∈ L, l.1 ∈ T) → (∀ C ∈ H, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      L.card ≤ k * w → k + H.card ≤ t → Mx A L H = Mx D L H := by
  intro k
  induction k with
  | zero =>
    intro L H _ hH hL hk
    simp only [zero_mul, Nat.le_zero, Finset.card_eq_zero] at hL
    subst hL
    exact htot H (by omega) hH
  | succ k ih =>
    intro L H hLT hH hL hk
    obtain ⟨U, C, hUC, hCL, hCw, hUL, hUk⟩ : ∃ U C : Finset (Fin m × Bool), U ∪ C = L ∧ C ⊆ L ∧
        C.card ≤ w ∧ U ⊆ L ∧ U.card ≤ k * w := by
      by_cases hw : L.card ≤ w
      · exact ⟨∅, L, by simp, le_refl _, hw, Finset.empty_subset _, by simp⟩
      · obtain ⟨C, hC, hCc⟩ := Finset.exists_subset_card_eq (le_of_lt (not_le.1 hw))
        refine ⟨L \ C, C, Finset.sdiff_union_of_subset hC, hC, le_of_eq hCc,
          Finset.sdiff_subset, ?_⟩
        rw [Finset.card_sdiff_of_subset hC, hCc]
        have : (k + 1) * w = k * w + w := by ring
        omega
    subst hUC
    have sA := Mx_step A U C H
    have sD := Mx_step D U C H
    have hUT : ∀ l ∈ U, l.1 ∈ T := fun l hl => hLT l (hUL hl)
    have e1 := ih U H hUT hH hUk (by omega)
    have e2 := ih U (insert C H) hUT (by
      intro C' hC'
      rcases Finset.mem_insert.1 hC' with h | h
      · subst h
        exact ⟨hCw, fun l hl => hLT l (hCL hl)⟩
      · exact hH C' h) hUk (by
        have := Finset.card_insert_le C H
        omega)
    omega

theorem pos_bwd (T : Finset (Fin m)) (t w : ℕ) (A D : Finset (Fin m) → ℕ)
    (hp : ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S,
      0 < ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A →
      0 < ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum D)
    (F : Finset (Finset (Fin m × Bool)))
    (hF : F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) :
    0 < ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A →
    0 < ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum D := by
  intro h
  rw [Finset.sum_pos_iff] at h ⊢
  obtain ⟨x, hx, hAx⟩ := h
  rw [Finset.mem_filter] at hx
  have hx2 := hx.2
  choose f hf hfx using hx2
  set S : Finset (Fin m) := F.attach.image (fun C => (f C.1 C.2).1) with hSdef
  have hST : S ⊆ T := by
    intro i hi
    rw [hSdef, Finset.mem_image] at hi
    obtain ⟨C, _, rfl⟩ := hi
    exact (hF.2 C.1 C.2).2 _ (hf C.1 C.2)
  have hSc : S.card ≤ t := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_attach]
    exact hF.1
  have hpos := hp S hST hSc (x ∩ S) Finset.inter_subset_right
    (Finset.sum_pos_iff.2 ⟨x, by simp, hAx⟩)
  rw [Finset.sum_pos_iff] at hpos
  obtain ⟨y, hy, hDy⟩ := hpos
  refine ⟨y, ?_, hDy⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  intro C hC
  refine ⟨f C hC, hf C hC, ?_⟩
  have hiS : (f C hC).1 ∈ S := by
    rw [hSdef, Finset.mem_image]
    exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩
  have hyx : (f C hC).1 ∈ y ↔ (f C hC).1 ∈ x := by
    have h1 : (f C hC).1 ∈ y ∩ S ↔ (f C hC).1 ∈ x ∩ S := by rw [hy]
    simpa [hiS] using h1
  rw [← hfx C hC]
  exact decide_eq_decide.2 hyx

theorem unit_eq (A : Finset (Fin m) → ℕ) (S B : Finset (Fin m)) (hB : B ⊆ S) :
    ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun x => ∀ C ∈ S.image (fun i => ({(i, decide (i ∈ B))} : Finset (Fin m × Bool))),
        ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A =
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A := by
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [Finset.forall_mem_image, Finset.mem_singleton, exists_eq_left, decide_eq_decide]
  constructor
  · intro h
    ext i
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      exact (@h i h2).1 h1
    · intro hi
      exact ⟨(@h i (hB hi)).2 hi, hB hi⟩
  · intro h i hi
    subst h
    simp [hi]

theorem main (m : ℕ) (T : Finset (Fin m)) (t w : ℕ) (hw : 0 < w) (A D : Finset (Fin m) → ℕ) :
    ((∀ F : Finset (Finset (Fin m × Bool)), (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      (0 < ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A ↔
       0 < ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum D)) ↔
      ∀ S ⊆ T, S.card ≤ t → ∀ B ⊆ S,
        (0 < ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A ↔
         0 < ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum D)) ∧
    ((∀ F : Finset (Finset (Fin m × Bool)), (F.card ≤ t ∧ ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T) →
      ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum A =
       ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).sum D) ↔
      ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S,
        ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum A =
         ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => x ∩ S = B)).sum D) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h S hS hc B hB
    rw [← unit_eq A S B hB, ← unit_eq D S B hB]
    apply h
    refine ⟨le_trans Finset.card_image_le hc, ?_⟩
    intro C hC
    rw [Finset.mem_image] at hC
    obtain ⟨i, hi, rfl⟩ := hC
    refine ⟨by simp; omega, ?_⟩
    intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact hS hi
  · intro h F hF
    exact ⟨pos_bwd T t w A D (fun S hS hc B hB => (h S hS hc B hB).1) F hF,
      pos_bwd T t w D A (fun S hS hc B hB => (h S hS hc B hB).2) F hF⟩
  · intro h S hS hc B hB
    rw [pin_eq A S B hB, pin_eq D S B hB]
    refine to_pin T t w A D (fun F hF hv => ?_) t _ ∅ ?_ (by simp) ?_ (by simp)
    · rw [← total_eq, ← total_eq]
      exact h F ⟨hF, hv⟩
    · intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      exact hS hi
    · exact le_trans Finset.card_image_le hc
  · intro h F hF
    rw [total_eq, total_eq]
    refine from_pin T t w A D h F ∅ (by simp) hF.2 ?_
    simp only [Finset.card_empty, zero_add]
    exact Nat.mul_le_mul_right w hF.1

end PEqualNP.Outside.L_lib_1129_aux

theorem PEqualNP.Outside.L_lib_1129 : (∀ (m : Nat) (T : Finset (Fin m)) (t w : Nat), 0 < w →

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
      ∀ S ⊆ T, S.card ≤ t * w → ∀ B ⊆ S, pin A S B = pin D S B)) := by
  intro m T t w hw
  exact PEqualNP.Outside.L_lib_1129_aux.main m T t w hw
