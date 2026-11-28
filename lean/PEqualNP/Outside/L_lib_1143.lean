import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1143

open Finset

def flip {n : ℕ} (j : Fin n) (x : Finset (Fin n)) : Finset (Fin n) :=
  if j ∈ x then x.erase j else insert j x

theorem flip_flip {n : ℕ} (j : Fin n) (x : Finset (Fin n)) : flip j (flip j x) = x := by
  unfold flip
  by_cases hj : j ∈ x
  · simp [hj, insert_erase hj]
  · simp [hj, erase_insert hj]

theorem flip_ne {n : ℕ} (j : Fin n) (x : Finset (Fin n)) : flip j x ≠ x := by
  unfold flip
  by_cases hj : j ∈ x
  · rw [if_pos hj]
    intro h
    have := notMem_erase j x
    rw [h] at this
    exact this hj
  · rw [if_neg hj]
    intro h
    have : j ∈ insert j x := mem_insert_self j x
    rw [h] at this
    exact hj this

theorem flip_inter {n : ℕ} (j : Fin n) (x s : Finset (Fin n)) (hs : j ∉ s) :
    flip j x ∩ s = x ∩ s := by
  unfold flip
  ext a
  by_cases ha : a = j
  · subst ha
    split_ifs <;> simp [hs]
  · split_ifs <;> simp [ha]

theorem sign_flip {n : ℕ} (j : Fin n) (x : Finset (Fin n)) :
    ((-1 : ℤ) ^ (flip j x).card) = -((-1 : ℤ) ^ x.card) := by
  unfold flip
  by_cases hj : j ∈ x
  · rw [if_pos hj, ← card_erase_add_one hj, pow_succ]
    ring
  · rw [if_neg hj, card_insert_of_notMem hj, pow_succ]
    ring

theorem pair_filter {n : ℕ} (j : Fin n) (x : Finset (Fin n)) (hj : j ∉ x) :
    (univ : Finset (Finset (Fin n))).filter (fun y => y ∩ univ.erase j = x) = {x, insert j x} := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  rw [inter_erase, inter_univ]
  constructor
  · intro h
    by_cases hy : j ∈ y
    · right
      rw [← h, insert_erase hy]
    · left
      rw [← h, erase_eq_of_notMem hy]
  · rintro (h | h)
    · rw [h, erase_eq_of_notMem hj]
    · rw [h, erase_insert hj]

theorem diff_formula {n : ℕ} (d : Finset (Fin n) → ℤ)
    (hpin : ∀ S : Finset (Fin n), S ≠ univ → ∀ z ⊆ S,
      ((univ : Finset (Finset (Fin n))).filter (fun x => x ∩ S = z)).sum d = 0) :
    ∀ x : Finset (Fin n), d x = (-1 : ℤ) ^ x.card * d ∅ := by
  have step : ∀ j : Fin n, ∀ x : Finset (Fin n), j ∉ x → d (insert j x) = - d x := by
    intro j x hj
    have hS : univ.erase j ≠ (univ : Finset (Fin n)) := by
      intro h
      have : j ∈ univ.erase j := by rw [h]; exact mem_univ j
      exact notMem_erase j _ this
    have hz : x ⊆ univ.erase j := by
      intro a ha
      rw [mem_erase]
      exact ⟨fun h => hj (h ▸ ha), mem_univ a⟩
    have h := hpin _ hS x hz
    rw [pair_filter j x hj] at h
    have hne : x ≠ insert j x := by
      intro h'
      apply hj
      rw [h']
      exact mem_insert_self j x
    rw [sum_pair hne] at h
    linarith
  intro x
  induction x using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [step a s ha, ih, card_insert_of_notMem ha, pow_succ]
    ring

theorem inj_restrict {n t : ℕ} (scope : Fin t → Finset (Fin n))
    (hcov : ∀ j : Fin n, ∃ i : Fin t, j ∈ scope i) (x y : Finset (Fin n))
    (h : ∀ i, x ∩ scope i = y ∩ scope i) : x = y := by
  ext a
  obtain ⟨i, hi⟩ := hcov a
  have := congrArg (fun s => a ∈ s) (h i)
  simp only [mem_inter, hi, and_true] at this
  exact Iff.of_eq this

theorem part_zero {n t : ℕ} (e : Finset (Fin n) → ℤ)
    (he : ∀ j x, e (flip j x) = - e x)
    (scope p : Fin t → Finset (Fin n))
    (hpriv : ∀ i : Fin t, ∃ j ∈ scope i, ∀ h : Fin t, j ∈ scope h → h = i)
    (T : Finset (Fin t)) (hT : T ≠ univ) :
    ∑ x : Finset (Fin n), (if ∀ i ∈ T, x ∩ scope i = p i then e x else 0) = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ T := by
    by_contra hc
    push_neg at hc
    exact hT (eq_univ_of_forall hc)
  obtain ⟨j, -, hj⟩ := hpriv i0
  have hkeep : ∀ x : Finset (Fin n), ∀ i ∈ T, flip j x ∩ scope i = x ∩ scope i := by
    intro x i hi
    apply flip_inter
    intro hji
    have := hj i hji
    subst this
    exact hi0 hi
  apply Finset.sum_involution (fun x _ => flip j x)
  · intro x _
    have hiff : (∀ i ∈ T, flip j x ∩ scope i = p i) ↔ (∀ i ∈ T, x ∩ scope i = p i) := by
      constructor
      · intro h i hi
        rw [← hkeep x i hi]
        exact h i hi
      · intro h i hi
        rw [hkeep x i hi]
        exact h i hi
    by_cases hx : ∀ i ∈ T, x ∩ scope i = p i
    · rw [if_pos hx, if_pos (hiff.mpr hx), he]
      ring
    · rw [if_neg hx, if_neg (fun h => hx (hiff.mp h))]
      ring
  · intro x _ _
    exact flip_ne j x
  · intro x _
    exact mem_univ _
  · intro x _
    exact flip_flip j x

theorem gap_formula {n t : ℕ} (e : Finset (Fin n) → ℤ)
    (he : ∀ j x, e (flip j x) = - e x)
    (scope p : Fin t → Finset (Fin n))
    (hpriv : ∀ i : Fin t, ∃ j ∈ scope i, ∀ h : Fin t, j ∈ scope h → h = i) :
    ((univ : Finset (Finset (Fin n))).filter (fun x => ∀ i : Fin t, x ∩ scope i ≠ p i)).sum e =
      (-1 : ℤ) ^ t *
        ((univ : Finset (Finset (Fin n))).filter (fun x => ∀ i : Fin t, x ∩ scope i = p i)).sum e := by
  rw [sum_filter, sum_filter]
  have hprod : ∀ x : Finset (Fin n),
      (if ∀ i : Fin t, x ∩ scope i ≠ p i then e x else 0) =
        ∑ T ∈ (univ : Finset (Fin t)).powerset,
          (-1 : ℤ) ^ T.card * (if ∀ i ∈ T, x ∩ scope i = p i then e x else 0) := by
    intro x
    have h1 : (if ∀ i : Fin t, x ∩ scope i ≠ p i then e x else 0) =
        (∏ i : Fin t, (-(if x ∩ scope i = p i then (1 : ℤ) else 0) + 1)) * e x := by
      by_cases hx : ∀ i : Fin t, x ∩ scope i ≠ p i
      · rw [if_pos hx, prod_eq_one]
        · ring
        · intro i _
          rw [if_neg (hx i)]
          ring
      · rw [if_neg hx]
        push_neg at hx
        obtain ⟨i, hi⟩ := hx
        rw [prod_eq_zero (mem_univ i)]
        · ring
        · rw [if_pos hi]
          ring
    rw [h1, prod_add, sum_mul]
    apply sum_congr rfl
    intro T _
    rw [prod_const_one, mul_one, prod_neg, prod_boole]
    by_cases hT : ∀ i ∈ T, x ∩ scope i = p i
    · rw [if_pos hT, if_pos hT]
      ring
    · rw [if_neg hT, if_neg hT]
      ring
  rw [sum_congr rfl (fun x _ => hprod x), sum_comm]
  simp_rw [← mul_sum]
  rw [sum_eq_single (univ : Finset (Fin t))]
  · rw [card_univ, Fintype.card_fin]
    congr 1
    apply sum_congr rfl
    intro x _
    simp only [mem_univ, true_implies]
  · intro T _ hT
    rw [part_zero e he scope p hpriv T hT, mul_zero]
  · intro h
    exact absurd (mem_powerset.mpr (subset_refl _)) h

end PEqualNP.Outside.L_lib_1143

open PEqualNP.Outside.L_lib_1143 Finset in
theorem PEqualNP.Outside.L_lib_1143 : ∀ (n t : Nat), 0 < n →
  ∀ (A B : Finset (Fin n) → Nat) (scope : Fin t → Finset (Fin n)),
  let cube := (Finset.univ : Finset (Finset (Fin n)))
  let diff := fun (x : Finset (Fin n)) => (A x : Int) - (B x : Int)
  let delta := diff ∅
  let pinnedAt := fun (S z x : Finset (Fin n)) => x ∩ S = z
  (∀ S : Finset (Fin n), S ≠ Finset.univ → ∀ z ⊆ S,
    (cube.filter (pinnedAt S z)).sum diff = 0) → delta ≠ 0 →
  (∀ j : Fin n, ∃ i : Fin t, j ∈ scope i) →
  (∀ i : Fin t, ∃ j ∈ scope i, ∀ h : Fin t, j ∈ scope h → h = i) →
  let choices := ((Finset.univ : Finset (Fin t → Finset (Fin n)))).filter
    (fun patterns => ∀ i, patterns i ⊆ scope i)
  let gap := fun (patterns : Fin t → Finset (Fin n)) =>
    (cube.filter (fun x => ∀ i : Fin t, x ∩ scope i ≠ patterns i)).sum diff
  (∀ p ∈ choices,
    (gap p ≠ 0 ↔ ∃ x ∈ cube, ∀ i, x ∩ scope i = p i) ∧
    (∀ x ∈ cube, (∀ i, x ∩ scope i = p i) →
      gap p = (-1 : Int) ^ (t + x.card) * delta)) ∧
  (choices.filter (fun p => gap p ≠ 0)).card = 2 ^ n := by
  intro n t _hn A B scope cube diff delta pinnedAt hpin hδ hcov hpriv choices gap
  have hdiff : ∀ x, diff x = (-1 : ℤ) ^ x.card * delta :=
    diff_formula diff (fun S hS z hz => hpin S hS z hz)
  have he : ∀ j x, diff (flip j x) = - diff x := by
    intro j x
    rw [hdiff, hdiff, sign_flip]
    ring
  have hgap : ∀ p, gap p = (-1 : ℤ) ^ t *
      ((univ : Finset (Finset (Fin n))).filter (fun x => ∀ i : Fin t, x ∩ scope i = p i)).sum diff :=
    fun p => gap_formula diff he scope p hpriv
  have hsingle : ∀ (p : Fin t → Finset (Fin n)) (x : Finset (Fin n)), (∀ i, x ∩ scope i = p i) →
      (univ : Finset (Finset (Fin n))).filter (fun y => ∀ i : Fin t, y ∩ scope i = p i) = {x} := by
    intro p x hx
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hy
      exact inj_restrict scope hcov y x (fun i => (hy i).trans (hx i).symm)
    · rintro rfl
      exact hx
  have hval : ∀ (p : Fin t → Finset (Fin n)) (x : Finset (Fin n)), (∀ i, x ∩ scope i = p i) → gap p = (-1 : ℤ) ^ (t + x.card) * delta := by
    intro p x hx
    rw [hgap, hsingle p x hx, sum_singleton]
    rw [show (A x : ℤ) - (B x : ℤ) = diff x from rfl, hdiff, pow_add]
    ring
  have hiff : ∀ p : Fin t → Finset (Fin n), gap p ≠ 0 ↔ ∃ x ∈ cube, ∀ i, x ∩ scope i = p i := by
    intro p
    constructor
    · intro h
      by_contra hc
      apply h
      rw [hgap]
      have : (univ : Finset (Finset (Fin n))).filter (fun y => ∀ i : Fin t, y ∩ scope i = p i) = ∅ := by
        rw [filter_eq_empty_iff]
        intro y _ hy
        exact hc ⟨y, mem_univ y, hy⟩
      rw [this, sum_empty, mul_zero]
    · rintro ⟨x, _, hx⟩
      rw [hval p x hx]
      apply mul_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact hδ
  refine ⟨fun p _ => ⟨hiff p, fun x _ hx => hval p x hx⟩, ?_⟩
  have himg : choices.filter (fun p => gap p ≠ 0) =
      (univ : Finset (Finset (Fin n))).image (fun x => fun i => x ∩ scope i) := by
    ext p
    simp only [choices, mem_filter, mem_univ, true_and, mem_image]
    rw [hiff p]
    constructor
    · rintro ⟨_, x, _, hx⟩
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => inter_subset_right, x, mem_univ x, fun i => rfl⟩
  rw [himg, card_image_of_injective, card_univ, Fintype.card_finset, Fintype.card_fin]
  intro x y h
  exact inj_restrict scope hcov x y (fun i => congrFun h i)
