import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18976

def L14 : List ℕ :=
  [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ),
   (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ),
   (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)]

def L3 : List (Fin 13) := [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)]

def wit2 (d : Fin 13) : ℕ × Fin 13 × Fin 13 :=
  match d.val with
  | 1 => (7962627, (1 : Fin 13), (0 : Fin 13))
  | 2 => (24444933, (1 : Fin 13), (0 : Fin 13))
  | 3 => (7962627, (9 : Fin 13), (0 : Fin 13))
  | 4 => (7962627, (3 : Fin 13), (1 : Fin 13))
  | 5 => (24444933, (3 : Fin 13), (0 : Fin 13))
  | 6 => (24444933, (9 : Fin 13), (0 : Fin 13))
  | 7 => (24444933, (9 : Fin 13), (2 : Fin 13))
  | 8 => (24444933, (3 : Fin 13), (2 : Fin 13))
  | 9 => (7962627, (3 : Fin 13), (0 : Fin 13))
  | 10 => (7962627, (9 : Fin 13), (1 : Fin 13))
  | 11 => (24444933, (1 : Fin 13), (2 : Fin 13))
  | 12 => (7962627, (1 : Fin 13), (1 : Fin 13))
  | _ => (67100672, 1, 0)

def wit3 (d1 d2 : Fin 13) : ℕ × Fin 13 × Fin 13 :=
  match d1.val, d2.val with
  | 1, 2 => (7405575, (1 : Fin 13), (0 : Fin 13))
  | 1, 3 => (6815755, (1 : Fin 13), (0 : Fin 13))
  | 1, 4 => (5799955, (1 : Fin 13), (0 : Fin 13))
  | 1, 5 => (23330829, (3 : Fin 13), (0 : Fin 13))
  | 1, 6 => (19415081, (3 : Fin 13), (0 : Fin 13))
  | 1, 7 => (22282261, (9 : Fin 13), (4 : Fin 13))
  | 1, 8 => (19988517, (3 : Fin 13), (2 : Fin 13))
  | 1, 9 => (6815755, (3 : Fin 13), (0 : Fin 13))
  | 1, 10 => (21757977, (1 : Fin 13), (3 : Fin 13))
  | 1, 11 => (23330829, (1 : Fin 13), (2 : Fin 13))
  | 1, 12 => (7405575, (1 : Fin 13), (1 : Fin 13))
  | 2, 3 => (23330829, (1 : Fin 13), (0 : Fin 13))
  | 2, 4 => (22282261, (1 : Fin 13), (0 : Fin 13))
  | 2, 5 => (19988517, (1 : Fin 13), (0 : Fin 13))
  | 2, 6 => (19988517, (9 : Fin 13), (0 : Fin 13))
  | 2, 7 => (6619269, (1 : Fin 13), (0 : Fin 13))
  | 2, 8 => (2179233, (1 : Fin 13), (5 : Fin 13))
  | 2, 9 => (19415081, (9 : Fin 13), (0 : Fin 13))
  | 2, 10 => (19415081, (1 : Fin 13), (3 : Fin 13))
  | 2, 11 => (22282261, (1 : Fin 13), (2 : Fin 13))
  | 2, 12 => (6815755, (1 : Fin 13), (1 : Fin 13))
  | 3, 4 => (21757977, (1 : Fin 13), (0 : Fin 13))
  | 3, 5 => (19415081, (1 : Fin 13), (0 : Fin 13))
  | 3, 6 => (7405575, (9 : Fin 13), (0 : Fin 13))
  | 3, 7 => (23330829, (9 : Fin 13), (2 : Fin 13))
  | 3, 8 => (22282261, (3 : Fin 13), (4 : Fin 13))
  | 3, 9 => (6815755, (9 : Fin 13), (0 : Fin 13))
  | 3, 10 => (7405575, (9 : Fin 13), (1 : Fin 13))
  | 3, 11 => (19988517, (1 : Fin 13), (2 : Fin 13))
  | 3, 12 => (5799955, (1 : Fin 13), (1 : Fin 13))
  | 4, 5 => (6815755, (3 : Fin 13), (1 : Fin 13))
  | 4, 6 => (19415081, (9 : Fin 13), (3 : Fin 13))
  | 4, 7 => (6815755, (9 : Fin 13), (3 : Fin 13))
  | 4, 8 => (7405575, (3 : Fin 13), (2 : Fin 13))
  | 4, 9 => (7405575, (3 : Fin 13), (1 : Fin 13))
  | 4, 10 => (23330829, (9 : Fin 13), (3 : Fin 13))
  | 4, 11 => (19988517, (9 : Fin 13), (5 : Fin 13))
  | 4, 12 => (23330829, (3 : Fin 13), (3 : Fin 13))
  | 5, 6 => (19988517, (3 : Fin 13), (0 : Fin 13))
  | 5, 7 => (2179233, (1 : Fin 13), (0 : Fin 13))
  | 5, 8 => (22282261, (3 : Fin 13), (2 : Fin 13))
  | 5, 9 => (7405575, (3 : Fin 13), (0 : Fin 13))
  | 5, 10 => (22282261, (3 : Fin 13), (0 : Fin 13))
  | 5, 11 => (6619269, (1 : Fin 13), (2 : Fin 13))
  | 5, 12 => (19415081, (3 : Fin 13), (3 : Fin 13))
  | 6, 7 => (22282261, (9 : Fin 13), (2 : Fin 13))
  | 6, 8 => (6619269, (1 : Fin 13), (7 : Fin 13))
  | 6, 9 => (23330829, (9 : Fin 13), (0 : Fin 13))
  | 6, 10 => (6815755, (9 : Fin 13), (1 : Fin 13))
  | 6, 11 => (2179233, (1 : Fin 13), (7 : Fin 13))
  | 6, 12 => (22282261, (9 : Fin 13), (0 : Fin 13))
  | 7, 8 => (19415081, (3 : Fin 13), (5 : Fin 13))
  | 7, 9 => (19988517, (9 : Fin 13), (2 : Fin 13))
  | 7, 10 => (7405575, (9 : Fin 13), (2 : Fin 13))
  | 7, 11 => (19415081, (9 : Fin 13), (5 : Fin 13))
  | 7, 12 => (19988517, (3 : Fin 13), (5 : Fin 13))
  | 8, 9 => (23330829, (3 : Fin 13), (2 : Fin 13))
  | 8, 10 => (19988517, (1 : Fin 13), (5 : Fin 13))
  | 8, 11 => (19415081, (1 : Fin 13), (5 : Fin 13))
  | 8, 12 => (6815755, (3 : Fin 13), (3 : Fin 13))
  | 9, 10 => (5799955, (1 : Fin 13), (4 : Fin 13))
  | 9, 11 => (22282261, (1 : Fin 13), (4 : Fin 13))
  | 9, 12 => (21757977, (1 : Fin 13), (4 : Fin 13))
  | 10, 11 => (6815755, (1 : Fin 13), (3 : Fin 13))
  | 10, 12 => (23330829, (1 : Fin 13), (3 : Fin 13))
  | 11, 12 => (7405575, (1 : Fin 13), (2 : Fin 13))
  | _, _ => (67100672, 1, 0)

lemma fin13_sub_self : ∀ a : Fin 13, a - a = 0 := by decide

lemma fin13_sub_add : ∀ a x : Fin 13, (x - a) + a = x := by decide

lemma fin13_sub_eq_iff (a b x : Fin 13) : x - a = b - a ↔ x = b := by
  constructor
  · intro h
    have h1 := congrArg (· + a) h
    rwa [fin13_sub_add, fin13_sub_add] at h1
  · intro h
    rw [h]

lemma fin13_sub_def : ∀ a b : Fin 13, a - b = a + (-b) := by decide

lemma fin13_add_comm : ∀ a b : Fin 13, a + b = b + a := by decide

lemma fin13_add_assoc (a b c : Fin 13) : a + b + c = a + (b + c) := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

lemma fin13_add_sub (u v w : Fin 13) : u + (v - w) = (u - w) + v := by
  rw [fin13_sub_def v w, fin13_add_comm v (-w), ← fin13_add_assoc, ← fin13_sub_def u w]

lemma fin13_mul_sub1 : ∀ a x : Fin 13, (1 : Fin 13) * x - (1 : Fin 13) * a = 1 * (x - a) := by decide
lemma fin13_mul_sub3 : ∀ a x : Fin 13, (3 : Fin 13) * x - (3 : Fin 13) * a = 3 * (x - a) := by decide
lemma fin13_mul_sub9 : ∀ a x : Fin 13, (9 : Fin 13) * x - (9 : Fin 13) * a = 9 * (x - a) := by decide

lemma fin13_shift (x4 : Fin 13) (hx4 : x4 ∈ L3) (a s x6 : Fin 13) :
    x4 * x6 + (s - x4 * a) = x4 * (x6 - a) + s := by
  rw [fin13_add_sub]
  simp only [L3, List.mem_cons, List.not_mem_nil, or_false] at hx4
  rcases hx4 with rfl | rfl | rfl
  · rw [fin13_mul_sub1]
  · rw [fin13_mul_sub3]
  · rw [fin13_mul_sub9]

lemma case0_ok : ∀ y : Fin 13,
    false = (67100672 : ℕ).testBit ↑((1 : Fin 13) * y + (0 : Fin 13)) := by decide

lemma case1_ok : ∀ y : Fin 13,
    decide (y = 0) = (25018369 : ℕ).testBit ↑((1 : Fin 13) * y + (0 : Fin 13)) := by decide

lemma case2_ok : ∀ d : Fin 13, d ≠ 0 →
    (wit2 d).1 ∈ L14 ∧ (wit2 d).2.1 ∈ L3 ∧
    ∀ y : Fin 13, decide (y = 0 ∨ y = d) =
      (wit2 d).1.testBit ↑((wit2 d).2.1 * y + (wit2 d).2.2) := by decide

lemma case3_ok : ∀ d1 d2 : Fin 13, d1 ≠ 0 → d2 ≠ 0 → d1 < d2 →
    (wit3 d1 d2).1 ∈ L14 ∧ (wit3 d1 d2).2.1 ∈ L3 ∧
    ∀ y : Fin 13, decide (y = 0 ∨ y = d1 ∨ y = d2) =
      (wit3 d1 d2).1.testBit ↑((wit3 d1 d2).2.1 * y + (wit3 d1 d2).2.2) := by decide

end PEqualNP.Outside.L_meta_18976

open PEqualNP.Outside.L_meta_18976

theorem PEqualNP.Outside.L_meta_18976 : (∀ (x1 : Finset (Fin (13 : ℕ))), x1.card ≤ (3 : ℕ) → ∃ x3 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)], ∃ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), Decidable.decide (x6 ∈ x1) = x3.testBit ↑(x4 * x6 + x5)) := by
  intro x1 hcard
  have hcases : x1.card = 0 ∨ x1.card = 1 ∨ x1.card = 2 ∨ x1.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [Finset.card_eq_zero.mp h0]
    refine ⟨67100672, by decide, 1, by decide, 0, fun x6 => ?_⟩
    rw [← case0_ok x6]
    simp only [Finset.notMem_empty, decide_false]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    refine ⟨25018369, by decide, 1, by decide, 0 - 1 * a, fun x6 => ?_⟩
    rw [fin13_shift 1 (by decide) a 0 x6, ← case1_ok (x6 - a)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Finset.mem_singleton]
    rw [← fin13_sub_self a, fin13_sub_eq_iff]
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    have hd : b - a ≠ 0 := by
      intro hz
      apply hab
      have h' : b - a = a - a := by rw [hz, fin13_sub_self]
      exact ((fin13_sub_eq_iff a a b).mp h').symm
    obtain ⟨hx3, hx4, hok⟩ := case2_ok (b - a) hd
    refine ⟨(wit2 (b - a)).1, hx3, (wit2 (b - a)).2.1, hx4,
      (wit2 (b - a)).2.2 - (wit2 (b - a)).2.1 * a, fun x6 => ?_⟩
    rw [fin13_shift _ hx4 a _ x6, ← hok (x6 - a)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    rw [← fin13_sub_self a, fin13_sub_eq_iff a a x6, fin13_sub_eq_iff a b x6]
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
    have hd1 : b - a ≠ 0 := by
      intro hz; apply hab
      exact ((fin13_sub_eq_iff a a b).mp (by rw [hz, fin13_sub_self])).symm
    have hd2 : c - a ≠ 0 := by
      intro hz; apply hac
      exact ((fin13_sub_eq_iff a a c).mp (by rw [hz, fin13_sub_self])).symm
    have hd12 : b - a ≠ c - a := by
      intro heq; apply hbc
      exact (fin13_sub_eq_iff a c b).mp heq
    rcases lt_or_gt_of_ne hd12 with hlt | hgt
    · obtain ⟨hx3, hx4, hok⟩ := case3_ok (b - a) (c - a) hd1 hd2 hlt
      refine ⟨(wit3 (b - a) (c - a)).1, hx3, (wit3 (b - a) (c - a)).2.1, hx4,
        (wit3 (b - a) (c - a)).2.2 - (wit3 (b - a) (c - a)).2.1 * a, fun x6 => ?_⟩
      rw [fin13_shift _ hx4 a _ x6, ← hok (x6 - a)]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      rw [← fin13_sub_self a, fin13_sub_eq_iff a a x6, fin13_sub_eq_iff a b x6, fin13_sub_eq_iff a c x6]
    · obtain ⟨hx3, hx4, hok⟩ := case3_ok (c - a) (b - a) hd2 hd1 hgt
      refine ⟨(wit3 (c - a) (b - a)).1, hx3, (wit3 (c - a) (b - a)).2.1, hx4,
        (wit3 (c - a) (b - a)).2.2 - (wit3 (c - a) (b - a)).2.1 * a, fun x6 => ?_⟩
      rw [fin13_shift _ hx4 a _ x6, ← hok (x6 - a)]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      rw [← fin13_sub_self a, fin13_sub_eq_iff a a x6, fin13_sub_eq_iff a c x6, fin13_sub_eq_iff a b x6]
      tauto
