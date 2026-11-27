import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field

namespace PEqualNP.Outside.L_meta_25556_aux

open Classical

private def move (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1,
    hit.toNat + (aligned && hit).toNat)

private def summaryFrom (mode code length : Nat) : Nat × Nat :=
  (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
    let result := move st.1 ((code >>> (3 * digitPos)) % 8)
    (result.1, st.2 + result.2)) (mode, 0)

private def summary (code length : Nat) : Nat × Nat :=
  summaryFrom 0 code length

private def price (n depth : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun codeWord =>
    2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum

private theorem move_mode_lt (mode letter : Nat) : (move mode letter).1 < 3 := by
  unfold move
  dsimp only
  split <;> [split <;> omega; omega]

private theorem move_gain_le (mode letter : Nat) : (move mode letter).2 ≤ 2 := by
  unfold move
  cases (((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)) <;> cases letter.testBit 2 <;> decide

private theorem foldl_summary_acc (code : Nat) (xs : List Nat) (mode acc : Nat) :
    xs.foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (mode, acc) =
    let s := xs.foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (mode, 0)
    (s.1, acc + s.2) := by
  induction xs generalizing mode acc with
  | nil => simp
  | cons d xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (acc + (move mode ((code >>> (3 * d)) % 8)).2)]
    rw [ih _ (0 + (move mode ((code >>> (3 * d)) % 8)).2)]
    simp only [Nat.zero_add, Nat.add_assoc]

private theorem shiftRight_three_succ (l rest k : Nat) (hl : l < 8) :
    (l + 8 * rest) >>> (3 * (k + 1)) = rest >>> (3 * k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (3 * (k + 1)) = 8 * 2 ^ (3 * k) := by
    rw [show 3 * (k + 1) = 3 + 3 * k by omega, Nat.pow_add]
  rw [hp, ← Nat.div_div_eq_div_mul]
  have hd : (l + 8 * rest) / 8 = rest := by omega
  rw [hd]

private theorem summaryFrom_zero (mode code : Nat) : summaryFrom mode code 0 = (mode, 0) := rfl

private theorem summaryFrom_succ (mode l rest n : Nat) (hl : l < 8) :
    summaryFrom mode (l + 8 * rest) (n + 1) =
      let r := move mode l
      let s := summaryFrom r.1 rest n
      (s.1, r.2 + s.2) := by
  unfold summaryFrom
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : ((l + 8 * rest) >>> (3 * 0)) % 8 = l := by
    simp only [Nat.mul_zero, Nat.shiftRight_zero]
    omega
  rw [h0]
  have hcongr : (List.range n).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 (((l + 8 * rest) >>> (3 * (digitPos + 1))) % 8)
      (result.1, st.2 + result.2)) ((move mode l).1, 0 + (move mode l).2) =
    (List.range n).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((rest >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) ((move mode l).1, (move mode l).2) := by
    simp only [Nat.zero_add]
    congr 1
    funext st digitPos
    rw [shiftRight_three_succ l rest digitPos hl]
  rw [hcongr, foldl_summary_acc]

private theorem summaryFrom_gain_le (mode code n : Nat) : (summaryFrom mode code n).2 ≤ 2 * n := by
  induction n generalizing mode code with
  | zero => simp [summaryFrom_zero]
  | succ n ih =>
    have hsplit : code = code % 8 + 8 * (code / 8) := by omega
    conv_lhs => rw [hsplit]
    rw [summaryFrom_succ mode (code % 8) (code / 8) n (by omega)]
    dsimp only
    have h1 := move_gain_le mode (code % 8)
    have h2 := ih (move mode (code % 8)).1 (code / 8)
    omega

private theorem list_sum_map_add {α : Type*} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_range_mul (a b : Nat) (f : Nat → Nat) :
    ((List.range (a * b)).map f).sum =
      ((List.range a).map (fun r => ((List.range b).map (fun q => f (r + a * q))).sum)).sum := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, List.range_add, List.map_append, List.sum_append, ih, List.map_map]
    have hstep : ((List.range a).map (fun r =>
        ((List.range (b + 1)).map (fun q => f (r + a * q))).sum)).sum =
      ((List.range a).map (fun r => ((List.range b).map (fun q => f (r + a * q))).sum)).sum +
      ((List.range a).map (fun r => f (r + a * b))).sum := by
      rw [← list_sum_map_add]
      congr 1
      apply List.map_congr_left
      intro r _
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [hstep]
    congr 1
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, Nat.add_comm]

private theorem sum_range_eight_pow_succ (n : Nat) (f : Nat → Nat) :
    ((List.range (8 ^ (n + 1))).map f).sum =
      ((List.range 8).map (fun l => ((List.range (8 ^ n)).map (fun rest => f (l + 8 * rest))).sum)).sum := by
  rw [Nat.pow_succ', sum_range_mul]

private def countGain (mode n g : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun w => if (summaryFrom mode w n).2 = g then 1 else 0)).sum

private theorem countGain_zero (mode g : Nat) :
    countGain mode 0 g = if g = 0 then 1 else 0 := by
  unfold countGain
  simp [summaryFrom_zero, eq_comm]

private theorem countGain_eq_zero_of_gt (mode n g : Nat) (hg : 2 * n < g) :
    countGain mode n g = 0 := by
  unfold countGain
  have hall : (List.range (8 ^ n)).map (fun w => if (summaryFrom mode w n).2 = g then 1 else 0) =
      (List.range (8 ^ n)).map (fun _ => 0) := by
    apply List.map_congr_left
    intro w _
    have hle := summaryFrom_gain_le mode w n
    have hne : (summaryFrom mode w n).2 ≠ g := by omega
    simp [hne]
  rw [hall]
  simp

private theorem countGain_succ (mode n g : Nat) :
    countGain mode (n + 1) g =
      ((List.range 8).map (fun l =>
        let r := move mode l
        if r.2 ≤ g then countGain r.1 n (g - r.2) else 0)).sum := by
  unfold countGain
  rw [sum_range_eight_pow_succ]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl8 : l < 8 := List.mem_range.1 hl
  by_cases hle : (move mode l).2 ≤ g
  · rw [if_pos hle]
    congr 1
    apply List.map_congr_left
    intro rest _
    rw [summaryFrom_succ mode l rest n hl8]
    dsimp only
    have hiff : (move mode l).2 + (summaryFrom (move mode l).1 rest n).2 = g ↔
        (summaryFrom (move mode l).1 rest n).2 = g - (move mode l).2 := by omega
    by_cases h : (summaryFrom (move mode l).1 rest n).2 = g - (move mode l).2
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  · rw [if_neg hle]
    have hall : (List.range (8 ^ n)).map
        (fun rest => if (summaryFrom mode (l + 8 * rest) (n + 1)).2 = g then 1 else 0) =
        (List.range (8 ^ n)).map (fun _ => 0) := by
      apply List.map_congr_left
      intro rest _
      rw [summaryFrom_succ mode l rest n hl8]
      dsimp only
      have hne : (move mode l).2 + (summaryFrom (move mode l).1 rest n).2 ≠ g := by omega
      simp [hne]
    rw [hall]
    simp

private theorem countGain_rec_0 (n g : Nat) :
    countGain 0 (n + 1) g =
      4 * countGain 1 n g + (if 1 ≤ g then 4 * countGain 1 n (g - 1) else 0) := by
  rw [countGain_succ]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 0 0 = (1, 0) := by decide
  have m1 : move 0 1 = (1, 0) := by decide
  have m2 : move 0 2 = (1, 0) := by decide
  have m3 : move 0 3 = (1, 0) := by decide
  have m4 : move 0 4 = (1, 1) := by decide
  have m5 : move 0 5 = (1, 1) := by decide
  have m6 : move 0 6 = (1, 1) := by decide
  have m7 : move 0 7 = (1, 1) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  split_ifs <;> omega

private theorem countGain_rec_1 (n g : Nat) :
    countGain 1 (n + 1) g =
      (if 2 ≤ g then countGain 0 n (g - 2) else 0) +
      3 * countGain 1 n g + (if 1 ≤ g then 3 * countGain 1 n (g - 1) else 0) +
      countGain 2 n g := by
  rw [countGain_succ]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 1 0 = (1, 0) := by decide
  have m1 : move 1 1 = (1, 0) := by decide
  have m2 : move 1 2 = (1, 0) := by decide
  have m3 : move 1 3 = (2, 0) := by decide
  have m4 : move 1 4 = (1, 1) := by decide
  have m5 : move 1 5 = (1, 1) := by decide
  have m6 : move 1 6 = (1, 1) := by decide
  have m7 : move 1 7 = (0, 2) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  split_ifs <;> omega

private theorem countGain_rec_2 (n g : Nat) :
    countGain 2 (n + 1) g =
      (if 2 ≤ g then 2 * countGain 0 n (g - 2) else 0) +
      2 * countGain 1 n g + (if 1 ≤ g then 2 * countGain 1 n (g - 1) else 0) +
      2 * countGain 2 n g := by
  rw [countGain_succ]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 2 0 = (1, 0) := by decide
  have m1 : move 2 1 = (1, 0) := by decide
  have m2 : move 2 2 = (2, 0) := by decide
  have m3 : move 2 3 = (2, 0) := by decide
  have m4 : move 2 4 = (1, 1) := by decide
  have m5 : move 2 5 = (1, 1) := by decide
  have m6 : move 2 6 = (0, 2) := by decide
  have m7 : move 2 7 = (0, 2) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  split_ifs <;> omega

private theorem price_eq_sum_countGain (n d : Nat) :
    (price n d : ℝ) / (2 : ℝ) ^ (5 * n) =
      ∑ g ∈ Finset.range (2 * n + 1),
        ((countGain 0 n g : ℝ) / (8 : ℝ) ^ n) * ((2 : ℝ) ^ (g - d))⁻¹ := by
  have h5n : (2 : ℝ) ^ (5 * n) = (8 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
    rw [h8, ← pow_mul, ← pow_add, show 3 * n + 2 * n = 5 * n by omega]
  have hsum_nat : price n d =
      ∑ g ∈ Finset.range (2 * n + 1), countGain 0 n g * 2 ^ (2 * n - (g - d)) := by
    unfold price countGain summary
    have hlist : ∀ (xs : List Nat),
        (∀ w ∈ xs, (summaryFrom 0 w n).2 ≤ 2 * n) →
        (xs.map (fun w => 2 ^ (2 * n - ((summaryFrom 0 w n).2 - d)))).sum =
          ∑ g ∈ Finset.range (2 * n + 1),
            (xs.map (fun w => if (summaryFrom 0 w n).2 = g then 1 else 0)).sum *
              2 ^ (2 * n - (g - d)) := by
      intro xs hxs
      induction xs with
      | nil => simp
      | cons w xs ih =>
        have hw : (summaryFrom 0 w n).2 ≤ 2 * n := hxs w (by simp)
        have hxs' : ∀ w' ∈ xs, (summaryFrom 0 w' n).2 ≤ 2 * n :=
          fun w' hw' => hxs w' (by simp [hw'])
        simp only [List.map_cons, List.sum_cons, ih hxs']
        have hterm : ∑ g ∈ Finset.range (2 * n + 1),
            ((if (summaryFrom 0 w n).2 = g then 1 else 0) +
              (xs.map (fun w' => if (summaryFrom 0 w' n).2 = g then 1 else 0)).sum) *
              2 ^ (2 * n - (g - d)) =
          (∑ g ∈ Finset.range (2 * n + 1),
            (if (summaryFrom 0 w n).2 = g then 1 else 0) * 2 ^ (2 * n - (g - d))) +
          (∑ g ∈ Finset.range (2 * n + 1),
            (xs.map (fun w' => if (summaryFrom 0 w' n).2 = g then 1 else 0)).sum *
              2 ^ (2 * n - (g - d))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro g _
          ring
        rw [hterm]
        congr 1
        have hsingle : ∑ g ∈ Finset.range (2 * n + 1),
            (if (summaryFrom 0 w n).2 = g then 1 else 0) * 2 ^ (2 * n - (g - d)) =
            2 ^ (2 * n - ((summaryFrom 0 w n).2 - d)) := by
          have hconv : ∀ g, (if (summaryFrom 0 w n).2 = g then 1 else 0) * 2 ^ (2 * n - (g - d)) =
              if g = (summaryFrom 0 w n).2 then 2 ^ (2 * n - (g - d)) else 0 := by
            intro g
            by_cases h : g = (summaryFrom 0 w n).2
            · subst h; simp
            · simp [h, Ne.symm h]
          simp only [hconv]
          rw [Finset.sum_ite_eq']
          simp [Finset.mem_range, show (summaryFrom 0 w n).2 < 2 * n + 1 by omega]
        rw [hsingle]
    exact hlist (List.range (8 ^ n)) (fun w _ => summaryFrom_gain_le 0 w n)
  rw [hsum_nat, h5n]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g hg
  have hgle : g ≤ 2 * n := by have := Finset.mem_range.mp hg; omega
  have hsub : g - d ≤ 2 * n := by omega
  have hpow2 : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ (2 * n - (g - d)) * (2 : ℝ) ^ (g - d) := by
    rw [← pow_add, Nat.sub_add_cancel hsub]
  have h8pos : (8 : ℝ) ^ n ≠ 0 := by positivity
  have h2pos : (2 : ℝ) ^ (g - d) ≠ 0 := by positivity
  have h2mpos : (2 : ℝ) ^ (2 * n - (g - d)) ≠ 0 := by positivity
  rw [hpow2]
  field_simp

private def binomProb (b : Nat) (p : ℝ) (k : Nat) : ℝ :=
  if k ≤ b then (Nat.choose b k : ℝ) * p ^ k * (1 - p) ^ (b - k) else 0

private theorem binomProb_nonneg (b : Nat) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : Nat) :
    0 ≤ binomProb b p k := by
  unfold binomProb
  split_ifs
  · have : 0 ≤ 1 - p := by linarith
    positivity
  · exact le_rfl

private theorem binomProb_zero (p : ℝ) (k : Nat) :
    binomProb 0 p k = if k = 0 then 1 else 0 := by
  unfold binomProb
  cases k with
  | zero => simp
  | succ k => simp

private theorem binomProb_succ (b : Nat) (p : ℝ) (k : Nat) :
    binomProb (b + 1) p k =
      (1 - p) * binomProb b p k + (if 1 ≤ k then p * binomProb b p (k - 1) else 0) := by
  cases k with
  | zero =>
    unfold binomProb
    simp [pow_succ]
    ring
  | succ k =>
    simp only [show 1 ≤ k + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    unfold binomProb
    by_cases h1 : k + 1 ≤ b
    · have h2 : k ≤ b := by omega
      have h3 : k + 1 ≤ b + 1 := by omega
      rw [if_pos h3, if_pos h1, if_pos h2, Nat.choose_succ_succ]
      push_cast
      have he2 : b - k = (b - (k + 1)) + 1 := by omega
      rw [he2, pow_succ (1 - p), pow_succ p]
      ring
    · by_cases h2 : k = b
      · subst h2
        rw [if_pos (le_refl _), if_neg (by omega), if_pos (le_refl _)]
        simp [pow_succ]
        ring
      · have h3 : ¬ (k + 1 ≤ b + 1) := by omega
        have h4 : ¬ (k ≤ b) := by omega
        rw [if_neg h3, if_neg h1, if_neg h4]
        ring

private theorem binomProb_sum_one (b : Nat) (p : ℝ) :
    ∑ k ∈ Finset.range (b + 1), binomProb b p k = 1 := by
  induction b with
  | zero => simp [binomProb_zero]
  | succ b ih =>
    have hsplit : ∑ k ∈ Finset.range (b + 2), binomProb (b + 1) p k =
        (∑ k ∈ Finset.range (b + 2), (1 - p) * binomProb b p k) +
        (∑ k ∈ Finset.range (b + 2), if 1 ≤ k then p * binomProb b p (k - 1) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      exact binomProb_succ b p k
    rw [hsplit]
    have h1 : ∑ k ∈ Finset.range (b + 2), (1 - p) * binomProb b p k = 1 - p := by
      rw [Finset.sum_range_succ, ← Finset.mul_sum, ih]
      have h0 : binomProb b p (b + 1) = 0 := by unfold binomProb; simp
      rw [h0]; ring
    have h2 : ∑ k ∈ Finset.range (b + 2), (if 1 ≤ k then p * binomProb b p (k - 1) else 0) = p := by
      rw [Finset.sum_range_succ']
      simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, add_zero, show ∀ k, 1 ≤ k + 1 by omega,
        Nat.add_sub_cancel, ← Finset.mul_sum, ih]
      ring
    rw [h1, h2]
    ring

private theorem binomProb_moments (b : Nat) (p : ℝ) :
    (∑ k ∈ Finset.range (b + 1), binomProb b p k * (k : ℝ) = (b : ℝ) * p) ∧
    (∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k : ℝ) ^ 2) =
      (b : ℝ) * p * (1 - p) + ((b : ℝ) * p) ^ 2) := by
  induction b with
  | zero =>
    simp [binomProb_zero]
  | succ b ih =>
    rcases ih with ⟨ih1, ih2⟩
    have h0 : binomProb b p (b + 1) = 0 := by unfold binomProb; simp
    have hsum1 : ∑ k ∈ Finset.range (b + 2), binomProb (b + 1) p k * (k : ℝ) =
        (∑ k ∈ Finset.range (b + 2), (1 - p) * (binomProb b p k * (k : ℝ))) +
        (∑ k ∈ Finset.range (b + 2), if 1 ≤ k then p * (binomProb b p (k - 1) * (k : ℝ)) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [binomProb_succ]
      split_ifs <;> ring
    have h1a : ∑ k ∈ Finset.range (b + 2), (1 - p) * (binomProb b p k * (k : ℝ)) =
        (1 - p) * ((b : ℝ) * p) := by
      rw [Finset.sum_range_succ, ← Finset.mul_sum, ih1, h0]; ring
    have h1b : ∑ k ∈ Finset.range (b + 2),
        (if 1 ≤ k then p * (binomProb b p (k - 1) * (k : ℝ)) else 0) =
        p * ((b : ℝ) * p + 1) := by
      rw [Finset.sum_range_succ']
      simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, add_zero, show ∀ k, 1 ≤ k + 1 by omega,
        Nat.add_sub_cancel]
      rw [← Finset.mul_sum]
      congr 1
      have hsp : ∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k + 1 : Nat) : ℝ) =
          (∑ k ∈ Finset.range (b + 1), binomProb b p k * (k : ℝ)) +
          (∑ k ∈ Finset.range (b + 1), binomProb b p k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast; ring
      rw [hsp, ih1, binomProb_sum_one]
    have hsum2 : ∑ k ∈ Finset.range (b + 2), binomProb (b + 1) p k * ((k : ℝ) ^ 2) =
        (∑ k ∈ Finset.range (b + 2), (1 - p) * (binomProb b p k * ((k : ℝ) ^ 2))) +
        (∑ k ∈ Finset.range (b + 2), if 1 ≤ k then p * (binomProb b p (k - 1) * ((k : ℝ) ^ 2)) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [binomProb_succ]
      split_ifs <;> ring
    have h2a : ∑ k ∈ Finset.range (b + 2), (1 - p) * (binomProb b p k * ((k : ℝ) ^ 2)) =
        (1 - p) * ((b : ℝ) * p * (1 - p) + ((b : ℝ) * p) ^ 2) := by
      rw [Finset.sum_range_succ, ← Finset.mul_sum, ih2, h0]; ring
    have h2b : ∑ k ∈ Finset.range (b + 2),
        (if 1 ≤ k then p * (binomProb b p (k - 1) * ((k : ℝ) ^ 2)) else 0) =
        p * (((b : ℝ) * p * (1 - p) + ((b : ℝ) * p) ^ 2) + 2 * ((b : ℝ) * p) + 1) := by
      rw [Finset.sum_range_succ']
      simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, add_zero, show ∀ k, 1 ≤ k + 1 by omega,
        Nat.add_sub_cancel]
      rw [← Finset.mul_sum]
      congr 1
      have hsp : ∑ k ∈ Finset.range (b + 1), binomProb b p k * (((k + 1 : Nat) : ℝ) ^ 2) =
          (∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k : ℝ) ^ 2)) +
          2 * (∑ k ∈ Finset.range (b + 1), binomProb b p k * (k : ℝ)) +
          (∑ k ∈ Finset.range (b + 1), binomProb b p k) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast; ring
      rw [hsp, ih2, ih1, binomProb_sum_one]
    constructor
    · rw [hsum1, h1a, h1b]; push_cast; ring
    · rw [hsum2, h2a, h2b]; push_cast; ring

private theorem binomProb_var (b : Nat) (p : ℝ) :
    ∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k : ℝ) - (b : ℝ) * p) ^ 2 =
      (b : ℝ) * p * (1 - p) := by
  have hsp : ∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k : ℝ) - (b : ℝ) * p) ^ 2 =
      (∑ k ∈ Finset.range (b + 1), binomProb b p k * ((k : ℝ) ^ 2)) -
      2 * ((b : ℝ) * p) * (∑ k ∈ Finset.range (b + 1), binomProb b p k * (k : ℝ)) +
      ((b : ℝ) * p) ^ 2 * (∑ k ∈ Finset.range (b + 1), binomProb b p k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsp, (binomProb_moments b p).1, (binomProb_moments b p).2, binomProb_sum_one]
  ring

private theorem binomProb_ratio_step (b : Nat) (p : ℝ) (k : Nat) (hk : k < b) :
    binomProb b p (k + 1) * (((k + 1 : Nat) : ℝ) * (1 - p)) =
      binomProb b p k * (((b - k : Nat) : ℝ) * p) := by
  unfold binomProb
  rw [if_pos (by omega : k + 1 ≤ b), if_pos (by omega : k ≤ b)]
  have hch : (b.choose (k + 1) : ℝ) * ((k + 1 : Nat) : ℝ) =
      (b.choose k : ℝ) * ((b - k : Nat) : ℝ) := by
    have hnat : b.choose (k + 1) * (k + 1) = b.choose k * (b - k) := by
      have h1 := Nat.choose_succ_right_eq b k
      linarith
    exact_mod_cast hnat
  have he : b - k = (b - (k + 1)) + 1 := by omega
  rw [he, pow_succ (1 - p), pow_succ p]
  have hch' : (b.choose (k + 1) : ℝ) * ((k + 1 : Nat) : ℝ) =
      (b.choose k : ℝ) * (((b - (k + 1) + 1 : Nat) : ℝ)) := by
    rw [← he]; exact hch
  calc
    (b.choose (k + 1) : ℝ) * (p ^ k * p) * (1 - p) ^ (b - (k + 1)) * (((k + 1 : Nat) : ℝ) * (1 - p))
        = ((b.choose (k + 1) : ℝ) * ((k + 1 : Nat) : ℝ)) * p ^ k * (1 - p) ^ (b - (k + 1)) * p * (1 - p) := by ring
    _ = ((b.choose k : ℝ) * (((b - (k + 1) + 1 : Nat) : ℝ))) * p ^ k * (1 - p) ^ (b - (k + 1)) * p * (1 - p) := by rw [hch']
    _ = (b.choose k : ℝ) * p ^ k * ((1 - p) ^ (b - (k + 1)) * (1 - p)) * (((b - (k + 1) + 1 : Nat) : ℝ) * p) := by ring

private theorem exp_neg_two_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp (-2 * u) ≤ 1 - u := by
  have hpos : 0 < Real.exp (2 * u) := Real.exp_pos _
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by
    have := Real.add_one_le_exp (2 * u)
    linarith
  have h2 : 1 ≤ (1 - u) * Real.exp (2 * u) := by
    calc
      1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
      _ ≤ (1 - u) * Real.exp (2 * u) := mul_le_mul_of_nonneg_left h1 (by linarith)
  rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
  rw [inv_le_comm₀ hpos (by linarith)]
  rw [← one_div, div_le_iff₀ (by linarith)]
  linarith

private theorem binomProb_mode_max (b : Nat) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    let k0 := Nat.floor (((b : ℝ) + 1) * p)
    k0 ≤ b ∧ ∀ k, binomProb b p k ≤ binomProb b p k0 := by
  intro k0
  have hk0_le : (k0 : ℝ) ≤ ((b : ℝ) + 1) * p := Nat.floor_le (by positivity)
  have hk0_gt : ((b : ℝ) + 1) * p - 1 < (k0 : ℝ) := by
    have := Nat.lt_floor_add_one (((b : ℝ) + 1) * p)
    linarith
  have hk0_b : k0 ≤ b := by
    have hlt : (k0 : ℝ) < (b : ℝ) + 1 := by nlinarith
    have : k0 < b + 1 := by exact_mod_cast hlt
    omega
  refine ⟨hk0_b, ?_⟩
  have hup : ∀ k, k < k0 → binomProb b p k ≤ binomProb b p (k + 1) := by
    intro k hk
    have hkb : k < b := by omega
    have hrat := binomProb_ratio_step b p k hkb
    have hk1 : ((k + 1 : Nat) : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk
    have hcmp : ((k + 1 : Nat) : ℝ) * (1 - p) ≤ ((b - k : Nat) : ℝ) * p := by
      have hsub : ((b - k : Nat) : ℝ) = (b : ℝ) - (k : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hsub]
      push_cast at hk1 ⊢
      nlinarith
    have hnn := binomProb_nonneg b (le_of_lt hp0) (le_of_lt hp1) k
    have hpos : 0 < ((k + 1 : Nat) : ℝ) * (1 - p) := by positivity
    nlinarith
  have hdn : ∀ k, k0 ≤ k → binomProb b p (k + 1) ≤ binomProb b p k := by
    intro k hk
    by_cases hkb : k < b
    · have hrat := binomProb_ratio_step b p k hkb
      have hk1 : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hcmp : ((b - k : Nat) : ℝ) * p ≤ ((k + 1 : Nat) : ℝ) * (1 - p) := by
        have hsub : ((b - k : Nat) : ℝ) = (b : ℝ) - (k : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [hsub]
        push_cast
        nlinarith
      have hnn := binomProb_nonneg b (le_of_lt hp0) (le_of_lt hp1) k
      have hpos : 0 < ((k + 1 : Nat) : ℝ) * (1 - p) := by positivity
      nlinarith
    · have h0 : binomProb b p (k + 1) = 0 := by unfold binomProb; rw [if_neg (by omega)]
      rw [h0]
      exact binomProb_nonneg b (le_of_lt hp0) (le_of_lt hp1) k
  intro k
  by_cases hle : k ≤ k0
  · have hwalk : ∀ d, k + d ≤ k0 → binomProb b p k ≤ binomProb b p (k + d) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        calc
          binomProb b p k ≤ binomProb b p (k + d) := ih (by omega)
          _ ≤ binomProb b p (k + d + 1) := hup (k + d) (by omega)
    have h1 := hwalk (k0 - k) (by omega)
    rwa [show k + (k0 - k) = k0 by omega] at h1
  · obtain ⟨d, rfl⟩ : ∃ d, k = k0 + d := ⟨k - k0, by omega⟩
    clear hle
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        binomProb b p (k0 + (d + 1)) = binomProb b p (k0 + d + 1) := by rfl
        _ ≤ binomProb b p (k0 + d) := hdn (k0 + d) (by omega)
        _ ≤ binomProb b p k0 := ih

private theorem binomProb_ratio_lower {b : Nat} {p : ℝ} (hb : 200000 ≤ b)
    (hp1 : 7 / 15 ≤ p) (hp2 : p ≤ 1 / 2) :
    let k0 := Nat.floor (((b : ℝ) + 1) * p)
    (∀ j : Nat, (j : ℝ) ≤ 34 * Real.sqrt (b : ℝ) →
      binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) ≤
        binomProb b p (k0 + j)) ∧
    (∀ j : Nat, (j : ℝ) ≤ 34 * Real.sqrt (b : ℝ) →
      binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) ≤
        binomProb b p (k0 - j)) := by
  intro k0
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hbR : (200000 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hsqrt_le : 34 * Real.sqrt (b : ℝ) ≤ (b : ℝ) / 13 := by
    have hsq : (34 * Real.sqrt (b : ℝ)) ^ 2 ≤ ((b : ℝ) / 13) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hbpos)]
      nlinarith
    have h1 : 0 ≤ 34 * Real.sqrt (b : ℝ) := by positivity
    have h2 : 0 ≤ (b : ℝ) / 13 := by linarith
    nlinarith
  have hk0_le : (k0 : ℝ) ≤ ((b : ℝ) + 1) * p := Nat.floor_le (by positivity)
  have hk0_gt : ((b : ℝ) + 1) * p - 1 < (k0 : ℝ) := by
    have := Nat.lt_floor_add_one (((b : ℝ) + 1) * p)
    linarith
  have hk0_lo : (b : ℝ) / 3 ≤ (k0 : ℝ) := by nlinarith
  have hk0_hi : (k0 : ℝ) ≤ (b : ℝ) * 2 / 3 := by nlinarith
  constructor
  · intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have hj_le : (j : ℝ) ≤ 34 * Real.sqrt (b : ℝ) := by push_cast at hj; linarith
      have hkj_lt : k0 + j < b := by
        have hlt : (k0 : ℝ) + (j : ℝ) < (b : ℝ) := by linarith
        have : k0 + j < b := by exact_mod_cast hlt
        exact this
      have hstep := binomProb_ratio_step b p (k0 + j) hkj_lt
      have hden_lo : (b : ℝ) / 6 ≤ ((k0 + j + 1 : Nat) : ℝ) * (1 - p) := by
        push_cast; nlinarith
      have hnum_diff : ((k0 + j + 1 : Nat) : ℝ) * (1 - p) - ((b - (k0 + j) : Nat) : ℝ) * p ≤
          ((j : ℝ) + 1) := by
        have hsub : ((b - (k0 + j) : Nat) : ℝ) = (b : ℝ) - ((k0 : ℝ) + (j : ℝ)) := by
          rw [Nat.cast_sub (by omega), Nat.cast_add]
        rw [hsub]
        push_cast
        nlinarith
      set u : ℝ := 6 * ((j : ℝ) + 1) / (b : ℝ)
      have hu0 : 0 ≤ u := by dsimp only [u]; positivity
      have hu1 : u ≤ 1 / 2 := by
        dsimp only [u]
        rw [div_le_iff₀ hbpos]
        have : (j : ℝ) + 1 ≤ 34 * Real.sqrt (b : ℝ) := by push_cast at hj; exact hj
        linarith
      have hrat_ge : (1 - u) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p)) ≤
          ((b - (k0 + j) : Nat) : ℝ) * p := by
        have hu_mul : ((j : ℝ) + 1) ≤ u * (((k0 + j + 1 : Nat) : ℝ) * (1 - p)) := by
          dsimp only [u]
          rw [div_mul_eq_mul_div, le_div_iff₀ hbpos]
          nlinarith
        linarith
      have hexp := exp_neg_two_le_one_sub hu0 hu1
      have hnn := binomProb_nonneg b hp0 hp1' (k0 + j)
      have hden_pos : 0 < ((k0 + j + 1 : Nat) : ℝ) * (1 - p) := by linarith
      have hone_step : binomProb b p (k0 + j) * Real.exp (-2 * u) ≤ binomProb b p (k0 + j + 1) := by
        have hmul : binomProb b p (k0 + j) * Real.exp (-2 * u) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p)) ≤
            binomProb b p (k0 + j + 1) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p)) := by
          rw [hstep]
          calc
            binomProb b p (k0 + j) * Real.exp (-2 * u) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p))
                ≤ binomProb b p (k0 + j) * (1 - u) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p)) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hnn) (le_of_lt hden_pos)
            _ = binomProb b p (k0 + j) * ((1 - u) * (((k0 + j + 1 : Nat) : ℝ) * (1 - p))) := by ring
            _ ≤ binomProb b p (k0 + j) * (((b - (k0 + j) : Nat) : ℝ) * p) :=
                  mul_le_mul_of_nonneg_left hrat_ge hnn
        exact le_of_mul_le_mul_right hmul hden_pos
      have hexp_eq : -6 * (((j + 1 : Nat) : ℝ) * (((j + 1 : Nat) : ℝ) + 1)) / (b : ℝ) =
          -6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ) + (-2 * u) := by
        dsimp only [u]; push_cast; ring
      calc
        binomProb b p k0 * Real.exp (-6 * (((j + 1 : Nat) : ℝ) * (((j + 1 : Nat) : ℝ) + 1)) / (b : ℝ))
            = (binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ))) * Real.exp (-2 * u) := by
                rw [hexp_eq, Real.exp_add]; ring
        _ ≤ binomProb b p (k0 + j) * Real.exp (-2 * u) :=
              mul_le_mul_of_nonneg_right (ih hj_le) (le_of_lt (Real.exp_pos _))
        _ ≤ binomProb b p (k0 + (j + 1)) := hone_step
  · intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have hj_le : (j : ℝ) ≤ 34 * Real.sqrt (b : ℝ) := by push_cast at hj; linarith
      have hj1_lt : j + 1 ≤ k0 := by
        have hlt : (j : ℝ) + 1 ≤ (k0 : ℝ) := by push_cast at hj; linarith
        exact_mod_cast hlt
      have hkm_lt : k0 - (j + 1) < b := by
        have : k0 ≤ b := by
          have : (k0 : ℝ) < (b : ℝ) := by linarith
          exact Nat.le_of_lt (by exact_mod_cast this)
        omega
      have hstep := binomProb_ratio_step b p (k0 - (j + 1)) hkm_lt
      have heq_succ : k0 - (j + 1) + 1 = k0 - j := by omega
      rw [heq_succ] at hstep
      have hden_lo : (b : ℝ) / 6 ≤ ((b - (k0 - (j + 1)) : Nat) : ℝ) * p := by
        have hsub : ((b - (k0 - (j + 1)) : Nat) : ℝ) = (b : ℝ) - ((k0 : ℝ) - ((j : ℝ) + 1)) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hj1_lt]; push_cast; ring
        rw [hsub]; nlinarith
      have hnum_diff : ((b - (k0 - (j + 1)) : Nat) : ℝ) * p - ((k0 - j : Nat) : ℝ) * (1 - p) ≤
          ((j : ℝ) + 1) := by
        have hsub1 : ((b - (k0 - (j + 1)) : Nat) : ℝ) = (b : ℝ) - ((k0 : ℝ) - ((j : ℝ) + 1)) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hj1_lt]; push_cast; ring
        have hsub2 : ((k0 - j : Nat) : ℝ) = (k0 : ℝ) - (j : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [hsub1, hsub2]
        nlinarith
      set u : ℝ := 6 * ((j : ℝ) + 1) / (b : ℝ)
      have hu0 : 0 ≤ u := by dsimp only [u]; positivity
      have hu1 : u ≤ 1 / 2 := by
        dsimp only [u]
        rw [div_le_iff₀ hbpos]
        have : (j : ℝ) + 1 ≤ 34 * Real.sqrt (b : ℝ) := by push_cast at hj; exact hj
        linarith
      have hrat_ge : (1 - u) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p) ≤
          ((k0 - j : Nat) : ℝ) * (1 - p) := by
        have hu_mul : ((j : ℝ) + 1) ≤ u * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p) := by
          dsimp only [u]
          rw [div_mul_eq_mul_div, le_div_iff₀ hbpos]
          nlinarith
        linarith
      have hexp := exp_neg_two_le_one_sub hu0 hu1
      have hnn := binomProb_nonneg b hp0 hp1' (k0 - j)
      have hden_pos : 0 < ((b - (k0 - (j + 1)) : Nat) : ℝ) * p := by linarith
      have hone_step : binomProb b p (k0 - j) * Real.exp (-2 * u) ≤ binomProb b p (k0 - (j + 1)) := by
        have hmul : binomProb b p (k0 - j) * Real.exp (-2 * u) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p) ≤
            binomProb b p (k0 - (j + 1)) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p) := by
          rw [← hstep]
          calc
            binomProb b p (k0 - j) * Real.exp (-2 * u) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p)
                ≤ binomProb b p (k0 - j) * (1 - u) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hnn) (le_of_lt hden_pos)
            _ = binomProb b p (k0 - j) * ((1 - u) * (((b - (k0 - (j + 1)) : Nat) : ℝ) * p)) := by ring
            _ ≤ binomProb b p (k0 - j) * (((k0 - j : Nat) : ℝ) * (1 - p)) :=
                  mul_le_mul_of_nonneg_left hrat_ge hnn
        exact le_of_mul_le_mul_right hmul hden_pos
      have hexp_eq : -6 * (((j + 1 : Nat) : ℝ) * (((j + 1 : Nat) : ℝ) + 1)) / (b : ℝ) =
          -6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ) + (-2 * u) := by
        dsimp only [u]; push_cast; ring
      calc
        binomProb b p k0 * Real.exp (-6 * (((j + 1 : Nat) : ℝ) * (((j + 1 : Nat) : ℝ) + 1)) / (b : ℝ))
            = (binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ))) * Real.exp (-2 * u) := by
                rw [hexp_eq, Real.exp_add]; ring
        _ ≤ binomProb b p (k0 - j) * Real.exp (-2 * u) :=
              mul_le_mul_of_nonneg_right (ih hj_le) (le_of_lt (Real.exp_pos _))
        _ ≤ binomProb b p (k0 - (j + 1)) := hone_step

private theorem binomProb_upper {b : Nat} {p : ℝ} (hb : 200000 ≤ b)
    (hp1 : 7 / 15 ≤ p) (hp2 : p ≤ 1 / 2) (k : Nat) :
    binomProb b p k ≤ 12 / Real.sqrt (b : ℝ) := by
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hp0_lt : 0 < p := by linarith
  have hp1_lt : p < 1 := by linarith
  have hbR : (200000 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hbpos
  have hsq_ge : (400 : ℝ) ≤ Real.sqrt (b : ℝ) := by
    have : (400 : ℝ) ^ 2 ≤ (b : ℝ) := by linarith
    exact (Real.le_sqrt (by norm_num) (le_of_lt hbpos)).mpr this
  let k0 := Nat.floor (((b : ℝ) + 1) * p)
  have hmax := (binomProb_mode_max b hp0_lt hp1_lt).2 k
  have hrat := (binomProb_ratio_lower hb hp1 hp2).1
  let s := Nat.floor (Real.sqrt (b : ℝ) / 4)
  have hs_le : (s : ℝ) ≤ Real.sqrt (b : ℝ) / 4 := Nat.floor_le (by positivity)
  have hs_gt : Real.sqrt (b : ℝ) / 4 - 1 < (s : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt (b : ℝ) / 4)
    linarith
  have hk0_le : (k0 : ℝ) ≤ ((b : ℝ) + 1) * p := Nat.floor_le (by positivity)
  have hsub : (Finset.range (s + 1)).image (fun j => k0 + j) ⊆ Finset.range (b + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hjle : j ≤ s := by have := Finset.mem_range.mp hj; omega
    have hlt : (k0 : ℝ) + (j : ℝ) < (b : ℝ) + 1 := by
      have hjR : (j : ℝ) ≤ (s : ℝ) := by exact_mod_cast hjle
      have hsq_b : Real.sqrt (b : ℝ) ≤ (b : ℝ) / 4 := by
        have : (Real.sqrt (b : ℝ)) ^ 2 ≤ ((b : ℝ) / 4) ^ 2 := by
          rw [Real.sq_sqrt (le_of_lt hbpos)]; nlinarith
        nlinarith
      nlinarith
    have : k0 + j < b + 1 := by exact_mod_cast hlt
    exact Finset.mem_range.mpr this
  have hsum_le : ∑ x ∈ (Finset.range (s + 1)).image (fun j => k0 + j), binomProb b p x ≤ 1 := by
    rw [← binomProb_sum_one b p]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => binomProb_nonneg b hp0 hp1' x)
  rw [Finset.sum_image (fun a _ c _ h => by omega)] at hsum_le
  have hterm_ge : ∀ j ∈ Finset.range (s + 1),
      binomProb b p k0 * Real.exp (-1) ≤ binomProb b p (k0 + j) := by
    intro j hj
    have hjle : j ≤ s := by have := Finset.mem_range.mp hj; omega
    have hjR : (j : ℝ) ≤ Real.sqrt (b : ℝ) / 4 := by
      have : (j : ℝ) ≤ (s : ℝ) := by exact_mod_cast hjle
      linarith
    have h1 := hrat j (by linarith)
    have hexp_ge : Real.exp (-1) ≤ Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ hbpos]
      have hsq : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) := Real.sq_sqrt (le_of_lt hbpos)
      nlinarith
    have hnn := binomProb_nonneg b hp0 hp1' k0
    exact le_trans (mul_le_mul_of_nonneg_left hexp_ge hnn) h1
  have hlow : ((s + 1 : Nat) : ℝ) * (binomProb b p k0 * Real.exp (-1)) ≤ 1 := by
    calc
      ((s + 1 : Nat) : ℝ) * (binomProb b p k0 * Real.exp (-1))
          = ∑ _j ∈ Finset.range (s + 1), binomProb b p k0 * Real.exp (-1) := by simp
      _ ≤ ∑ j ∈ Finset.range (s + 1), binomProb b p (k0 + j) := Finset.sum_le_sum hterm_ge
      _ ≤ 1 := hsum_le
  have hs1 : Real.sqrt (b : ℝ) / 4 ≤ ((s + 1 : Nat) : ℝ) := by push_cast; linarith
  have he1 : Real.exp 1 ≤ 3 := by
    have h := Real.exp_one_lt_d9
    linarith
  have hk0_ub : binomProb b p k0 ≤ 12 / Real.sqrt (b : ℝ) := by
    rw [le_div_iff₀ hsqpos]
    have hnn := binomProb_nonneg b hp0 hp1' k0
    have h2 : (Real.sqrt (b : ℝ) / 4) * (binomProb b p k0 * Real.exp (-1)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hs1 (by positivity)) hlow
    have h3 : binomProb b p k0 * Real.sqrt (b : ℝ) ≤ 4 * Real.exp 1 := by
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have hmul : (binomProb b p k0 * Real.sqrt (b : ℝ)) * Real.exp (-1) ≤ 4 * Real.exp 1 * Real.exp (-1) := by
        rw [mul_assoc 4, ← Real.exp_add]; norm_num; linarith
      exact le_of_mul_le_mul_right hmul (Real.exp_pos (-1))
    linarith
  exact le_trans hmax hk0_ub

private theorem binomProb_lower {b : Nat} {p : ℝ} (hb : 200000 ≤ b)
    (hp1 : 7 / 15 ≤ p) (hp2 : p ≤ 1 / 2) {k : Nat}
    (hk : |(k : ℝ) - (b : ℝ) * p| ≤ 32 * Real.sqrt (b : ℝ)) :
    Real.exp (-7000) / (4 * Real.sqrt (b : ℝ)) ≤ binomProb b p k := by
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hp0_lt : 0 < p := by linarith
  have hp1_lt : p < 1 := by linarith
  have hbR : (200000 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hbpos
  have hsq_ge : (400 : ℝ) ≤ Real.sqrt (b : ℝ) := by
    have : (400 : ℝ) ^ 2 ≤ (b : ℝ) := by linarith
    exact (Real.le_sqrt (by norm_num) (le_of_lt hbpos)).mpr this
  let k0 := Nat.floor (((b : ℝ) + 1) * p)
  have hmode := binomProb_mode_max b hp0_lt hp1_lt
  have hcheb : (3 : ℝ) / 4 ≤
      ∑ j ∈ (Finset.range (b + 1)).filter (fun (j : Nat) => |(j : ℝ) - (b : ℝ) * p| ≤ Real.sqrt (b : ℝ)),
        binomProb b p j := by
    let S := (Finset.range (b + 1)).filter (fun (j : Nat) => |(j : ℝ) - (b : ℝ) * p| ≤ Real.sqrt (b : ℝ))
    let T := (Finset.range (b + 1)).filter (fun (j : Nat) => ¬ (|(j : ℝ) - (b : ℝ) * p| ≤ Real.sqrt (b : ℝ)))
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]; intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : S ∪ T = Finset.range (b + 1) := by
      ext j; simp only [S, T, Finset.mem_union, Finset.mem_filter]; tauto
    have hT_le : (b : ℝ) * (∑ j ∈ T, binomProb b p j) ≤ (b : ℝ) / 4 := by
      calc
        (b : ℝ) * (∑ j ∈ T, binomProb b p j)
            = ∑ j ∈ T, binomProb b p j * (b : ℝ) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ ∑ j ∈ T, binomProb b p j * ((j : ℝ) - (b : ℝ) * p) ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hgt : Real.sqrt (b : ℝ) < |(j : ℝ) - (b : ℝ) * p| := by
                have := (Finset.mem_filter.mp hj).2; linarith
              have hsq : (b : ℝ) ≤ ((j : ℝ) - (b : ℝ) * p) ^ 2 := by
                have h1 : (Real.sqrt (b : ℝ)) ^ 2 ≤ (|(j : ℝ) - (b : ℝ) * p|) ^ 2 := by nlinarith
                rw [Real.sq_sqrt (le_of_lt hbpos), sq_abs] at h1
                exact h1
              exact mul_le_mul_of_nonneg_left hsq (binomProb_nonneg b hp0 hp1' j)
        _ ≤ ∑ j ∈ Finset.range (b + 1), binomProb b p j * ((j : ℝ) - (b : ℝ) * p) ^ 2 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro j _ _
              exact mul_nonneg (binomProb_nonneg b hp0 hp1' j) (sq_nonneg _)
        _ = (b : ℝ) * p * (1 - p) := binomProb_var b p
        _ ≤ (b : ℝ) / 4 := by
              have hq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
              nlinarith
    have hT_ub : ∑ j ∈ T, binomProb b p j ≤ 1 / 4 := by nlinarith
    have htot : (∑ j ∈ S, binomProb b p j) + (∑ j ∈ T, binomProb b p j) = 1 := by
      rw [← Finset.sum_union hdisj, hunion, binomProb_sum_one]
    linarith
  have hk0_lb : 1 / (4 * Real.sqrt (b : ℝ)) ≤ binomProb b p k0 := by
    let S := (Finset.range (b + 1)).filter (fun (j : Nat) => |(j : ℝ) - (b : ℝ) * p| ≤ Real.sqrt (b : ℝ))
    let lo := Nat.floor ((b : ℝ) * p - Real.sqrt (b : ℝ))
    let hi := Nat.floor ((b : ℝ) * p + Real.sqrt (b : ℝ))
    have hS_sub : S ⊆ Finset.Icc lo hi := by
      intro j hj
      have habs := (Finset.mem_filter.mp hj).2
      rw [abs_le] at habs
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.floor_le_of_le (by linarith)
      · exact Nat.le_floor (by linarith)
    have hS_card : (S.card : ℝ) ≤ 3 * Real.sqrt (b : ℝ) := by
      have hc1 : S.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card hS_sub
      rw [Nat.card_Icc] at hc1
      have hlo_gt : (b : ℝ) * p - Real.sqrt (b : ℝ) - 1 < (lo : ℝ) := by
        have := Nat.lt_floor_add_one ((b : ℝ) * p - Real.sqrt (b : ℝ)); linarith
      have hhi_le : (hi : ℝ) ≤ (b : ℝ) * p + Real.sqrt (b : ℝ) :=
        Nat.floor_le (by positivity)
      have hle_lh : lo ≤ hi := by
        apply Nat.floor_mono; linarith
      have hc2 : ((hi + 1 - lo : Nat) : ℝ) ≤ 3 * Real.sqrt (b : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      have hc1R : (S.card : ℝ) ≤ ((hi + 1 - lo : Nat) : ℝ) := by exact_mod_cast hc1
      linarith
    have hsum_ub : ∑ j ∈ S, binomProb b p j ≤ (S.card : ℝ) * binomProb b p k0 := by
      calc
        ∑ j ∈ S, binomProb b p j ≤ ∑ _j ∈ S, binomProb b p k0 :=
          Finset.sum_le_sum (fun j _ => hmode.2 j)
        _ = (S.card : ℝ) * binomProb b p k0 := by simp
    have hnn := binomProb_nonneg b hp0 hp1' k0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hk0_le : (k0 : ℝ) ≤ ((b : ℝ) + 1) * p := Nat.floor_le (by positivity)
  have hk0_gt : ((b : ℝ) + 1) * p - 1 < (k0 : ℝ) := by
    have := Nat.lt_floor_add_one (((b : ℝ) + 1) * p); linarith
  have hk_diff : |(k : ℝ) - (k0 : ℝ)| ≤ 33 * Real.sqrt (b : ℝ) := by
    rw [abs_le] at hk ⊢
    constructor <;> linarith
  have hrat := binomProb_ratio_lower hb hp1 hp2
  have hsq_b : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) := Real.sq_sqrt (le_of_lt hbpos)
  by_cases hge : k0 ≤ k
  · let j := k - k0
    have hkjeq : k0 + j = k := by omega
    have hjR : (j : ℝ) ≤ 33 * Real.sqrt (b : ℝ) := by
      rw [Nat.cast_sub hge]
      rw [abs_le] at hk_diff; linarith
    have h1 := hrat.1 j (by linarith)
    rw [hkjeq] at h1
    have hexp_ge : Real.exp (-7000) ≤ Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ hbpos]
      nlinarith
    have hnn := binomProb_nonneg b hp0 hp1' k0
    calc
      Real.exp (-7000) / (4 * Real.sqrt (b : ℝ))
          = (1 / (4 * Real.sqrt (b : ℝ))) * Real.exp (-7000) := by ring
      _ ≤ binomProb b p k0 * Real.exp (-7000) :=
            mul_le_mul_of_nonneg_right hk0_lb (le_of_lt (Real.exp_pos _))
      _ ≤ binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_ge hnn
      _ ≤ binomProb b p k := h1
  · let j := k0 - k
    have hkjeq : k0 - j = k := by omega
    have hjR : (j : ℝ) ≤ 33 * Real.sqrt (b : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      rw [abs_le] at hk_diff; linarith
    have h1 := hrat.2 j (by linarith)
    rw [hkjeq] at h1
    have hexp_ge : Real.exp (-7000) ≤ Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ hbpos]
      nlinarith
    have hnn := binomProb_nonneg b hp0 hp1' k0
    calc
      Real.exp (-7000) / (4 * Real.sqrt (b : ℝ))
          = (1 / (4 * Real.sqrt (b : ℝ))) * Real.exp (-7000) := by ring
      _ ≤ binomProb b p k0 * Real.exp (-7000) :=
            mul_le_mul_of_nonneg_right hk0_lb (le_of_lt (Real.exp_pos _))
      _ ≤ binomProb b p k0 * Real.exp (-6 * ((j : ℝ) * ((j : ℝ) + 1)) / (b : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_ge hnn
      _ ≤ binomProb b p k := h1

private def pathWeight (x : ℝ) : Nat → Nat → Nat → Nat → ℝ
  | _, 0, b, r => if b = 0 ∧ r = 0 then 1 else 0
  | 0, n + 1, b, r =>
      if 1 ≤ b then 4 * (1 + x) * pathWeight x 1 n (b - 1) r else 0
  | 1, n + 1, b, r =>
      (if 1 ≤ r then x ^ 2 * pathWeight x 0 n b (r - 1) else 0) +
      (if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) +
      pathWeight x 2 n b r
  | _, n + 1, b, r =>
      (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) +
      (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) +
      2 * pathWeight x 2 n b r

private theorem pathWeight_succ_0 (x : ℝ) (n b r : Nat) :
    pathWeight x 0 (n + 1) b r = if 1 ≤ b then 4 * (1 + x) * pathWeight x 1 n (b - 1) r else 0 := rfl

private theorem pathWeight_succ_1 (x : ℝ) (n b r : Nat) :
    pathWeight x 1 (n + 1) b r =
      (if 1 ≤ r then x ^ 2 * pathWeight x 0 n b (r - 1) else 0) +
      (if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) +
      pathWeight x 2 n b r := rfl

private theorem pathWeight_zero (x : ℝ) (mode b r : Nat) :
    pathWeight x mode 0 b r = if b = 0 ∧ r = 0 then 1 else 0 := by
  cases mode <;> rfl

private theorem pathWeight_succ_2 (x : ℝ) (n b r : Nat) :
    pathWeight x 2 (n + 1) b r =
      (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) +
      (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) +
      2 * pathWeight x 2 n b r := rfl

private theorem pathWeight_succ_ge2 (x : ℝ) (m n b r : Nat) :
    pathWeight x (m + 2) (n + 1) b r =
      (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) +
      (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) +
      2 * pathWeight x 2 n b r := rfl

private theorem pathWeight_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∀ n mode b r, 0 ≤ pathWeight x mode n b r := by
  intro n
  induction n with
  | zero =>
    intro mode b r
    rw [pathWeight_zero]
    split_ifs <;> norm_num
  | succ n ih =>
    intro mode b r
    match mode with
    | 0 =>
      rw [pathWeight_succ_0]
      split_ifs
      · have := ih 1 (b - 1) r; nlinarith
      · exact le_rfl
    | 1 =>
      rw [pathWeight_succ_1]
      have h0 : 0 ≤ if 1 ≤ r then x ^ 2 * pathWeight x 0 n b (r - 1) else 0 := by
        split_ifs
        · exact mul_nonneg (sq_nonneg x) (ih 0 b (r - 1))
        · exact le_rfl
      have h1 : 0 ≤ if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0 := by
        split_ifs
        · have := ih 1 (b - 1) r; nlinarith
        · exact le_rfl
      have h2 := ih 2 b r
      linarith
    | m + 2 =>
      rw [pathWeight_succ_ge2]
      have h0 : 0 ≤ if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0 := by
        split_ifs
        · have := ih 0 b (r - 1); nlinarith [sq_nonneg x]
        · exact le_rfl
      have h1 : 0 ≤ if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0 := by
        split_ifs
        · have := ih 1 (b - 1) r; nlinarith
        · exact le_rfl
      have h2 := ih 2 b r
      linarith

private theorem pathWeight_gt_zero (x : ℝ) :
    ∀ n mode b r, (n < b ∨ n < r) → pathWeight x mode n b r = 0 := by
  intro n
  induction n with
  | zero =>
    intro mode b r h
    rw [pathWeight_zero, if_neg (by omega)]
  | succ n ih =>
    intro mode b r h
    match mode with
    | 0 =>
      rw [pathWeight_succ_0]
      split_ifs with hb
      · rw [ih 1 (b - 1) r (by omega)]; ring
      · rfl
    | 1 =>
      rw [pathWeight_succ_1]
      have h0 : (if 1 ≤ r then x ^ 2 * pathWeight x 0 n b (r - 1) else 0) = 0 := by
        split_ifs with hr
        · rw [ih 0 b (r - 1) (by omega)]; ring
        · rfl
      have h1 : (if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) = 0 := by
        split_ifs with hb
        · rw [ih 1 (b - 1) r (by omega)]; ring
        · rfl
      have h2 : pathWeight x 2 n b r = 0 := ih 2 b r (by omega)
      rw [h0, h1, h2]; ring
    | m + 2 =>
      rw [pathWeight_succ_ge2]
      have h0 : (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) = 0 := by
        split_ifs with hr
        · rw [ih 0 b (r - 1) (by omega)]; ring
        · rfl
      have h1 : (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) = 0 := by
        split_ifs with hb
        · rw [ih 1 (b - 1) r (by omega)]; ring
        · rfl
      have h2 : pathWeight x 2 n b r = 0 := ih 2 b r (by omega)
      rw [h0, h1, h2]; ring

private theorem pathWeight_gt_sum_zero (x : ℝ) :
    ∀ n mode b r, n < b + r → pathWeight x mode n b r = 0 := by
  intro n
  induction n with
  | zero =>
    intro mode b r h
    rw [pathWeight_zero, if_neg (by omega)]
  | succ n ih =>
    intro mode b r h
    match mode with
    | 0 =>
      rw [pathWeight_succ_0]
      split_ifs with hb
      · rw [ih 1 (b - 1) r (by omega)]; ring
      · rfl
    | 1 =>
      rw [pathWeight_succ_1]
      have h0 : (if 1 ≤ r then x ^ 2 * pathWeight x 0 n b (r - 1) else 0) = 0 := by
        split_ifs with hr
        · rw [ih 0 b (r - 1) (by omega)]; ring
        · rfl
      have h1 : (if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) = 0 := by
        split_ifs with hb
        · rw [ih 1 (b - 1) r (by omega)]; ring
        · rfl
      have h2 : pathWeight x 2 n b r = 0 := ih 2 b r (by omega)
      rw [h0, h1, h2]; ring
    | m + 2 =>
      rw [pathWeight_succ_ge2]
      have h0 : (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) = 0 := by
        split_ifs with hr
        · rw [ih 0 b (r - 1) (by omega)]; ring
        · rfl
      have h1 : (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) = 0 := by
        split_ifs with hb
        · rw [ih 1 (b - 1) r (by omega)]; ring
        · rfl
      have h2 : pathWeight x 2 n b r = 0 := ih 2 b r (by omega)
      rw [h0, h1, h2]; ring

private theorem countGain_eq_pathWeight {x : ℝ} (hx : 0 < x) :
    ∀ n mode g, mode < 3 →
      (countGain mode n g : ℝ) * x ^ g =
        ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
          pathWeight x mode n b r *
            (if 2 * r ≤ g then binomProb b (x / (1 + x)) (g - 2 * r) else 0) := by
  let p : ℝ := x / (1 + x)
  have h1x : 0 < 1 + x := by linarith
  have hp1 : 1 - p = 1 / (1 + x) := by dsimp only [p]; field_simp; ring
  have hshift_b : ∀ (f : Nat → Nat → ℝ) (n : Nat) (h0 : ∀ r, f (n + 1) r = 0)
      (g : Nat),
      (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        (if 1 ≤ b then f (b - 1) r else 0) *
          (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) =
      (1 - p) * (∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
        f b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
      (if 1 ≤ g then p * (∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
        f b r * (if 2 * r ≤ g - 1 then binomProb b p (g - 1 - 2 * r) else 0)) else 0) := by
    intro f n _ g
    rw [Finset.sum_range_succ']
    simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero,
      show ∀ b, 1 ≤ b + 1 by omega, Nat.add_sub_cancel]
    have hinner : ∀ b ∈ Finset.range (n + 1), ∀ r ∈ Finset.range (n + 2),
        f b r * (if 2 * r ≤ g then binomProb (b + 1) p (g - 2 * r) else 0) =
        (1 - p) * (f b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
        (if 1 ≤ g then p * (f b r * (if 2 * r ≤ g - 1 then binomProb b p (g - 1 - 2 * r) else 0)) else 0) := by
      intro b _ r _
      by_cases h2r : 2 * r ≤ g
      · rw [if_pos h2r, if_pos h2r, binomProb_succ]
        by_cases h1g : 1 ≤ g
        · rw [if_pos h1g]
          by_cases h1sub : 1 ≤ g - 2 * r
          · have h2r1 : 2 * r ≤ g - 1 := by omega
            have hsub : g - 2 * r - 1 = g - 1 - 2 * r := by omega
            rw [if_pos h1sub, if_pos h2r1, hsub]; ring
          · have h2r1 : ¬ (2 * r ≤ g - 1) := by omega
            rw [if_neg h1sub, if_neg h2r1]; ring
        · have h1sub : ¬ (1 ≤ g - 2 * r) := by omega
          rw [if_neg h1g, if_neg h1sub]; ring
      · rw [if_neg h2r, if_neg h2r]
        by_cases h1g : 1 ≤ g
        · rw [if_pos h1g, if_neg (by omega : ¬ (2 * r ≤ g - 1))]; ring
        · rw [if_neg h1g]; ring
    calc
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
          f b r * (if 2 * r ≤ g then binomProb (b + 1) p (g - 2 * r) else 0)
          = ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
              ((1 - p) * (f b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
              (if 1 ≤ g then p * (f b r * (if 2 * r ≤ g - 1 then binomProb b p (g - 1 - 2 * r) else 0)) else 0)) := by
            apply Finset.sum_congr rfl; intro b hb; apply Finset.sum_congr rfl; intro r hr
            exact hinner b hb r hr
      _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
            split_ifs <;> simp [Finset.mul_sum]
  have hshift_r : ∀ (f : Nat → Nat → ℝ) (n g : Nat),
      (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        (if 1 ≤ r then f b (r - 1) else 0) *
          (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) =
      if 2 ≤ g then
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 1),
          f b r * (if 2 * r ≤ g - 2 then binomProb b p (g - 2 - 2 * r) else 0)
      else 0 := by
    intro f n g
    by_cases h2g : 2 ≤ g
    · rw [if_pos h2g]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_range_succ']
      simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, zero_mul, add_zero,
        show ∀ r, 1 ≤ r + 1 by omega, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h2r : 2 * r ≤ g - 2
      · rw [if_pos (by omega : 2 * (r + 1) ≤ g), if_pos h2r,
            show g - 2 * (r + 1) = g - 2 - 2 * r by omega]
      · rw [if_neg (by omega : ¬ (2 * (r + 1) ≤ g)), if_neg h2r]
    · rw [if_neg h2g]
      apply Finset.sum_eq_zero; intro b _
      apply Finset.sum_eq_zero; intro r _
      by_cases hr1 : 1 ≤ r
      · rw [if_pos hr1, if_neg (by omega : ¬ (2 * r ≤ g))]; ring
      · rw [if_neg hr1]; ring
  have htrim_r : ∀ (mode n g : Nat),
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
    intro mode n g
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_range_succ, pathWeight_gt_zero x n mode b (n + 1) (Or.inr (by omega))]
    ring
  have htrim_b : ∀ (mode n g : Nat),
      ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
    intro mode n g
    rw [Finset.sum_range_succ]
    have hz : ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n (n + 1) r * (if 2 * r ≤ g then binomProb (n + 1) p (g - 2 * r) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro r _
      rw [pathWeight_gt_zero x n mode (n + 1) r (Or.inl (by omega))]; ring
    rw [hz, add_zero]
  have htrim_br : ∀ (mode n g : Nat),
      ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
    intro mode n g
    rw [Finset.sum_range_succ]
    have hz : ∑ r ∈ Finset.range (n + 2),
        pathWeight x mode n (n + 1) r * (if 2 * r ≤ g then binomProb (n + 1) p (g - 2 * r) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro r _
      rw [pathWeight_gt_zero x n mode (n + 1) r (Or.inl (by omega))]; ring
    rw [hz, add_zero, htrim_r]
  intro n
  induction n with
  | zero =>
    intro mode g _
    rw [countGain_zero]
    cases g <;> simp [pathWeight_zero, binomProb_zero]
  | succ n ih =>
    intro mode g hmode
    have hmul_b' : ∀ (c : ℝ) (mode' : Nat), mode' < 3 →
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then c * (1 + x) * pathWeight x mode' n (b - 1) r else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
        c * ((countGain mode' n g : ℝ) * x ^ g) +
          (if 1 ≤ g then c * x * ((countGain mode' n (g - 1) : ℝ) * x ^ (g - 1)) else 0) := by
      intro c mode' hm'
      have hfactor : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then c * (1 + x) * pathWeight x mode' n (b - 1) r else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
          (c * (1 + x)) * ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
            (if 1 ≤ b then pathWeight x mode' n (b - 1) r else 0) *
              (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
        split_ifs <;> ring
      rw [hfactor, hshift_b (pathWeight x mode' n) n (fun r => pathWeight_gt_zero x n mode' (n + 1) r (Or.inl (by omega))) g,
          htrim_r, htrim_r, ← ih mode' g hm', ← ih mode' (g - 1) hm']
      have h1x_ne : (1 + x) ≠ 0 := ne_of_gt h1x
      have h1 : c * (1 + x) * (1 - p) = c := by rw [hp1]; field_simp
      have h2 : c * (1 + x) * p = c * x := by dsimp only [p]; field_simp
      by_cases h1g : 1 ≤ g
      · rw [if_pos h1g, if_pos h1g]
        calc
          c * (1 + x) * ((1 - p) * ((countGain mode' n g : ℝ) * x ^ g) +
              p * ((countGain mode' n (g - 1) : ℝ) * x ^ (g - 1)))
              = (c * (1 + x) * (1 - p)) * ((countGain mode' n g : ℝ) * x ^ g) +
                (c * (1 + x) * p) * ((countGain mode' n (g - 1) : ℝ) * x ^ (g - 1)) := by ring
          _ = _ := by rw [h1, h2]
      · rw [if_neg h1g, if_neg h1g, add_zero, add_zero, ← mul_assoc, h1]
    have hmul_r' : ∀ (c : ℝ),
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then c * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
        if 2 ≤ g then c * x ^ 2 * ((countGain 0 n (g - 2) : ℝ) * x ^ (g - 2)) else 0 := by
      intro c
      have hfactor : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then c * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
          (c * x ^ 2) * ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
            (if 1 ≤ r then pathWeight x 0 n b (r - 1) else 0) *
              (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
        split_ifs <;> ring
      rw [hfactor, hshift_r (pathWeight x 0 n) n g]
      by_cases h2g : 2 ≤ g
      · rw [if_pos h2g, if_pos h2g, htrim_b, ← ih 0 (g - 2) (by omega)]
      · rw [if_neg h2g, if_neg h2g]; ring
    have hpow1 : 1 ≤ g → x * x ^ (g - 1) = x ^ g := by
      intro h1g
      rw [← pow_succ', Nat.sub_add_cancel h1g]
    have hpow2 : 2 ≤ g → x ^ 2 * x ^ (g - 2) = x ^ g := by
      intro h2g
      rw [← pow_add, show 2 + (g - 2) = g by omega]
    match mode with
    | 0 =>
      rw [countGain_rec_0]
      change _ = ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        (if 1 ≤ b then 4 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) *
          (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)
      rw [hmul_b' 4 1 (by omega)]
      by_cases h1g : 1 ≤ g
      · rw [if_pos h1g, if_pos h1g]
        push_cast
        have := hpow1 h1g
        calc
          (4 * (countGain 1 n g : ℝ) + 4 * (countGain 1 n (g - 1) : ℝ)) * x ^ g
              = 4 * ((countGain 1 n g : ℝ) * x ^ g) + 4 * (countGain 1 n (g - 1) : ℝ) * (x * x ^ (g - 1)) := by
                  rw [this]; ring
          _ = _ := by ring
      · rw [if_neg h1g, if_neg h1g]; push_cast; ring
    | 1 =>
      rw [countGain_rec_1]
      have hsp : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 1 (n + 1) b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then 1 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then 3 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro r _
        rw [pathWeight_succ_1]
        split_ifs <;> ring
      rw [hsp, hmul_r' 1, hmul_b' 3 1 (by omega), htrim_br, ← ih 2 g (by omega)]
      by_cases h2g : 2 ≤ g
      · have h1g : 1 ≤ g := by omega
        rw [if_pos h2g, if_pos h2g, if_pos h1g, if_pos h1g]
        push_cast
        have hp1' := hpow1 h1g
        have hp2' := hpow2 h2g
        calc
          ((countGain 0 n (g - 2) : ℝ) + 3 * (countGain 1 n g : ℝ) +
              3 * (countGain 1 n (g - 1) : ℝ) + (countGain 2 n g : ℝ)) * x ^ g
              = (countGain 0 n (g - 2) : ℝ) * (x ^ 2 * x ^ (g - 2)) +
                3 * ((countGain 1 n g : ℝ) * x ^ g) +
                3 * (countGain 1 n (g - 1) : ℝ) * (x * x ^ (g - 1)) +
                (countGain 2 n g : ℝ) * x ^ g := by rw [hp1', hp2']; ring
          _ = _ := by ring
      · rw [if_neg h2g, if_neg h2g]
        by_cases h1g : 1 ≤ g
        · rw [if_pos h1g, if_pos h1g]
          push_cast
          have hp1' := hpow1 h1g
          calc
            (0 + 3 * (countGain 1 n g : ℝ) + 3 * (countGain 1 n (g - 1) : ℝ) + (countGain 2 n g : ℝ)) * x ^ g
                = 3 * ((countGain 1 n g : ℝ) * x ^ g) +
                  3 * (countGain 1 n (g - 1) : ℝ) * (x * x ^ (g - 1)) +
                  (countGain 2 n g : ℝ) * x ^ g := by rw [hp1']; ring
            _ = _ := by ring
        · rw [if_neg h1g, if_neg h1g]; push_cast; ring
    | 2 =>
      rw [countGain_rec_2]
      have hsp : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 (n + 1) b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then 2 * x ^ 2 * pathWeight x 0 n b (r - 1) else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then 2 * (1 + x) * pathWeight x 1 n (b - 1) r else 0) *
            (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) +
        2 * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro r _
        rw [pathWeight_succ_2]
        split_ifs <;> ring
      rw [hsp, hmul_r' 2, hmul_b' 2 1 (by omega), htrim_br, ← ih 2 g (by omega)]
      by_cases h2g : 2 ≤ g
      · have h1g : 1 ≤ g := by omega
        rw [if_pos h2g, if_pos h2g, if_pos h1g, if_pos h1g]
        push_cast
        have hp1' := hpow1 h1g
        have hp2' := hpow2 h2g
        calc
          (2 * (countGain 0 n (g - 2) : ℝ) + 2 * (countGain 1 n g : ℝ) +
              2 * (countGain 1 n (g - 1) : ℝ) + 2 * (countGain 2 n g : ℝ)) * x ^ g
              = 2 * (countGain 0 n (g - 2) : ℝ) * (x ^ 2 * x ^ (g - 2)) +
                2 * ((countGain 1 n g : ℝ) * x ^ g) +
                2 * (countGain 1 n (g - 1) : ℝ) * (x * x ^ (g - 1)) +
                2 * ((countGain 2 n g : ℝ) * x ^ g) := by rw [hp1', hp2']; ring
          _ = _ := by ring
      · rw [if_neg h2g, if_neg h2g]
        by_cases h1g : 1 ≤ g
        · rw [if_pos h1g, if_pos h1g]
          push_cast
          have hp1' := hpow1 h1g
          calc
            (0 + 2 * (countGain 1 n g : ℝ) + 2 * (countGain 1 n (g - 1) : ℝ) + 2 * (countGain 2 n g : ℝ)) * x ^ g
                = 2 * ((countGain 1 n g : ℝ) * x ^ g) +
                  2 * (countGain 1 n (g - 1) : ℝ) * (x * x ^ (g - 1)) +
                  2 * ((countGain 2 n g : ℝ) * x ^ g) := by rw [hp1']; ring
            _ = _ := by ring
        · rw [if_neg h1g, if_neg h1g]; push_cast; ring
    | _ + 3 => omega

private def mgfSum (x : ℝ) (mode n : Nat) : ℝ :=
  ∑ g ∈ Finset.range (2 * n + 1), (countGain mode n g : ℝ) * x ^ g

private theorem pathWeight_total_sum {x : ℝ} (hx : 0 < x) (mode n : Nat) (hm : mode < 3) :
    ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), pathWeight x mode n b r =
      mgfSum x mode n := by
  unfold mgfSum
  have h1 : ∑ g ∈ Finset.range (2 * n + 1), (countGain mode n g : ℝ) * x ^ g =
      ∑ g ∈ Finset.range (2 * n + 1), ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r *
          (if 2 * r ≤ g then binomProb b (x / (1 + x)) (g - 2 * r) else 0) := by
    apply Finset.sum_congr rfl; intro g _
    exact countGain_eq_pathWeight hx n mode g hm
  rw [h1]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r hr
  rw [← Finset.mul_sum]
  have hble : b ≤ n := by have := Finset.mem_range.mp hb; omega
  have hrle : r ≤ n := by have := Finset.mem_range.mp hr; omega
  by_cases hbr : b + r ≤ n
  · have hsum_g' : ∑ g ∈ Finset.range (2 * n + 1),
        (if 2 * r ≤ g then binomProb b (x / (1 + x)) (g - 2 * r) else 0) = 1 := by
      have hsplit : ∑ g ∈ Finset.range (2 * n + 1),
          (if 2 * r ≤ g then binomProb b (x / (1 + x)) (g - 2 * r) else 0) =
        ∑ k ∈ Finset.range (2 * n + 1 - 2 * r), binomProb b (x / (1 + x)) k := by
        have hsub : 2 * r + (2 * n + 1 - 2 * r) = 2 * n + 1 := by omega
        conv_lhs => rw [← hsub, Finset.sum_range_add]
        have hz : ∑ g ∈ Finset.range (2 * r),
            (if 2 * r ≤ g then binomProb b (x / (1 + x)) (g - 2 * r) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro g hg
          rw [if_neg (by have := Finset.mem_range.mp hg; omega)]
        rw [hz, zero_add]
        apply Finset.sum_congr rfl; intro k _
        rw [if_pos (by omega), show 2 * r + k - 2 * r = k by omega]
      rw [hsplit]
      have hle : b + 1 ≤ 2 * n + 1 - 2 * r := by omega
      have heq : 2 * n + 1 - 2 * r = (b + 1) + (2 * n + 1 - 2 * r - (b + 1)) := by omega
      rw [heq, Finset.sum_range_add, binomProb_sum_one]
      have hz : ∑ k ∈ Finset.range (2 * n + 1 - 2 * r - (b + 1)),
          binomProb b (x / (1 + x)) (b + 1 + k) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        unfold binomProb; rw [if_neg (by omega)]
      rw [hz, add_zero]
    rw [hsum_g', mul_one]
  · have h0 : pathWeight x mode n b r = 0 := pathWeight_gt_sum_zero x n mode b r (by omega)
    rw [h0, zero_mul]

private theorem pathWeight_half_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ n mode, mode < 3 →
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x mode n b r * ((1 / 2 : ℝ) ^ b) ≤ (6 : ℝ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro mode _
    simp [pathWeight]
  | succ n ih =>
    have hshift_b : ∀ (mode' : Nat), mode' < 3 →
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then pathWeight x mode' n (b - 1) r else 0) * ((1 / 2 : ℝ) ^ b) ≤
        (1 / 2 : ℝ) * (6 : ℝ) ^ n := by
      intro mode' hm'
      rw [Finset.sum_range_succ']
      simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero,
        show ∀ b, 1 ≤ b + 1 by omega, Nat.add_sub_cancel]
      have hrew : ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ (b + 1)) =
        (1 / 2 : ℝ) * ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ b) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_range_succ, pathWeight_gt_zero x n mode' b (n + 1) (Or.inr (by omega)),
            zero_mul, add_zero, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _
        rw [pow_succ]; ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left (ih mode' hm') (by norm_num)
    have hshift_r : ∀ (mode' : Nat), mode' < 3 →
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then pathWeight x mode' n b (r - 1) else 0) * ((1 / 2 : ℝ) ^ b) ≤
        (6 : ℝ) ^ n := by
      intro mode' hm'
      have hrew : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then pathWeight x mode' n b (r - 1) else 0) * ((1 / 2 : ℝ) ^ b) =
        ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ b) := by
        rw [Finset.sum_range_succ]
        have hz : ∑ r ∈ Finset.range (n + 2),
            (if 1 ≤ r then pathWeight x mode' n (n + 1) (r - 1) else 0) * ((1 / 2 : ℝ) ^ (n + 1)) = 0 := by
          apply Finset.sum_eq_zero; intro r _
          split_ifs
          · rw [pathWeight_gt_zero x n mode' (n + 1) (r - 1) (Or.inl (by omega))]; ring
          · ring
        rw [hz, add_zero]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_range_succ']
        simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, zero_mul, add_zero,
          show ∀ r, 1 ≤ r + 1 by omega, Nat.add_sub_cancel]
      rw [hrew]
      exact ih mode' hm'
    have hstay : ∀ (mode' : Nat), mode' < 3 →
        ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ b) ≤ (6 : ℝ) ^ n := by
      intro mode' hm'
      have hrew : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ b) =
        ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
          pathWeight x mode' n b r * ((1 / 2 : ℝ) ^ b) := by
        rw [Finset.sum_range_succ]
        have hz : ∑ r ∈ Finset.range (n + 2),
            pathWeight x mode' n (n + 1) r * ((1 / 2 : ℝ) ^ (n + 1)) = 0 := by
          apply Finset.sum_eq_zero; intro r _
          rw [pathWeight_gt_zero x n mode' (n + 1) r (Or.inl (by omega))]; ring
        rw [hz, add_zero]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_range_succ, pathWeight_gt_zero x n mode' b (n + 1) (Or.inr (by omega)),
            zero_mul, add_zero]
      rw [hrew]
      exact ih mode' hm'
    intro mode hm
    match mode with
    | 0 =>
      have hrew : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 0 (n + 1) b r * ((1 / 2 : ℝ) ^ b) =
        (4 * (1 + x)) * ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then pathWeight x 1 n (b - 1) r else 0) * ((1 / 2 : ℝ) ^ b) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
        rw [pathWeight_succ_0]; split_ifs <;> ring
      rw [hrew, pow_succ]
      have h1 := hshift_b 1 (by omega)
      have h6nn : (0 : ℝ) ≤ (6 : ℝ) ^ n := by positivity
      nlinarith
    | 1 =>
      have hrew : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 1 (n + 1) b r * ((1 / 2 : ℝ) ^ b) =
        x ^ 2 * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then pathWeight x 0 n b (r - 1) else 0) * ((1 / 2 : ℝ) ^ b)) +
        (3 * (1 + x)) * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then pathWeight x 1 n (b - 1) r else 0) * ((1 / 2 : ℝ) ^ b)) +
        (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 n b r * ((1 / 2 : ℝ) ^ b)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro r _
        rw [pathWeight_succ_1]; split_ifs <;> ring
      rw [hrew, pow_succ]
      have h0 := mul_le_mul_of_nonneg_left (hshift_r 0 (by omega)) (sq_nonneg x)
      have h1 := mul_le_mul_of_nonneg_left (hshift_b 1 (by omega)) (show (0 : ℝ) ≤ 3 * (1 + x) by linarith)
      have h2 := hstay 2 (by omega)
      have h6nn : (0 : ℝ) ≤ (6 : ℝ) ^ n := by positivity
      have hx2 : x ^ 2 ≤ 1 := by nlinarith
      have h0' : x ^ 2 * (6 : ℝ) ^ n ≤ (6 : ℝ) ^ n := by nlinarith
      have h1' : 3 * (1 + x) * (1 / 2 * (6 : ℝ) ^ n) ≤ 3 * (6 : ℝ) ^ n := by nlinarith
      calc
        _ ≤ x ^ 2 * (6 : ℝ) ^ n + 3 * (1 + x) * ((1 / 2 : ℝ) * (6 : ℝ) ^ n) + (6 : ℝ) ^ n := add_le_add (add_le_add h0 h1) h2
        _ ≤ (6 : ℝ) ^ n + 3 * (6 : ℝ) ^ n + (6 : ℝ) ^ n := add_le_add (add_le_add h0' h1') le_rfl
        _ ≤ (6 : ℝ) ^ n * 6 := by linarith
    | 2 =>
      have hrew : ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 (n + 1) b r * ((1 / 2 : ℝ) ^ b) =
        (2 * x ^ 2) * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ r then pathWeight x 0 n b (r - 1) else 0) * ((1 / 2 : ℝ) ^ b)) +
        (2 * (1 + x)) * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          (if 1 ≤ b then pathWeight x 1 n (b - 1) r else 0) * ((1 / 2 : ℝ) ^ b)) +
        2 * (∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
          pathWeight x 2 n b r * ((1 / 2 : ℝ) ^ b)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro r _
        rw [pathWeight_succ_2]; split_ifs <;> ring
      rw [hrew, pow_succ]
      have h0 := mul_le_mul_of_nonneg_left (hshift_r 0 (by omega)) (show (0 : ℝ) ≤ 2 * x ^ 2 by positivity)
      have h1 := mul_le_mul_of_nonneg_left (hshift_b 1 (by omega)) (show (0 : ℝ) ≤ 2 * (1 + x) by linarith)
      have h2 := mul_le_mul_of_nonneg_left (hstay 2 (by omega)) (by norm_num : (0 : ℝ) ≤ 2)
      have h6nn : (0 : ℝ) ≤ (6 : ℝ) ^ n := by positivity
      have hx2 : x ^ 2 ≤ 1 := by nlinarith
      have h0' : 2 * x ^ 2 * (6 : ℝ) ^ n ≤ 2 * (6 : ℝ) ^ n := by nlinarith
      have h1' : 2 * (1 + x) * (1 / 2 * (6 : ℝ) ^ n) ≤ 2 * (6 : ℝ) ^ n := by nlinarith
      calc
        _ ≤ 2 * x ^ 2 * (6 : ℝ) ^ n + 2 * (1 + x) * ((1 / 2 : ℝ) * (6 : ℝ) ^ n) + 2 * (6 : ℝ) ^ n := add_le_add (add_le_add h0 h1) h2
        _ ≤ 2 * (6 : ℝ) ^ n + 2 * (6 : ℝ) ^ n + 2 * (6 : ℝ) ^ n := add_le_add (add_le_add h0' h1') le_rfl
        _ = (6 : ℝ) ^ n * 6 := by ring
    | _ + 3 => omega

private theorem mgfSum_rec (x : ℝ) (hx : 0 < x) (n : Nat) :
    mgfSum x 0 (n + 1) = 4 * (1 + x) * mgfSum x 1 n ∧
    mgfSum x 1 (n + 1) = x ^ 2 * mgfSum x 0 n + 3 * (1 + x) * mgfSum x 1 n + mgfSum x 2 n ∧
    mgfSum x 2 (n + 1) = 2 * x ^ 2 * mgfSum x 0 n + 2 * (1 + x) * mgfSum x 1 n + 2 * mgfSum x 2 n := by
  have hrec := fun m hm => (pathWeight_total_sum hx m (n + 1) hm).symm
  have htot := fun m hm => pathWeight_total_sum hx m n hm
  have hsb : ∀ m, m < 3 →
      ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        (if 1 ≤ b then pathWeight x m n (b - 1) r else 0) = mgfSum x m n := by
    intro m hm
    rw [Finset.sum_range_succ']
    simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, Finset.sum_const_zero, add_zero,
      show ∀ b, 1 ≤ b + 1 by omega, Nat.add_sub_cancel]
    rw [← htot m hm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_range_succ, pathWeight_gt_zero x n m b (n + 1) (Or.inr (by omega)), add_zero]
  have hsr : ∀ m, m < 3 →
      ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2),
        (if 1 ≤ r then pathWeight x m n b (r - 1) else 0) = mgfSum x m n := by
    intro m hm
    rw [Finset.sum_range_succ]
    have hz : ∑ r ∈ Finset.range (n + 2), (if 1 ≤ r then pathWeight x m n (n + 1) (r - 1) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro r _
      split_ifs
      · exact pathWeight_gt_zero x n m (n + 1) (r - 1) (Or.inl (by omega))
      · rfl
    rw [hz, add_zero, ← htot m hm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_range_succ']
    simp only [show ¬ (1 ≤ 0) by omega, ↓reduceIte, add_zero, show ∀ r, 1 ≤ r + 1 by omega,
      Nat.add_sub_cancel]
  have hst : ∀ m, m < 3 →
      ∑ b ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2), pathWeight x m n b r = mgfSum x m n := by
    intro m hm
    rw [Finset.sum_range_succ]
    have hz : ∑ r ∈ Finset.range (n + 2), pathWeight x m n (n + 1) r = 0 := by
      apply Finset.sum_eq_zero; intro r _
      exact pathWeight_gt_zero x n m (n + 1) r (Or.inl (by omega))
    rw [hz, add_zero, ← htot m hm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_range_succ, pathWeight_gt_zero x n m b (n + 1) (Or.inr (by omega)), add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrec 0 (by omega), ← hsb 1 (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
    rw [pathWeight_succ_0]; split_ifs <;> ring
  · rw [hrec 1 (by omega), ← hsr 0 (by omega), ← hsb 1 (by omega), ← hst 2 (by omega)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro r _
    rw [pathWeight_succ_1]; split_ifs <;> ring
  · rw [hrec 2 (by omega), ← hsr 0 (by omega), ← hsb 1 (by omega), ← hst 2 (by omega)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro r _
    rw [pathWeight_succ_2]; split_ifs <;> ring

private noncomputable def lam (x : ℝ) : ℝ :=
  ((3 * x + 5) + Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2)) / 16

private theorem lam_quad {x : ℝ} (hx1 : 3 / 4 ≤ x) (hx2 : x ≤ 1) :
    let μ := 8 * lam x
    6 ≤ μ ∧ μ ≤ 8 ∧ μ ^ 2 - (3 * x + 5) * μ + 4 * (1 - x) * (1 + x) ^ 2 = 0 := by
  intro μ
  have hdisc : 25 ≤ (3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2 := by nlinarith
  have hdisc_ub : (3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2 ≤ 64 := by nlinarith
  have hsq5 : 5 ≤ Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hsq8 : Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2) ≤ 8 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsq : (Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2)) ^ 2 =
      (3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2 := Real.sq_sqrt (by linarith)
  have hμeq : μ = ((3 * x + 5) + Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2)) / 2 := by
    dsimp only [μ, lam]; ring
  refine ⟨by rw [hμeq]; linarith, by rw [hμeq]; linarith, ?_⟩
  rw [hμeq]
  nlinarith

private theorem mgfSum_sandwich {x : ℝ} (hx1 : 3 / 4 ≤ x) (hx2 : x ≤ 1) :
    let μ := 8 * lam x
    let v0 := 4 * (1 + x) / μ
    let v2 := 2 - v0
    ∀ n,
      (1 / 2) * v0 * μ ^ n ≤ mgfSum x 0 n ∧ mgfSum x 0 n ≤ 2 * v0 * μ ^ n ∧
      (1 / 2) * 1 * μ ^ n ≤ mgfSum x 1 n ∧ mgfSum x 1 n ≤ 2 * 1 * μ ^ n ∧
      (1 / 2) * v2 * μ ^ n ≤ mgfSum x 2 n ∧ mgfSum x 2 n ≤ 2 * v2 * μ ^ n := by
  intro μ v0 v2
  obtain ⟨hμ6, hμ8, hquad⟩ := lam_quad hx1 hx2
  have hμpos : 0 < μ := by linarith
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hv0_lo : 1 / 2 ≤ v0 := by
    dsimp only [v0]; rw [le_div_iff₀ hμpos]; linarith
  have hv0_hi : v0 ≤ 4 / 3 := by
    dsimp only [v0]; rw [div_le_iff₀ hμpos]; linarith
  have hv2_lo : 1 / 2 ≤ v2 := by dsimp only [v2]; linarith
  have hv2_hi : v2 ≤ 2 := by dsimp only [v2]; linarith
  have heig0 : 4 * (1 + x) * 1 = μ * v0 := by dsimp only [v0]; field_simp
  have heig1 : x ^ 2 * v0 + 3 * (1 + x) * 1 + v2 = μ * 1 := by
    dsimp only [v2, v0]
    field_simp
    nlinarith
  have heig2 : 2 * x ^ 2 * v0 + 2 * (1 + x) * 1 + 2 * v2 = μ * v2 := by
    dsimp only [v2, v0]
    field_simp
    nlinarith
  intro n
  induction n with
  | zero =>
    have h0 : mgfSum x 0 0 = 1 := by unfold mgfSum; simp [countGain_zero]
    have h1 : mgfSum x 1 0 = 1 := by unfold mgfSum; simp [countGain_zero]
    have h2 : mgfSum x 2 0 = 1 := by unfold mgfSum; simp [countGain_zero]
    rw [h0, h1, h2]
    refine ⟨by nlinarith, by nlinarith, by norm_num, by norm_num, by nlinarith, by nlinarith⟩
  | succ n ih =>
    rcases ih with ⟨l0, u0, l1, u1, l2, u2⟩
    rcases mgfSum_rec x (by linarith) n with ⟨r0, r1, r2⟩
    rw [r0, r1, r2, pow_succ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        1 / 2 * v0 * (μ ^ n * μ) = (1 / 2 * μ ^ n) * (μ * v0) := by ring
        _ = (1 / 2 * μ ^ n) * (4 * (1 + x) * 1) := by rw [← heig0]
        _ = 4 * (1 + x) * (1 / 2 * 1 * μ ^ n) := by ring
        _ ≤ 4 * (1 + x) * mgfSum x 1 n := mul_le_mul_of_nonneg_left l1 (by linarith)
    · calc
        4 * (1 + x) * mgfSum x 1 n ≤ 4 * (1 + x) * (2 * 1 * μ ^ n) :=
          mul_le_mul_of_nonneg_left u1 (by linarith)
        _ = (2 * μ ^ n) * (4 * (1 + x) * 1) := by ring
        _ = (2 * μ ^ n) * (μ * v0) := by rw [heig0]
        _ = 2 * v0 * (μ ^ n * μ) := by ring
    · calc
        1 / 2 * 1 * (μ ^ n * μ) = (1 / 2 * μ ^ n) * (μ * 1) := by ring
        _ = (1 / 2 * μ ^ n) * (x ^ 2 * v0 + 3 * (1 + x) * 1 + v2) := by rw [← heig1]
        _ = x ^ 2 * (1 / 2 * v0 * μ ^ n) + 3 * (1 + x) * (1 / 2 * 1 * μ ^ n) + (1 / 2 * v2 * μ ^ n) := by ring
        _ ≤ x ^ 2 * mgfSum x 0 n + 3 * (1 + x) * mgfSum x 1 n + mgfSum x 2 n := by
          have s0 := mul_le_mul_of_nonneg_left l0 (sq_nonneg x)
          have s1 := mul_le_mul_of_nonneg_left l1 (show (0 : ℝ) ≤ 3 * (1 + x) by linarith)
          linarith
    · calc
        x ^ 2 * mgfSum x 0 n + 3 * (1 + x) * mgfSum x 1 n + mgfSum x 2 n
            ≤ x ^ 2 * (2 * v0 * μ ^ n) + 3 * (1 + x) * (2 * 1 * μ ^ n) + (2 * v2 * μ ^ n) := by
          have s0 := mul_le_mul_of_nonneg_left u0 (sq_nonneg x)
          have s1 := mul_le_mul_of_nonneg_left u1 (show (0 : ℝ) ≤ 3 * (1 + x) by linarith)
          linarith
        _ = (2 * μ ^ n) * (x ^ 2 * v0 + 3 * (1 + x) * 1 + v2) := by ring
        _ = (2 * μ ^ n) * (μ * 1) := by rw [heig1]
        _ = 2 * 1 * (μ ^ n * μ) := by ring
    · calc
        1 / 2 * v2 * (μ ^ n * μ) = (1 / 2 * μ ^ n) * (μ * v2) := by ring
        _ = (1 / 2 * μ ^ n) * (2 * x ^ 2 * v0 + 2 * (1 + x) * 1 + 2 * v2) := by rw [← heig2]
        _ = 2 * x ^ 2 * (1 / 2 * v0 * μ ^ n) + 2 * (1 + x) * (1 / 2 * 1 * μ ^ n) + 2 * (1 / 2 * v2 * μ ^ n) := by ring
        _ ≤ 2 * x ^ 2 * mgfSum x 0 n + 2 * (1 + x) * mgfSum x 1 n + 2 * mgfSum x 2 n := by
          have s0 := mul_le_mul_of_nonneg_left l0 (show (0 : ℝ) ≤ 2 * x ^ 2 by positivity)
          have s1 := mul_le_mul_of_nonneg_left l1 (show (0 : ℝ) ≤ 2 * (1 + x) by linarith)
          linarith
    · calc
        2 * x ^ 2 * mgfSum x 0 n + 2 * (1 + x) * mgfSum x 1 n + 2 * mgfSum x 2 n
            ≤ 2 * x ^ 2 * (2 * v0 * μ ^ n) + 2 * (1 + x) * (2 * 1 * μ ^ n) + 2 * (2 * v2 * μ ^ n) := by
          have s0 := mul_le_mul_of_nonneg_left u0 (show (0 : ℝ) ≤ 2 * x ^ 2 by positivity)
          have s1 := mul_le_mul_of_nonneg_left u1 (show (0 : ℝ) ≤ 2 * (1 + x) by linarith)
          linarith
        _ = (2 * μ ^ n) * (2 * x ^ 2 * v0 + 2 * (1 + x) * 1 + 2 * v2) := by ring
        _ = (2 * μ ^ n) * (μ * v2) := by rw [heig2]
        _ = 2 * v2 * (μ ^ n * μ) := by ring

private theorem mgfSum_0_bounds {x : ℝ} (hx1 : 3 / 4 ≤ x) (hx2 : x ≤ 1) (n : Nat) :
    (1 / 4) * (8 * lam x) ^ n ≤ mgfSum x 0 n ∧ mgfSum x 0 n ≤ 4 * (8 * lam x) ^ n := by
  have h := mgfSum_sandwich hx1 hx2 n
  obtain ⟨hμ6, hμ8, _⟩ := lam_quad hx1 hx2
  have hμpos : 0 < 8 * lam x := by linarith
  have hv0_lo : 1 / 2 ≤ 4 * (1 + x) / (8 * lam x) := by rw [le_div_iff₀ hμpos]; linarith
  have hv0_hi : 4 * (1 + x) / (8 * lam x) ≤ 2 := by rw [div_le_iff₀ hμpos]; linarith
  have hpnn : 0 ≤ (8 * lam x) ^ n := by positivity
  constructor <;> nlinarith [h.1, h.2.1]

private theorem exp_cubic_bound {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ |z| ^ 3 := by
  have h := Real.exp_bound (x := z) (by linarith) (n := 3) (by omega)
  have hsum : ∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℝ) = 1 + z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hcoef : ((Nat.succ 3 : Nat) : ℝ) / ((Nat.factorial 3 : ℝ) * (3 : Nat)) ≤ 1 := by
    norm_num [Nat.factorial]
  calc
    |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |z| ^ 3 * (((Nat.succ 3 : Nat) : ℝ) / ((Nat.factorial 3 : ℝ) * (3 : Nat))) := h
    _ ≤ |z| ^ 3 * 1 := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = |z| ^ 3 := mul_one _

private theorem lam_t_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 8) :
    1 - (5 / 8) * t + (13 / 32) * t ^ 2 - 4 * t ^ 3 ≤ lam (Real.exp (-t)) ∧
    lam (Real.exp (-t)) ≤ 1 - (5 / 8) * t + (13 / 32) * t ^ 2 + 4 * t ^ 3 := by
  set x := Real.exp (-t)
  have hexp_t := exp_cubic_bound (z := -t) (by rw [abs_neg, abs_of_nonneg ht0]; linarith)
  rw [abs_neg, abs_of_nonneg ht0, abs_le] at hexp_t
  set e := 1 - x
  have he_lo : t - t ^ 2 / 2 - t ^ 3 ≤ e := by dsimp only [e, x]; linarith
  have he_hi : e ≤ t - t ^ 2 / 2 + t ^ 3 := by dsimp only [e, x]; linarith
  have he0 : 0 ≤ e := by nlinarith
  have he8 : e ≤ 1 / 8 := by nlinarith
  have hx1 : 3 / 4 ≤ x := by dsimp only [e] at he8; linarith
  have hx2 : x ≤ 1 := by dsimp only [e] at he0; linarith
  obtain ⟨hμ6, hμ8, hquad⟩ := lam_quad hx1 hx2
  have hlam_lo_7 : 3 / 4 ≤ lam x := by linarith
  have hQ_eq : ∀ y : ℝ, 8 * y ^ 2 - (3 * x + 5) * y + (1 / 2) * (1 - x) * (1 + x) ^ 2 =
      8 * (y - lam x) * (y - ((3 * x + 5) / 8 - lam x)) := by
    intro y
    have hq : 8 * (lam x) ^ 2 - (3 * x + 5) * lam x + (1 / 2) * (1 - x) * (1 + x) ^ 2 = 0 := by
      nlinarith
    linarith [hq]
  have hother_lt : (3 * x + 5) / 8 - lam x ≤ 1 / 4 := by linarith
  have hlam_poly_lo : 1 - (5 / 8) * e + (3 / 32) * e ^ 2 - e ^ 3 ≤ lam x := by
    set y := 1 - (5 / 8) * e + (3 / 32) * e ^ 2 - e ^ 3
    have hy : 1 / 2 ≤ y := by dsimp only [y]; nlinarith
    have hQy : 8 * y ^ 2 - (3 * x + 5) * y + (1 / 2) * (1 - x) * (1 + x) ^ 2 ≤ 0 := by
      have hx_eq : x = 1 - e := by dsimp only [e]; ring
      rw [hx_eq]
      have hfac : 8 * y ^ 2 - (3 * (1 - e) + 5) * y + (1 / 2) * (1 - (1 - e)) * (1 + (1 - e)) ^ 2 =
          e ^ 3 * (-(261 / 32) + (905 / 128) * e - (3 / 2) * e ^ 2 + 8 * e ^ 3) := by
        dsimp only [y]; ring
      rw [hfac]
      have he3_nn : 0 ≤ e ^ 3 := by positivity
      have he2_nn : 0 ≤ e ^ 2 := sq_nonneg e
      have he3_ub : e ^ 3 ≤ 1 / 512 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos he3_nn (by linarith)
    rw [hQ_eq y] at hQy
    have hpos : 0 < y - ((3 * x + 5) / 8 - lam x) := by linarith
    by_contra hlt
    have hgt : 0 < 8 * (y - lam x) := by linarith
    have : 0 < 8 * (y - lam x) * (y - ((3 * x + 5) / 8 - lam x)) := mul_pos hgt hpos
    linarith
  have hlam_poly_hi : lam x ≤ 1 - (5 / 8) * e + (3 / 32) * e ^ 2 + e ^ 3 := by
    set y := 1 - (5 / 8) * e + (3 / 32) * e ^ 2 + e ^ 3
    have hy : 1 / 2 ≤ y := by dsimp only [y]; nlinarith
    have hQy : 0 ≤ 8 * y ^ 2 - (3 * x + 5) * y + (1 / 2) * (1 - x) * (1 + x) ^ 2 := by
      have hx_eq : x = 1 - e := by dsimp only [e]; ring
      rw [hx_eq]
      have hfac : 8 * y ^ 2 - (3 * (1 - e) + 5) * y + (1 / 2) * (1 - (1 - e)) * (1 + (1 - e)) ^ 2 =
          e ^ 3 * (251 / 32 - (887 / 128) * e + (3 / 2) * e ^ 2 + 8 * e ^ 3) := by
        dsimp only [y]; ring
      rw [hfac]
      have he3_nn : 0 ≤ e ^ 3 := by positivity
      have he2_nn : 0 ≤ e ^ 2 := sq_nonneg e
      exact mul_nonneg he3_nn (by linarith)
    rw [hQ_eq y] at hQy
    have hpos : 0 < y - ((3 * x + 5) / 8 - lam x) := by linarith
    have : 0 ≤ 8 * (y - lam x) := nonneg_of_mul_nonneg_left hQy hpos
    linarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have he_le_t : e ≤ t := by nlinarith
  have he_ge_t2 : t - t ^ 2 ≤ e := by nlinarith
  have he2_lo : t ^ 2 - 2 * t ^ 3 ≤ e ^ 2 := by
    have h1 : (t - t ^ 2) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (by nlinarith) he_ge_t2 2
    nlinarith
  have he2_hi : e ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ he0 he_le_t 2
  have he3_hi : e ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ he0 he_le_t 3
  exact ⟨by linarith, by linarith⟩

private theorem log_lam_expansion {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 8) :
    -(5 / 8) * t + (27 / 128) * t ^ 2 - 20 * t ^ 3 ≤ Real.log (lam (Real.exp (-t))) ∧
    Real.log (lam (Real.exp (-t))) ≤ -(5 / 8) * t + (27 / 128) * t ^ 2 + 20 * t ^ 3 := by
  obtain ⟨hlam_t_lo, hlam_t_hi⟩ := lam_t_bounds ht0 ht1
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have ht2_le : t ^ 2 ≤ (1 / 8) * t := by nlinarith
  have ht3_le : t ^ 3 ≤ (1 / 64) * t := by nlinarith
  have ht3_ub : t ^ 3 ≤ 1 / 512 := by nlinarith
  have hlam_pos : 0 < lam (Real.exp (-t)) := by linarith
  constructor
  · rw [Real.le_log_iff_exp_le hlam_pos]
    set z := -(5 / 8) * t + (27 / 128) * t ^ 2 - 20 * t ^ 3
    have hz_abs : |z| ≤ 1 / 2 := by
      rw [abs_le]; dsimp only [z]; constructor <;> linarith
    have hz_bd := (abs_le.mp (exp_cubic_bound hz_abs)).2
    have habs_z : |z| ≤ t := by
      rw [abs_le]; dsimp only [z]; constructor <;> linarith
    have hz3 : |z| ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (abs_nonneg z) habs_z 3
    have hz2_ub : z ^ 2 ≤ (25 / 64) * t ^ 2 + 4 * t ^ 3 := by
      have hfac : z ^ 2 - (25 / 64) * t ^ 2 - 4 * t ^ 3 =
          t ^ 3 * (-(2183 / 512) + (410329 / 16384) * t - (135 / 16) * t ^ 2 + 400 * t ^ 3) := by
        dsimp only [z]; ring
      have hle : z ^ 2 - (25 / 64) * t ^ 2 - 4 * t ^ 3 ≤ 0 := by
        rw [hfac]; exact mul_nonpos_of_nonneg_of_nonpos ht3 (by linarith)
      linarith
    have hz_def : z = -(5 / 8) * t + (27 / 128) * t ^ 2 - 20 * t ^ 3 := rfl
    linarith
  · rw [Real.log_le_iff_le_exp hlam_pos]
    set z := -(5 / 8) * t + (27 / 128) * t ^ 2 + 20 * t ^ 3
    have hz_abs : |z| ≤ 1 / 2 := by
      rw [abs_le]; dsimp only [z]; constructor <;> linarith
    have hz_bd := (abs_le.mp (exp_cubic_bound hz_abs)).1
    have habs_z : |z| ≤ t := by
      rw [abs_le]; dsimp only [z]; constructor <;> linarith
    have hz3 : |z| ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (abs_nonneg z) habs_z 3
    have hz2_lb : (25 / 64) * t ^ 2 - 4 * t ^ 3 ≤ z ^ 2 := by
      have hfac : z ^ 2 - (25 / 64) * t ^ 2 + 4 * t ^ 3 =
          t ^ 3 * (1913 / 512 - (408871 / 16384) * t + (135 / 16) * t ^ 2 + 400 * t ^ 3) := by
        dsimp only [z]; ring
      have hge : 0 ≤ z ^ 2 - (25 / 64) * t ^ 2 + 4 * t ^ 3 := by
        rw [hfac]; exact mul_nonneg ht3 (by linarith)
      linarith
    have hz_def : z = -(5 / 8) * t + (27 / 128) * t ^ 2 + 20 * t ^ 3 := rfl
    linarith

private theorem log_le_eight_root8 {n : Nat} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set u := Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ)))
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn_pos))
  have hu8 : u ^ 8 = (n : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (u ^ 2) ^ 2 = Real.sqrt (n : ℝ) := by
      rw [h1]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : ((u ^ 2) ^ 2) ^ 2 = (n : ℝ) := by
      rw [h2]; exact Real.sq_sqrt (le_of_lt hn_pos)
    calc
      u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) := h3
  have hlog : Real.log (n : ℝ) = 8 * Real.log u := by
    rw [← hu8, Real.log_pow]; norm_num
  have hle : Real.log u ≤ u := by
    have := Real.log_le_sub_one_of_pos hu_pos
    linarith
  linarith

private theorem tilt_upper_sum (n d : Nat) (hn2M : 2000000 ≤ n) (t : ℝ)
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16) :
    let x : ℝ := Real.exp (-t)
    let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
    ((∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) / mgfSum x 0 n ≤
      1 / Real.sqrt (n : ℝ)) ∧
    ((∑ g ∈ Finset.range (2 * n + 1),
        qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
                   else (Real.exp t / 2) ^ (g - d))) ≤
      120 / (t * Real.sqrt (n : ℝ))) := by
  intro x qAtom
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  set p : ℝ := x / (1 + x)
  have hp1 : 7 / 15 ≤ p := by dsimp only [p]; rw [le_div_iff₀ (by linarith)]; linarith
  have hp2 : p ≤ 1 / 2 := by dsimp only [p]; rw [div_le_iff₀ (by linarith)]; linarith
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  have hbad_b :
      (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) / mgfSum x 0 n ≤
      1 / Real.sqrt (n : ℝ) := by
    have hlam72 : 72 / 10 ≤ 8 * lam x := by
      have hdisc : 51 ≤ (3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2 := by nlinarith
      have hsq7 : 7 ≤ Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2) := by
        exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
      have hμeq : 8 * lam x = ((3 * x + 5) + Real.sqrt ((3 * x + 5) ^ 2 - 16 * (1 - x) * (1 + x) ^ 2)) / 2 := by
        unfold lam; ring
      linarith
    have hhalf := pathWeight_half_bound (le_of_lt hx_pos) hx_le1 n 0 (by omega)
    have hmark : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) ≤
        (2 : ℝ) ^ (n / 8) * (6 : ℝ) ^ n := by
      have h1 : ((1 / 2 : ℝ) ^ (n / 8)) *
          (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
            ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) ≤ (6 : ℝ) ^ n := by
        rw [Finset.mul_sum]
        calc
          ∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
              (1 / 2 : ℝ) ^ (n / 8) * ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r
              ≤ ∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
                  ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r * ((1 / 2 : ℝ) ^ b) := by
                apply Finset.sum_le_sum; intro b hb
                rw [Finset.mul_sum]
                apply Finset.sum_le_sum; intro r _
                have hblt : b ≤ n / 8 := by have := (Finset.mem_filter.mp hb).2; omega
                have hpow : (1 / 2 : ℝ) ^ (n / 8) ≤ (1 / 2 : ℝ) ^ b :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) hblt
                have hnn := pathWeight_nonneg (le_of_lt hx_pos) n 0 b r
                nlinarith
          _ ≤ ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
                pathWeight x 0 n b r * ((1 / 2 : ℝ) ^ b) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro b _ _
              apply Finset.sum_nonneg; intro r _
              exact mul_nonneg (pathWeight_nonneg (le_of_lt hx_pos) n 0 b r) (by positivity)
          _ ≤ (6 : ℝ) ^ n := hhalf
      have h2p : (2 : ℝ) ^ (n / 8) * (1 / 2 : ℝ) ^ (n / 8) = 1 := by
        rw [← mul_pow]; norm_num
      calc
        _ = (2 : ℝ) ^ (n / 8) * ((1 / 2 : ℝ) ^ (n / 8) * _) := by rw [← mul_assoc, h2p, one_mul]
        _ ≤ (2 : ℝ) ^ (n / 8) * (6 : ℝ) ^ n := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hZlb : (1 / 4) * (72 / 10 : ℝ) ^ n ≤ mgfSum x 0 n :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hlam72 n) (by norm_num)) hZ.1
    rw [div_le_iff₀ hZpos]
    have hpow_ratio : 4 * Real.sqrt (n : ℝ) * ((2 : ℝ) ^ (n / 8) * (6 : ℝ) ^ n) ≤ (72 / 10 : ℝ) ^ n := by
      let m := n / 8
      have hm_ge : 250000 ≤ m := by omega
      have h8m : 8 * m ≤ n := Nat.mul_div_le n 8
      have hratio : (2 : ℝ) ^ m * (6 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m * (72 / 10 : ℝ) ^ n := by
        have hstep1 : (2 : ℝ) ^ m * (6 : ℝ) ^ (8 * m) ≤ (1 / 2 : ℝ) ^ m * (72 / 10 : ℝ) ^ (8 * m) := by
          rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          norm_num
        have hstep2 : (6 : ℝ) ^ (n - 8 * m) ≤ (72 / 10 : ℝ) ^ (n - 8 * m) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have hn_eq : 8 * m + (n - 8 * m) = n := Nat.add_sub_cancel' h8m
        calc
          (2 : ℝ) ^ m * (6 : ℝ) ^ n = ((2 : ℝ) ^ m * (6 : ℝ) ^ (8 * m)) * (6 : ℝ) ^ (n - 8 * m) := by
            conv_lhs => rw [← hn_eq, pow_add]
            ring
          _ ≤ ((1 / 2 : ℝ) ^ m * (72 / 10 : ℝ) ^ (8 * m)) * (72 / 10 : ℝ) ^ (n - 8 * m) :=
            mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
          _ = (1 / 2 : ℝ) ^ m * (72 / 10 : ℝ) ^ n := by
            conv_rhs => rw [← hn_eq, pow_add]
            ring
      have h4sq : 4 * Real.sqrt (n : ℝ) ≤ (2 : ℝ) ^ m := by
        have hlin : (n : ℝ) ≤ 9 * (m : ℝ) := by
          have : n ≤ 8 * m + 7 := by omega
          have : (n : ℝ) ≤ 8 * (m : ℝ) + 7 := by exact_mod_cast this
          have : (250000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
          linarith
        have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
          have : (Real.sqrt (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by rw [Real.sq_sqrt (le_of_lt hnpos)]; nlinarith
          nlinarith
        have hm2 : ∀ k : Nat, 4 * 9 * k ≤ 2 ^ k ∨ k < 12 := by
          intro k
          induction k with
          | zero => right; omega
          | succ k ih =>
            by_cases hk : k < 11
            · right; omega
            · left
              by_cases hk11 : k = 11
              · subst hk11; norm_num
              · rcases ih with h | h
                · rw [Nat.pow_succ]; omega
                · omega
        have h2m : 4 * 9 * m ≤ 2 ^ m := by
          rcases hm2 m with h | h
          · exact h
          · omega
        have h2mR : (4 * 9 * m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast h2m
        linarith
      have h2inv : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
      calc
        4 * Real.sqrt (n : ℝ) * ((2 : ℝ) ^ m * (6 : ℝ) ^ n)
            ≤ (2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ m * (72 / 10 : ℝ) ^ n) :=
          mul_le_mul h4sq hratio (by positivity) (by positivity)
        _ = ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) * (72 / 10 : ℝ) ^ n := by ring
        _ = (72 / 10 : ℝ) ^ n := by rw [h2inv, one_mul]
    calc
      ∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
          ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r
          ≤ (2 : ℝ) ^ (n / 8) * (6 : ℝ) ^ n := hmark
      _ = (1 / Real.sqrt (n : ℝ)) * ((1 / 4) * (4 * Real.sqrt (n : ℝ) * ((2 : ℝ) ^ (n / 8) * (6 : ℝ) ^ n))) := by
          field_simp
      _ ≤ (1 / Real.sqrt (n : ℝ)) * ((1 / 4) * (72 / 10 : ℝ) ^ n) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_ratio (by norm_num)) (by positivity)
      _ ≤ (1 / Real.sqrt (n : ℝ)) * mgfSum x 0 n :=
          mul_le_mul_of_nonneg_left hZlb (by positivity)
  refine ⟨hbad_b, ?_⟩
  have hqAtom_ub : ∀ g, qAtom g ≤ 40 / Real.sqrt (n : ℝ) := by
    intro g
    dsimp only [qAtom]
    have hp_def : x / (1 + x) = p := rfl
    rw [countGain_eq_pathWeight hx_pos n 0 g (by omega), hp_def]
    let Sbad := (Finset.range (n + 1)).filter (fun b => b < n / 8)
    let Sgood := (Finset.range (n + 1)).filter (fun b => ¬ (b < n / 8))
    have hdisj : Disjoint Sbad Sgood := by
      rw [Finset.disjoint_left]; intro b h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : Sbad ∪ Sgood = Finset.range (n + 1) := by
      ext b; simp only [Sbad, Sgood, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hunion, Finset.sum_union hdisj, add_div]
    have h1 : (∑ b ∈ Sbad, ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) / mgfSum x 0 n ≤
        1 / Real.sqrt (n : ℝ) := by
      calc
        _ ≤ (∑ b ∈ Sbad, ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) / mgfSum x 0 n := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hZpos)
          apply Finset.sum_le_sum; intro b _
          apply Finset.sum_le_sum; intro r _
          have hnn := pathWeight_nonneg (le_of_lt hx_pos) n 0 b r
          have hbp : (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) ≤ 1 := by
            split_ifs
            · by_cases hle : g - 2 * r ≤ b
              · calc
                  binomProb b p (g - 2 * r) ≤ ∑ k ∈ Finset.range (b + 1), binomProb b p k :=
                    Finset.single_le_sum (fun k _ => binomProb_nonneg b hp0 hp1' k)
                      (Finset.mem_range.mpr (by omega))
                  _ = 1 := binomProb_sum_one b p
              · unfold binomProb; rw [if_neg hle]; norm_num
            · norm_num
          nlinarith
        _ ≤ 1 / Real.sqrt (n : ℝ) := hbad_b
    have h2 : (∑ b ∈ Sgood, ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) / mgfSum x 0 n ≤
        39 / Real.sqrt (n : ℝ) := by
      have hsub : ∑ b ∈ Sgood, ∑ r ∈ Finset.range (n + 1),
          pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) ≤
        (39 / Real.sqrt (n : ℝ)) * mgfSum x 0 n := by
        calc
          _ ≤ ∑ b ∈ Sgood, ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r * (39 / Real.sqrt (n : ℝ)) := by
            apply Finset.sum_le_sum; intro b hb
            have hbge : n / 8 ≤ b := by have := (Finset.mem_filter.mp hb).2; omega
            have hb200k : 200000 ≤ b := by omega
            have hb_sq : Real.sqrt (n : ℝ) / 3 ≤ Real.sqrt (b : ℝ) := by
              have h9b : (n : ℝ) ≤ 9 * (b : ℝ) := by
                have h1 : (n : ℝ) ≤ 8 * (b : ℝ) + 7 := by
                  have : n ≤ 8 * b + 7 := by omega
                  exact_mod_cast this
                have h2 : (200000 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb200k
                linarith
              have hsq : (Real.sqrt (n : ℝ) / 3) ^ 2 ≤ (Real.sqrt (b : ℝ)) ^ 2 := by
                rw [div_pow, Real.sq_sqrt (le_of_lt hnpos), Real.sq_sqrt (by positivity)]
                linarith
              nlinarith [Real.sqrt_nonneg (b : ℝ)]
            have h12 : 12 / Real.sqrt (b : ℝ) ≤ 39 / Real.sqrt (n : ℝ) := by
              rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hsqpos]
              linarith
            apply Finset.sum_le_sum; intro r _
            have hnn := pathWeight_nonneg (le_of_lt hx_pos) n 0 b r
            have hbp : (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) ≤ 39 / Real.sqrt (n : ℝ) := by
              split_ifs
              · exact le_trans (binomProb_upper hb200k hp1 hp2 (g - 2 * r)) h12
              · positivity
            exact mul_le_mul_of_nonneg_left hbp hnn
          _ = (39 / Real.sqrt (n : ℝ)) * ∑ b ∈ Sgood, ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
          _ ≤ (39 / Real.sqrt (n : ℝ)) * ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro b _ _; apply Finset.sum_nonneg; intro r _; exact pathWeight_nonneg (le_of_lt hx_pos) n 0 b r
          _ = (39 / Real.sqrt (n : ℝ)) * mgfSum x 0 n := by rw [pathWeight_total_sum hx_pos 0 n (by omega)]
      rwa [div_le_iff₀ hZpos]
    have hsum12 := add_le_add h1 h2
    rw [show 1 / Real.sqrt (n : ℝ) + 39 / Real.sqrt (n : ℝ) = 40 / Real.sqrt (n : ℝ) by ring] at hsum12
    rw [hunion]
    exact hsum12
  have hstep1 :
      ∑ g ∈ Finset.range (2 * n + 1),
        qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
                   else (Real.exp t / 2) ^ (g - d)) ≤
      (40 / Real.sqrt (n : ℝ)) *
        ∑ g ∈ Finset.range (2 * n + 1),
          (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
           else (Real.exp t / 2) ^ (g - d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro g _
    have hw_nn : 0 ≤ (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ)) else (Real.exp t / 2) ^ (g - d)) := by
      split_ifs <;> positivity
    exact mul_le_mul_of_nonneg_right (hqAtom_ub g) hw_nn
  have hgeom_sum :
      ∑ g ∈ Finset.range (2 * n + 1),
        (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
         else (Real.exp t / 2) ^ (g - d)) ≤ 3 / t := by
    have hsplit : ∑ g ∈ Finset.range (2 * n + 1),
        (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ)) else (Real.exp t / 2) ^ (g - d)) =
      (∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => g ≤ d), Real.exp (-t * ((d - g : Nat) : ℝ))) +
      (∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d)), (Real.exp t / 2) ^ (g - d)) := by
      have hdisj : Disjoint ((Finset.range (2 * n + 1)).filter (fun g => g ≤ d))
          ((Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d))) := by
        rw [Finset.disjoint_left]; intro g h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hu : (Finset.range (2 * n + 1)).filter (fun g => g ≤ d) ∪
          (Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d)) = Finset.range (2 * n + 1) := by
        ext g; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      conv_lhs => rw [← hu, Finset.sum_union hdisj]
      congr 1
      · apply Finset.sum_congr rfl; intro g hg; rw [if_pos (Finset.mem_filter.mp hg).2]
      · apply Finset.sum_congr rfl; intro g hg; rw [if_neg (Finset.mem_filter.mp hg).2]
    rw [hsplit]
    have hleft : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => g ≤ d),
        Real.exp (-t * ((d - g : Nat) : ℝ)) ≤ 2 / t := by
      have hinj : Set.InjOn (fun g => d - g)
          ((Finset.range (2 * n + 1)).filter (fun g => g ≤ d)) := by
        intro g1 hg1 g2 hg2 heq
        have h1 := (Finset.mem_filter.mp hg1).2
        have h2 := (Finset.mem_filter.mp hg2).2
        dsimp only at heq
        omega
      have himg : ((Finset.range (2 * n + 1)).filter (fun g => g ≤ d)).image (fun g => d - g) ⊆
          Finset.range (d + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨g, hg, rfl⟩
        exact Finset.mem_range.mpr (by omega)
      have hrew : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => g ≤ d),
          Real.exp (-t * ((d - g : Nat) : ℝ)) ≤
          ∑ k ∈ Finset.range (d + 1), (Real.exp (-t)) ^ k := by
        have h1 : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => g ≤ d),
            Real.exp (-t * ((d - g : Nat) : ℝ)) =
          ∑ k ∈ ((Finset.range (2 * n + 1)).filter (fun g => g ≤ d)).image (fun g => d - g),
            (Real.exp (-t)) ^ k := by
          rw [Finset.sum_image hinj]
          apply Finset.sum_congr rfl; intro g _
          rw [← Real.exp_nat_mul]; ring_nf
        rw [h1]
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun k _ _ => by positivity)
      have hgeom : (1 - Real.exp (-t)) * ∑ k ∈ Finset.range (d + 1), (Real.exp (-t)) ^ k ≤ 1 := by
        have hmul := geom_sum_mul (Real.exp (-t)) (d + 1)
        have : (1 - Real.exp (-t)) * ∑ k ∈ Finset.range (d + 1), (Real.exp (-t)) ^ k =
            1 - (Real.exp (-t)) ^ (d + 1) := by linarith
        rw [this]
        have : 0 ≤ (Real.exp (-t)) ^ (d + 1) := by positivity
        linarith
      have h1me : t / 2 ≤ 1 - Real.exp (-t) := by
        have hexp_t := (abs_le.mp (exp_cubic_bound (z := -t)
          (by rw [abs_neg, abs_of_nonneg (le_of_lt ht_pos)]; linarith))).2
        rw [abs_neg, abs_of_nonneg (le_of_lt ht_pos)] at hexp_t
        nlinarith
      have hsum_nn : 0 ≤ ∑ k ∈ Finset.range (d + 1), (Real.exp (-t)) ^ k :=
        Finset.sum_nonneg (fun k _ => by positivity)
      have hle : ∑ k ∈ Finset.range (d + 1), (Real.exp (-t)) ^ k ≤ 2 / t := by
        rw [le_div_iff₀ ht_pos]; nlinarith
      linarith
    have hright : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d)),
        (Real.exp t / 2) ^ (g - d) ≤ 1 / t := by
      have hinj : Set.InjOn (fun g => g - d)
          ((Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d))) := by
        intro g1 hg1 g2 hg2 heq
        have h1 := (Finset.mem_filter.mp hg1).2
        have h2 := (Finset.mem_filter.mp hg2).2
        dsimp only at heq
        omega
      have himg : ((Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d))).image (fun g => g - d) ⊆
          Finset.range (2 * n + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨g, hg, rfl⟩
        have := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
        exact Finset.mem_range.mpr (by omega)
      have hrew : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d)),
          (Real.exp t / 2) ^ (g - d) ≤
          ∑ k ∈ Finset.range (2 * n + 1), (2 / 3 : ℝ) ^ k := by
        have h1 : ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d)),
            (Real.exp t / 2) ^ (g - d) =
          ∑ k ∈ ((Finset.range (2 * n + 1)).filter (fun g => ¬ (g ≤ d))).image (fun g => g - d),
            (Real.exp t / 2) ^ k := by
          rw [Finset.sum_image hinj]
        rw [h1]
        have hbase : Real.exp t / 2 ≤ 2 / 3 := by
          have hb := (abs_le.mp (exp_cubic_bound (z := t)
            (by rw [abs_of_nonneg (le_of_lt ht_pos)]; linarith))).2
          rw [abs_of_nonneg (le_of_lt ht_pos)] at hb
          nlinarith
        calc
          _ ≤ ∑ k ∈ Finset.range (2 * n + 1), (Real.exp t / 2) ^ k :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun k _ _ => by positivity)
          _ ≤ ∑ k ∈ Finset.range (2 * n + 1), (2 / 3 : ℝ) ^ k :=
            Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (by positivity) hbase k)
      have hgeom : ∑ k ∈ Finset.range (2 * n + 1), (2 / 3 : ℝ) ^ k ≤ 3 := by
        have hmul := geom_sum_mul (2 / 3 : ℝ) (2 * n + 1)
        have hnn : 0 ≤ (2 / 3 : ℝ) ^ (2 * n + 1) := by positivity
        linarith
      have h3t : 3 ≤ 1 / t := by rw [le_div_iff₀ ht_pos]; linarith
      linarith
    calc
      _ ≤ 2 / t + 1 / t := add_le_add hleft hright
      _ = 3 / t := by ring
  calc
    _ ≤ (40 / Real.sqrt (n : ℝ)) * (3 / t) :=
      le_trans hstep1 (mul_le_mul_of_nonneg_left hgeom_sum (by positivity))
    _ = 120 / (t * Real.sqrt (n : ℝ)) := by ring

private theorem tilt_moms (n d : Nat) (hn2M : 2000000 ≤ n) (a t : ℝ)
    (ha_def : a = (5 : ℝ) * (n : ℝ) / 8 - (d : ℝ))
    (ha_lo : 100 * Real.sqrt (n : ℝ) ≤ a)
    (ht_def : t = (64 / 27) * (a / (n : ℝ)))
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hnt3 : (n : ℝ) * t ^ 3 ≤ 1 / 1000) :
    let x : ℝ := Real.exp (-t)
    let η : ℝ := 1 / Real.sqrt (n : ℝ)
    let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
    (∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (η * ((g : ℝ) - (d : ℝ))) ≤ 32) ∧
    (∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (-η * ((g : ℝ) - (d : ℝ))) ≤ 32) := by
  intro x η qAtom
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  have hloglam := log_lam_expansion (le_of_lt ht_pos) (by linarith)
  have hη_pos : 0 < η := by dsimp only [η]; positivity
  have hη_le : η ≤ 1 / 1000 := by
    dsimp only [η]; rw [div_le_iff₀ hsqpos]
    have : (1000 : ℝ) ^ 2 ≤ (n : ℝ) := by linarith
    have := (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).mpr this
    linarith
  have htp_le : t + η ≤ 1 / 8 := by linarith
  have htm_ge : 0 ≤ t - η := by
    have : 1 / Real.sqrt (n : ℝ) ≤ (64 / 27) * (100 * Real.sqrt (n : ℝ) / (n : ℝ)) := by
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
      rw [div_le_iff₀ hsqpos]
      field_simp
      nlinarith [hsq]
    dsimp only [η]
    rw [ht_def]
    have : (64 / 27) * (100 * Real.sqrt (n : ℝ) / (n : ℝ)) ≤ (64 / 27) * (a / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right ha_lo (le_of_lt hnpos)
    linarith
  have htm_le : t - η ≤ 1 / 8 := by linarith
  constructor
  · have hx' : x * Real.exp η = Real.exp (-(t - η)) := by
      dsimp only [x]; rw [← Real.exp_add]; ring_nf
    have hsum_eq : ∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (η * ((g : ℝ) - (d : ℝ))) =
        (mgfSum (Real.exp (-(t - η))) 0 n / mgfSum x 0 n) * Real.exp (-η * (d : ℝ)) := by
      calc
        ∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (η * ((g : ℝ) - (d : ℝ)))
            = ∑ g ∈ Finset.range (2 * n + 1),
                (((countGain 0 n g : ℝ) * (Real.exp (-(t - η))) ^ g) * Real.exp (-η * (d : ℝ))) / mgfSum x 0 n := by
              apply Finset.sum_congr rfl; intro g _
              dsimp only [qAtom]
              have hexpg : (Real.exp η) ^ g = Real.exp ((g : ℝ) * η) := (Real.exp_nat_mul η g).symm
              have heq : Real.exp (η * ((g : ℝ) - (d : ℝ))) = Real.exp ((g : ℝ) * η) * Real.exp (-η * (d : ℝ)) := by
                rw [← Real.exp_add]; ring_nf
              rw [div_mul_eq_mul_div, ← hx', mul_pow, hexpg, heq]; ring
        _ = (∑ g ∈ Finset.range (2 * n + 1),
              ((countGain 0 n g : ℝ) * (Real.exp (-(t - η))) ^ g) * Real.exp (-η * (d : ℝ))) / mgfSum x 0 n :=
              (Finset.sum_div _ _ _).symm
        _ = (mgfSum (Real.exp (-(t - η))) 0 n / mgfSum x 0 n) * Real.exp (-η * (d : ℝ)) := by
              unfold mgfSum; rw [div_mul_eq_mul_div, Finset.sum_mul]
    rw [hsum_eq]
    have hx'1 : 3 / 4 ≤ Real.exp (-(t - η)) := by
      have := Real.add_one_le_exp (-(t - η)); linarith
    have hx'2 : Real.exp (-(t - η)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hZ' := (mgfSum_0_bounds hx'1 hx'2 n).2
    have hll' := (log_lam_expansion htm_ge htm_le).2
    have hll0 := hloglam.1
    have hrat : mgfSum (Real.exp (-(t - η))) 0 n / mgfSum x 0 n ≤
        16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x))) := by
      have hlp1 : 0 < lam (Real.exp (-(t - η))) := by linarith [(lam_quad hx'1 hx'2).1]
      have hlp0 : 0 < lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
      have hpow_eq : (8 * lam (Real.exp (-(t - η)))) ^ n / (8 * lam x) ^ n =
          Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x))) := by
        rw [← div_pow, mul_div_mul_left _ _ (by norm_num : (8 : ℝ) ≠ 0),
            ← Real.log_div (ne_of_gt hlp1) (ne_of_gt hlp0), Real.exp_nat_mul,
            Real.exp_log (div_pos hlp1 hlp0)]
      rw [div_le_iff₀ hZpos]
      calc
        mgfSum (Real.exp (-(t - η))) 0 n ≤ 4 * (8 * lam (Real.exp (-(t - η)))) ^ n := hZ'
        _ = 16 * ((8 * lam (Real.exp (-(t - η)))) ^ n / (8 * lam x) ^ n) * ((1 / 4) * (8 * lam x) ^ n) := by
            have hne : (8 * lam x) ^ n ≠ 0 := by positivity
            field_simp; ring
        _ ≤ 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x))) * mgfSum x 0 n := by
            rw [hpow_eq]
            exact mul_le_mul_of_nonneg_left hZ.1 (by positivity)
    have hexp_ub : (n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x)) + (-η * (d : ℝ)) ≤ 1 / 2 := by
      have hd_eq : (d : ℝ) = (5 : ℝ) * (n : ℝ) / 8 - a := by linarith
      have h1 : Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x) ≤
          (5 / 8) * η - (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t - η) ^ 3 + 20 * t ^ 3 := by
        linarith
      have h2' := mul_le_mul_of_nonneg_left h1 (le_of_lt hnpos)
      have h2 : (n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x)) + (-η * (d : ℝ)) ≤
          (n : ℝ) * ((5 / 8) * η - (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t - η) ^ 3 + 20 * t ^ 3) -
          η * ((5 : ℝ) * (n : ℝ) / 8 - a) := by
        rw [hd_eq]; linarith
      have hcancel : (n : ℝ) * ((5 / 8) * η - (27 / 64) * t * η) - η * ((5 : ℝ) * (n : ℝ) / 8 - a) = 0 := by
        rw [ht_def]; field_simp; ring
      have hη2 : (n : ℝ) * η ^ 2 = 1 := by
        dsimp only [η]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hnpos)]; field_simp
      have htm3' : (n : ℝ) * (t - η) ^ 3 ≤ (n : ℝ) * t ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htm_ge (by linarith) 3) (le_of_lt hnpos)
      have h3 : (n : ℝ) * ((5 / 8) * η - (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t - η) ^ 3 + 20 * t ^ 3) -
          η * ((5 : ℝ) * (n : ℝ) / 8 - a) =
          (27 / 128) * ((n : ℝ) * η ^ 2) + 20 * ((n : ℝ) * (t - η) ^ 3) + 20 * ((n : ℝ) * t ^ 3) := by
        linear_combination hcancel
      linarith
    calc
      (mgfSum (Real.exp (-(t - η))) 0 n / mgfSum x 0 n) * Real.exp (-η * (d : ℝ))
          ≤ 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x))) *
              Real.exp (-η * (d : ℝ)) := mul_le_mul_of_nonneg_right hrat (le_of_lt (Real.exp_pos _))
      _ = 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t - η)))) - Real.log (lam x)) + (-η * (d : ℝ))) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ 16 * Real.exp (1 / 2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_ub) (by norm_num)
      _ ≤ 32 := by
          have h := (abs_le.mp (exp_cubic_bound (z := 1 / 2) (by norm_num))).2
          norm_num at h; linarith
  · have hx' : x * Real.exp (-η) = Real.exp (-(t + η)) := by
      dsimp only [x]; rw [← Real.exp_add]; ring_nf
    have hsum_eq : ∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (-η * ((g : ℝ) - (d : ℝ))) =
        (mgfSum (Real.exp (-(t + η))) 0 n / mgfSum x 0 n) * Real.exp (η * (d : ℝ)) := by
      calc
        ∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (-η * ((g : ℝ) - (d : ℝ)))
            = ∑ g ∈ Finset.range (2 * n + 1),
                (((countGain 0 n g : ℝ) * (Real.exp (-(t + η))) ^ g) * Real.exp (η * (d : ℝ))) / mgfSum x 0 n := by
              apply Finset.sum_congr rfl; intro g _
              dsimp only [qAtom]
              have hexpg : (Real.exp (-η)) ^ g = Real.exp ((g : ℝ) * (-η)) := (Real.exp_nat_mul (-η) g).symm
              have heq : Real.exp (-η * ((g : ℝ) - (d : ℝ))) = Real.exp ((g : ℝ) * (-η)) * Real.exp (η * (d : ℝ)) := by
                rw [← Real.exp_add]; ring_nf
              rw [div_mul_eq_mul_div, ← hx', mul_pow, hexpg, heq]; ring
        _ = (∑ g ∈ Finset.range (2 * n + 1),
              ((countGain 0 n g : ℝ) * (Real.exp (-(t + η))) ^ g) * Real.exp (η * (d : ℝ))) / mgfSum x 0 n :=
              (Finset.sum_div _ _ _).symm
        _ = (mgfSum (Real.exp (-(t + η))) 0 n / mgfSum x 0 n) * Real.exp (η * (d : ℝ)) := by
              unfold mgfSum
              rw [← Finset.sum_mul]
              exact (div_mul_eq_mul_div _ _ _).symm
    rw [hsum_eq]
    have hx'1 : 3 / 4 ≤ Real.exp (-(t + η)) := by
      have := Real.add_one_le_exp (-(t + η)); linarith
    have hx'2 : Real.exp (-(t + η)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hZ' := (mgfSum_0_bounds hx'1 hx'2 n).2
    have hll' := (log_lam_expansion (by linarith) htp_le).2
    have hll0 := hloglam.1
    have hrat : mgfSum (Real.exp (-(t + η))) 0 n / mgfSum x 0 n ≤
        16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x))) := by
      have hlp1 : 0 < lam (Real.exp (-(t + η))) := by linarith [(lam_quad hx'1 hx'2).1]
      have hlp0 : 0 < lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
      have hpow_eq : (8 * lam (Real.exp (-(t + η)))) ^ n / (8 * lam x) ^ n =
          Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x))) := by
        rw [← div_pow, mul_div_mul_left _ _ (by norm_num : (8 : ℝ) ≠ 0),
            ← Real.log_div (ne_of_gt hlp1) (ne_of_gt hlp0), Real.exp_nat_mul,
            Real.exp_log (div_pos hlp1 hlp0)]
      rw [div_le_iff₀ hZpos]
      calc
        mgfSum (Real.exp (-(t + η))) 0 n ≤ 4 * (8 * lam (Real.exp (-(t + η)))) ^ n := hZ'
        _ = 16 * ((8 * lam (Real.exp (-(t + η)))) ^ n / (8 * lam x) ^ n) * ((1 / 4) * (8 * lam x) ^ n) := by
            have hne : (8 * lam x) ^ n ≠ 0 := by positivity
            field_simp; ring
        _ ≤ 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x))) * mgfSum x 0 n := by
            rw [hpow_eq]
            exact mul_le_mul_of_nonneg_left hZ.1 (by positivity)
    have hexp_ub : (n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x)) + (η * (d : ℝ)) ≤ 1 / 2 := by
      have hd_eq : (d : ℝ) = (5 : ℝ) * (n : ℝ) / 8 - a := by linarith
      have h1 : Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x) ≤
          -(5 / 8) * η + (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t + η) ^ 3 + 20 * t ^ 3 := by
        linarith
      have h2' := mul_le_mul_of_nonneg_left h1 (le_of_lt hnpos)
      have h2 : (n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x)) + (η * (d : ℝ)) ≤
          (n : ℝ) * (-(5 / 8) * η + (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t + η) ^ 3 + 20 * t ^ 3) +
          η * ((5 : ℝ) * (n : ℝ) / 8 - a) := by
        rw [hd_eq]; linarith
      have hcancel : (n : ℝ) * (-(5 / 8) * η + (27 / 64) * t * η) + η * ((5 : ℝ) * (n : ℝ) / 8 - a) = 0 := by
        rw [ht_def]; field_simp; ring
      have hη2 : (n : ℝ) * η ^ 2 = 1 := by
        dsimp only [η]; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hnpos)]; field_simp
      have htp3 : (n : ℝ) * (t + η) ^ 3 ≤ 1 / 125 := by
        have hcb : (t + η) ^ 3 ≤ 4 * t ^ 3 + 4 * η ^ 3 := by
          have : 0 ≤ (t + η) * (t - η) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
          have : 4 * t ^ 3 + 4 * η ^ 3 - (t + η) ^ 3 = 3 * ((t + η) * (t - η) ^ 2) := by ring
          linarith
        have hcb' := mul_le_mul_of_nonneg_left hcb (le_of_lt hnpos)
        have hη3 : (n : ℝ) * η ^ 3 ≤ 1 / 1000 := by
          have : (n : ℝ) * η ^ 3 = ((n : ℝ) * η ^ 2) * η := by ring
          rw [this, hη2, one_mul]; exact hη_le
        linarith [hnt3]
      have h3 : (n : ℝ) * (-(5 / 8) * η + (27 / 64) * t * η + (27 / 128) * η ^ 2 + 20 * (t + η) ^ 3 + 20 * t ^ 3) +
          η * ((5 : ℝ) * (n : ℝ) / 8 - a) =
          (27 / 128) * ((n : ℝ) * η ^ 2) + 20 * ((n : ℝ) * (t + η) ^ 3) + 20 * ((n : ℝ) * t ^ 3) := by
        linear_combination hcancel
      linarith
    calc
      (mgfSum (Real.exp (-(t + η))) 0 n / mgfSum x 0 n) * Real.exp (η * (d : ℝ))
          ≤ 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x))) *
              Real.exp (η * (d : ℝ)) := mul_le_mul_of_nonneg_right hrat (le_of_lt (Real.exp_pos _))
      _ = 16 * Real.exp ((n : ℝ) * (Real.log (lam (Real.exp (-(t + η)))) - Real.log (lam x)) + (η * (d : ℝ))) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ 16 * Real.exp (1 / 2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_ub) (by norm_num)
      _ ≤ 32 := by
          have h := (abs_le.mp (exp_cubic_bound (z := 1 / 2) (by norm_num))).2
          norm_num at h; linarith

private theorem tilt_conc (n d : Nat) (hn2M : 2000000 ≤ n) (a t : ℝ)
    (ha_def : a = (5 : ℝ) * (n : ℝ) / 8 - (d : ℝ))
    (ha_lo : 100 * Real.sqrt (n : ℝ) ≤ a)
    (ht_def : t = (64 / 27) * (a / (n : ℝ)))
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hnt3 : (n : ℝ) * t ^ 3 ≤ 1 / 1000) :
    let x : ℝ := Real.exp (-t)
    let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
    (3 : ℝ) / 4 ≤
      ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun (g : Nat) => |(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ)),
        qAtom g := by
  intro x qAtom
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  set η : ℝ := 1 / Real.sqrt (n : ℝ)
  obtain ⟨hmom_plus, hmom_minus⟩ := tilt_moms n d hn2M a t ha_def ha_lo ht_def ht_pos ht_hi hnt3
  let Sgood := (Finset.range (2 * n + 1)).filter (fun (g : Nat) => |(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ))
  let Sbad := (Finset.range (2 * n + 1)).filter (fun (g : Nat) => ¬ (|(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ)))
  have hdisj : Disjoint Sgood Sbad := by
    rw [Finset.disjoint_left]; intro g h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hu : Sgood ∪ Sbad = Finset.range (2 * n + 1) := by
    ext g; simp only [Sgood, Sbad, Finset.mem_union, Finset.mem_filter]; tauto
  have hq_nn : ∀ g, 0 ≤ qAtom g := fun g => div_nonneg (by positivity) (le_of_lt hZpos)
  have hq_sum : ∑ g ∈ Finset.range (2 * n + 1), qAtom g = 1 := by
    dsimp only [qAtom]; rw [← Finset.sum_div]; exact div_self (ne_of_gt hZpos)
  have hbad_le : Real.exp 6 * ∑ g ∈ Sbad, qAtom g ≤ 64 := by
    rw [Finset.mul_sum]
    calc
      ∑ g ∈ Sbad, Real.exp 6 * qAtom g
          ≤ ∑ g ∈ Sbad, qAtom g * (Real.exp (η * ((g : ℝ) - (d : ℝ))) + Real.exp (-η * ((g : ℝ) - (d : ℝ)))) := by
            apply Finset.sum_le_sum; intro g hg
            have hgt : 6 * Real.sqrt (n : ℝ) < |(g : ℝ) - (d : ℝ)| := by
              have := (Finset.mem_filter.mp hg).2; linarith
            have he6 : Real.exp 6 ≤ Real.exp (η * ((g : ℝ) - (d : ℝ))) + Real.exp (-η * ((g : ℝ) - (d : ℝ))) := by
              have h6 : 6 ≤ η * |(g : ℝ) - (d : ℝ)| := by
                dsimp only [η]; rw [one_div_mul_eq_div, le_div_iff₀ hsqpos]; linarith
              rcases le_or_gt 0 ((g : ℝ) - (d : ℝ)) with hpos | hneg
              · rw [abs_of_nonneg hpos] at h6
                have := Real.exp_le_exp.mpr h6
                linarith [Real.exp_pos (-η * ((g : ℝ) - (d : ℝ)))]
              · rw [abs_of_neg hneg] at h6
                have h6' : 6 ≤ -η * ((g : ℝ) - (d : ℝ)) := by linarith
                have := Real.exp_le_exp.mpr h6'
                linarith [Real.exp_pos (η * ((g : ℝ) - (d : ℝ)))]
            nlinarith [hq_nn g]
      _ ≤ ∑ g ∈ Finset.range (2 * n + 1),
            qAtom g * (Real.exp (η * ((g : ℝ) - (d : ℝ))) + Real.exp (-η * ((g : ℝ) - (d : ℝ)))) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro g _ _; exact mul_nonneg (hq_nn g) (by positivity)
      _ = (∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (η * ((g : ℝ) - (d : ℝ)))) +
          (∑ g ∈ Finset.range (2 * n + 1), qAtom g * Real.exp (-η * ((g : ℝ) - (d : ℝ)))) := by
            rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro g _; ring
      _ ≤ 32 + 32 := add_le_add hmom_plus hmom_minus
      _ = 64 := by norm_num
  have he6_ge : (256 : ℝ) ≤ Real.exp 6 := by
    have h5 : (26 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h6 : (676 / 100 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
    have h7 : (45 : ℝ) ≤ Real.exp 4 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]; nlinarith
    rw [show (6 : ℝ) = 4 + 2 by norm_num, Real.exp_add]
    nlinarith
  have hbad_ub : ∑ g ∈ Sbad, qAtom g ≤ 1 / 4 := by nlinarith
  have htot : (∑ g ∈ Sgood, qAtom g) + (∑ g ∈ Sbad, qAtom g) = 1 := by
    rw [← Finset.sum_union hdisj, hu, hq_sum]
  linarith

private theorem goodPaths_mass_lb (n d : Nat) (hn2M : 2000000 ≤ n) (t : ℝ)
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hbad_b :
      (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight (Real.exp (-t)) 0 n b r) / mgfSum (Real.exp (-t)) 0 n ≤
      1 / Real.sqrt (n : ℝ))
    (hconc_G : (3 : ℝ) / 4 ≤
      ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun (g : Nat) => |(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ)),
        ((countGain 0 n g : ℝ) * (Real.exp (-t)) ^ g) / mgfSum (Real.exp (-t)) 0 n) :
    let x : ℝ := Real.exp (-t)
    let p : ℝ := x / (1 + x)
    let GoodPaths : Finset (Nat × Nat) :=
      ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (fun br =>
        n / 8 ≤ br.1 ∧ |(2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ)| ≤ 10 * Real.sqrt (n : ℝ))
    (1 : ℝ) / 4 ≤ (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) / mgfSum x 0 n := by
  intro x p GoodPaths
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hp1 : 7 / 15 ≤ p := by dsimp only [p]; rw [le_div_iff₀ (by linarith)]; linarith
  have hp2 : p ≤ 1 / 2 := by dsimp only [p]; rw [div_le_iff₀ (by linarith)]; linarith
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
  let Gwin := (Finset.range (2 * n + 1)).filter (fun (g : Nat) => |(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ))
  have hsplit : ∑ g ∈ Gwin, qAtom g =
    (∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
      pathWeight x 0 n b r *
        ∑ g ∈ Gwin,
          (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0)) / mgfSum x 0 n := by
    dsimp only [qAtom]
    rw [← Finset.sum_div]
    congr 1
    have h1 : ∑ g ∈ Gwin, (countGain 0 n g : ℝ) * x ^ g =
      ∑ g ∈ Gwin, ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
      apply Finset.sum_congr rfl; intro g _
      exact countGain_eq_pathWeight hx_pos n 0 g (by omega)
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
  have hsum_prod :
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r *
          ∑ g ∈ Gwin, (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) ≤
      (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) +
      (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) +
      (1 / 16) * mgfSum x 0 n := by
    have hrew_prod :
        ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
          pathWeight x 0 n b r *
            ∑ g ∈ Gwin, (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
        ∑ br ∈ (Finset.range (n + 1)).product (Finset.range (n + 1)),
          pathWeight x 0 n br.1 br.2 *
            ∑ g ∈ Gwin, (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) := by
      symm; exact Finset.sum_product _ _ _
    rw [hrew_prod]
    let AllP := (Finset.range (n + 1)).product (Finset.range (n + 1))
    let SmallB := AllP.filter (fun br => br.1 < n / 8)
    have hterm_le : ∀ br ∈ AllP,
        pathWeight x 0 n br.1 br.2 *
          ∑ g ∈ Gwin, (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) ≤
        (if br ∈ GoodPaths then pathWeight x 0 n br.1 br.2 else 0) +
        (if br ∈ SmallB then pathWeight x 0 n br.1 br.2 else 0) +
        (1 / 16) * pathWeight x 0 n br.1 br.2 := by
      intro br hbr
      have hnn := pathWeight_nonneg (le_of_lt hx_pos) n 0 br.1 br.2
      have hinner_le1 : ∑ g ∈ Gwin,
          (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) ≤ 1 := by
        have hinj : Set.InjOn (fun g => g - 2 * br.2)
            (Gwin.filter (fun g => 2 * br.2 ≤ g)) := by
          intro g1 hg1 g2 hg2 heq
          have h1 := (Finset.mem_filter.mp hg1).2
          have h2 := (Finset.mem_filter.mp hg2).2
          dsimp only at heq
          omega
        have h1 : ∑ g ∈ Gwin,
            (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) =
          ∑ g ∈ Gwin.filter (fun g => 2 * br.2 ≤ g), binomProb br.1 p (g - 2 * br.2) := by
          rw [← Finset.sum_filter]
        rw [h1, ← Finset.sum_image hinj]
        let T := (Gwin.filter (fun g => 2 * br.2 ≤ g)).image (fun g => g - 2 * br.2)
        calc
          ∑ k ∈ T, binomProb br.1 p k
              = ∑ k ∈ T.filter (fun k => k ≤ br.1), binomProb br.1 p k := by
                symm; apply Finset.sum_subset (Finset.filter_subset _ _)
                intro k _ hnot
                have hgt : ¬ (k ≤ br.1) := fun h => hnot (Finset.mem_filter.mpr ⟨‹_›, h⟩)
                unfold binomProb; rw [if_neg hgt]
          _ ≤ ∑ k ∈ Finset.range (br.1 + 1), binomProb br.1 p k := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro k hk; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hk).2; omega)
                · intro k _ _; exact binomProb_nonneg br.1 hp0 hp1' k
          _ = 1 := binomProb_sum_one br.1 p
      by_cases hG : br ∈ GoodPaths
      · rw [if_pos hG]; split_ifs <;> nlinarith
      · rw [if_neg hG]
        by_cases hS : br ∈ SmallB
        · rw [if_pos hS]; nlinarith
        · rw [if_neg hS, zero_add, zero_add]
          have hbge : n / 8 ≤ br.1 := by
            by_contra hlt; exact hS (Finset.mem_filter.mpr ⟨hbr, by omega⟩)
          have hfar : 10 * Real.sqrt (n : ℝ) < |(2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ)| := by
            by_contra hle
            exact hG (Finset.mem_filter.mpr ⟨hbr, hbge, by linarith⟩)
          have hble : br.1 ≤ n := by
            have := (Finset.mem_product.mp hbr).1; have := Finset.mem_range.mp this; omega
          have hcheb_far :
              ∑ g ∈ Gwin, (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) ≤ 1 / 16 := by
            have hinj : Set.InjOn (fun g => g - 2 * br.2)
                (Gwin.filter (fun g => 2 * br.2 ≤ g)) := by
              intro g1 hg1 g2 hg2 heq
              have h1 := (Finset.mem_filter.mp hg1).2
              have h2 := (Finset.mem_filter.mp hg2).2
              dsimp only at heq
              omega
            have h1 : ∑ g ∈ Gwin,
                (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) =
              ∑ k ∈ (Gwin.filter (fun g => 2 * br.2 ≤ g)).image (fun g => g - 2 * br.2),
                binomProb br.1 p k := by
              rw [← Finset.sum_filter, ← Finset.sum_image hinj]
            rw [h1]
            let T := (Gwin.filter (fun g => 2 * br.2 ≤ g)).image (fun g => g - 2 * br.2)
            have hsub_far : T.filter (fun k => k ≤ br.1) ⊆
                (Finset.range (br.1 + 1)).filter (fun (k : Nat) => 4 * Real.sqrt (n : ℝ) ≤ |(k : ℝ) - (br.1 : ℝ) * p|) := by
              intro k hk
              have hkT := (Finset.mem_filter.mp hk).1
              have hkle := (Finset.mem_filter.mp hk).2
              rcases Finset.mem_image.mp hkT with ⟨g, hg, rfl⟩
              have hg2r := (Finset.mem_filter.mp hg).2
              have hgd := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨by omega, ?_⟩
              rw [Nat.cast_sub hg2r]; push_cast
              have htri : |(2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ)| ≤
                  |((g : ℝ) - 2 * (br.2 : ℝ)) - (br.1 : ℝ) * p| + |(g : ℝ) - (d : ℝ)| := by
                have := abs_add_le (-(g : ℝ) + 2 * (br.2 : ℝ) + (br.1 : ℝ) * p) ((g : ℝ) - (d : ℝ))
                have h2 : |-(g : ℝ) + 2 * (br.2 : ℝ) + (br.1 : ℝ) * p| =
                    |((g : ℝ) - 2 * (br.2 : ℝ)) - (br.1 : ℝ) * p| := by
                  rw [← abs_neg]; congr 1; ring
                rw [h2] at this
                have h3 : -(g : ℝ) + 2 * (br.2 : ℝ) + (br.1 : ℝ) * p + ((g : ℝ) - (d : ℝ)) =
                    (2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ) := by ring
                rw [h3] at this
                exact this
              linarith
            have hvar_ub : (16 * (n : ℝ)) * (∑ k ∈ T.filter (fun k => k ≤ br.1), binomProb br.1 p k) ≤ (n : ℝ) / 4 := by
              calc
                (16 * (n : ℝ)) * (∑ k ∈ T.filter (fun k => k ≤ br.1), binomProb br.1 p k)
                    = ∑ k ∈ T.filter (fun k => k ≤ br.1), binomProb br.1 p k * (16 * (n : ℝ)) := by
                        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
                _ ≤ ∑ k ∈ (Finset.range (br.1 + 1)).filter (fun (k : Nat) => 4 * Real.sqrt (n : ℝ) ≤ |(k : ℝ) - (br.1 : ℝ) * p|),
                      binomProb br.1 p k * ((k : ℝ) - (br.1 : ℝ) * p) ^ 2 := by
                      apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hsub_far
                        (fun k _ _ => mul_nonneg (binomProb_nonneg br.1 hp0 hp1' k) (sq_nonneg _)))
                      apply Finset.sum_le_sum; intro k hk
                      have h4 := (Finset.mem_filter.mp (hsub_far hk)).2
                      have hsq : 16 * (n : ℝ) ≤ ((k : ℝ) - (br.1 : ℝ) * p) ^ 2 := by
                        have h1 : (4 * Real.sqrt (n : ℝ)) ^ 2 ≤ (|(k : ℝ) - (br.1 : ℝ) * p|) ^ 2 := by nlinarith
                        rw [mul_pow, Real.sq_sqrt (le_of_lt hnpos), sq_abs] at h1
                        linarith
                      exact mul_le_mul_of_nonneg_left hsq (binomProb_nonneg br.1 hp0 hp1' k)
                _ ≤ ∑ k ∈ Finset.range (br.1 + 1), binomProb br.1 p k * ((k : ℝ) - (br.1 : ℝ) * p) ^ 2 := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      intro k _ _; exact mul_nonneg (binomProb_nonneg br.1 hp0 hp1' k) (sq_nonneg _)
                _ = (br.1 : ℝ) * p * (1 - p) := binomProb_var br.1 p
                _ ≤ (n : ℝ) / 4 := by
                      have hbnR : (br.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hble
                      have hq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
                      nlinarith
            have htrim : ∑ k ∈ T, binomProb br.1 p k = ∑ k ∈ T.filter (fun k => k ≤ br.1), binomProb br.1 p k := by
              symm; apply Finset.sum_subset (Finset.filter_subset _ _)
              intro k _ hnot
              have hgt : ¬ (k ≤ br.1) := fun h => hnot (Finset.mem_filter.mpr ⟨‹_›, h⟩)
              unfold binomProb; rw [if_neg hgt]
            rw [htrim]; nlinarith
          nlinarith
    calc
      ∑ br ∈ AllP, pathWeight x 0 n br.1 br.2 *
          ∑ g ∈ Gwin, (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0)
          ≤ ∑ br ∈ AllP, ((if br ∈ GoodPaths then pathWeight x 0 n br.1 br.2 else 0) +
              (if br ∈ SmallB then pathWeight x 0 n br.1 br.2 else 0) +
              (1 / 16) * pathWeight x 0 n br.1 br.2) := Finset.sum_le_sum hterm_le
      _ = (∑ br ∈ AllP, if br ∈ GoodPaths then pathWeight x 0 n br.1 br.2 else 0) +
          (∑ br ∈ AllP, if br ∈ SmallB then pathWeight x 0 n br.1 br.2 else 0) +
          (1 / 16) * (∑ br ∈ AllP, pathWeight x 0 n br.1 br.2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) +
          (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
            ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) +
          (1 / 16) * mgfSum x 0 n := by
            congr 1
            · congr 1
              · rw [← Finset.sum_filter]
                have : AllP.filter (fun br => br ∈ GoodPaths) = GoodPaths := by
                  ext br; simp only [Finset.mem_filter, GoodPaths, AllP]; tauto
                rw [this]
              · rw [← Finset.sum_filter]
                have : AllP.filter (fun br => br ∈ SmallB) =
                    ((Finset.range (n + 1)).filter (fun b => b < n / 8)) ×ˢ (Finset.range (n + 1)) := by
                  ext ⟨b, r⟩; simp [SmallB, AllP]; tauto
                rw [this, Finset.sum_product]
            · dsimp only [AllP]; rw [Finset.product_eq_sprod, Finset.sum_product, pathWeight_total_sum hx_pos 0 n (by omega)]
  have hbad_le_18 : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
      ∑ r ∈ Finset.range (n + 1), pathWeight x 0 n b r) / mgfSum x 0 n ≤ 1 / 8 := by
    have hsq8 : 8 ≤ Real.sqrt (n : ℝ) := by
      have : (8 : ℝ) ^ 2 ≤ (n : ℝ) := by linarith
      exact (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).mpr this
    have h18 : 1 / Real.sqrt (n : ℝ) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ hsqpos (by norm_num)]; linarith
    exact le_trans hbad_b h18
  change (3 : ℝ) / 4 ≤ ∑ g ∈ Gwin, qAtom g at hconc_G
  rw [hsplit] at hconc_G
  have hdiv := div_le_div_of_nonneg_right hsum_prod (le_of_lt hZpos)
  rw [add_div, add_div, mul_div_assoc, div_self (ne_of_gt hZpos), mul_one] at hdiv
  linarith

private theorem goodPaths_atom_lb (n d : Nat) (hn2M : 2000000 ≤ n) (t : ℝ)
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hGoodPaths_mass :
      let x : ℝ := Real.exp (-t)
      let p : ℝ := x / (1 + x)
      let GoodPaths : Finset (Nat × Nat) :=
        ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (fun br =>
          n / 8 ≤ br.1 ∧ |(2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ)| ≤ 10 * Real.sqrt (n : ℝ))
      (1 : ℝ) / 4 ≤ (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) / mgfSum x 0 n)
    (g : Nat) (hgd_abs : |(g : ℝ) - (d : ℝ)| ≤ Real.sqrt (n : ℝ)) :
    let x : ℝ := Real.exp (-t)
    Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)) ≤
      ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n := by
  intro x
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  set p : ℝ := x / (1 + x)
  have hp1 : 7 / 15 ≤ p := by dsimp only [p]; rw [le_div_iff₀ (by linarith)]; linarith
  have hp2 : p ≤ 1 / 2 := by dsimp only [p]; rw [div_le_iff₀ (by linarith)]; linarith
  have hp0 : 0 ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  let GoodPaths : Finset (Nat × Nat) :=
    ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (fun br =>
      n / 8 ≤ br.1 ∧ |(2 * (br.2 : ℝ) + (br.1 : ℝ) * p) - (d : ℝ)| ≤ 10 * Real.sqrt (n : ℝ))
  have hp_def : x / (1 + x) = p := rfl
  rw [countGain_eq_pathWeight hx_pos n 0 g (by omega), hp_def, le_div_iff₀ hZpos]
  have hprod_ge :
      ∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2 * (Real.exp (-7000) / (4 * Real.sqrt (n : ℝ))) ≤
      ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) := by
    have hsum_eq : ∑ b ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        pathWeight x 0 n b r * (if 2 * r ≤ g then binomProb b p (g - 2 * r) else 0) =
      ∑ br ∈ (Finset.range (n + 1)).product (Finset.range (n + 1)),
        pathWeight x 0 n br.1 br.2 * (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) := by
      symm; exact Finset.sum_product _ _ _
    rw [hsum_eq]
    calc
      ∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2 * (Real.exp (-7000) / (4 * Real.sqrt (n : ℝ)))
          ≤ ∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2 *
              (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) := by
            apply Finset.sum_le_sum; intro br hbr
            have hmemP := (Finset.mem_filter.mp hbr).1
            have hbge : n / 8 ≤ br.1 := (Finset.mem_filter.mp hbr).2.1
            have hmu := (Finset.mem_filter.mp hbr).2.2
            have hble : br.1 ≤ n := by
              have := Finset.mem_range.mp (Finset.mem_product.mp hmemP).1; omega
            have hb200k : 200000 ≤ br.1 := by omega
            have hb_sq_le : Real.sqrt (br.1 : ℝ) ≤ Real.sqrt (n : ℝ) :=
              Real.sqrt_le_sqrt (by exact_mod_cast hble)
            have hb_sq_ge : Real.sqrt (n : ℝ) / 3 ≤ Real.sqrt (br.1 : ℝ) := by
              have h9b : (n : ℝ) ≤ 9 * (br.1 : ℝ) := by
                have : n ≤ 8 * br.1 + 7 := by omega
                have h1 : (n : ℝ) ≤ 8 * (br.1 : ℝ) + 7 := by exact_mod_cast this
                have h2 : (200000 : ℝ) ≤ (br.1 : ℝ) := by exact_mod_cast hb200k
                linarith
              have hsq : (Real.sqrt (n : ℝ) / 3) ^ 2 ≤ (Real.sqrt (br.1 : ℝ)) ^ 2 := by
                rw [div_pow, Real.sq_sqrt (le_of_lt hnpos), Real.sq_sqrt (by positivity)]; linarith
              nlinarith [Real.sqrt_nonneg (br.1 : ℝ)]
            have hdiff_mu : |(g : ℝ) - (2 * (br.2 : ℝ) + (br.1 : ℝ) * p)| ≤ 11 * Real.sqrt (n : ℝ) := by
              have htri := abs_add_le ((g : ℝ) - (d : ℝ)) ((d : ℝ) - (2 * (br.2 : ℝ) + (br.1 : ℝ) * p))
              have heq : (g : ℝ) - (d : ℝ) + ((d : ℝ) - (2 * (br.2 : ℝ) + (br.1 : ℝ) * p)) =
                  (g : ℝ) - (2 * (br.2 : ℝ) + (br.1 : ℝ) * p) := by ring
              rw [heq, abs_sub_comm (d : ℝ)] at htri
              linarith
            have h2r_le_g : 2 * br.2 ≤ g := by
              have hbR : (200000 : ℝ) ≤ (br.1 : ℝ) := by exact_mod_cast hb200k
              have hsq_b : 33 * Real.sqrt (br.1 : ℝ) ≤ (br.1 : ℝ) * p := by
                have hsq : (33 * Real.sqrt (br.1 : ℝ)) ^ 2 ≤ ((br.1 : ℝ) * (7 / 15)) ^ 2 := by
                  rw [mul_pow, Real.sq_sqrt (by positivity)]; nlinarith
                have hsq1 : 33 * Real.sqrt (br.1 : ℝ) ≤ (br.1 : ℝ) * (7 / 15) := by
                  nlinarith [Real.sqrt_nonneg (br.1 : ℝ)]
                have hsq2 : (br.1 : ℝ) * (7 / 15) ≤ (br.1 : ℝ) * p :=
                  mul_le_mul_of_nonneg_left hp1 (by positivity)
                linarith
              have h1 : (br.1 : ℝ) * p - 11 * Real.sqrt (n : ℝ) ≤ (g : ℝ) - 2 * (br.2 : ℝ) := by
                rw [abs_le] at hdiff_mu; linarith
              have h2 : (2 * br.2 : ℝ) ≤ (g : ℝ) := by linarith
              exact_mod_cast h2
            rw [if_pos h2r_le_g]
            have hk_abs : |((g - 2 * br.2 : Nat) : ℝ) - (br.1 : ℝ) * p| ≤ 32 * Real.sqrt (br.1 : ℝ) := by
              rw [Nat.cast_sub h2r_le_g]; push_cast
              have heq : (g : ℝ) - 2 * (br.2 : ℝ) - (br.1 : ℝ) * p =
                  (g : ℝ) - (2 * (br.2 : ℝ) + (br.1 : ℝ) * p) := by ring
              rw [heq]
              have h11 : 11 * Real.sqrt (n : ℝ) ≤ 32 * Real.sqrt (br.1 : ℝ) := by
                have h9b : (n : ℝ) ≤ 8.1 * (br.1 : ℝ) := by
                  have : n ≤ 8 * br.1 + 7 := by omega
                  have h1 : (n : ℝ) ≤ 8 * (br.1 : ℝ) + 7 := by exact_mod_cast this
                  have h2 : (200000 : ℝ) ≤ (br.1 : ℝ) := by exact_mod_cast hb200k
                  linarith
                have hsq : (11 * Real.sqrt (n : ℝ)) ^ 2 ≤ (32 * Real.sqrt (br.1 : ℝ)) ^ 2 := by
                  rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hnpos), Real.sq_sqrt (by positivity)]
                  nlinarith
                nlinarith [Real.sqrt_nonneg (br.1 : ℝ)]
              linarith
            have hblb := binomProb_lower hb200k hp1 hp2 hk_abs
            have hsqrt_cmp : Real.exp (-7000) / (4 * Real.sqrt (n : ℝ)) ≤
                Real.exp (-7000) / (4 * Real.sqrt (br.1 : ℝ)) := by
              apply div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _))
                (by positivity) (by linarith)
            exact mul_le_mul_of_nonneg_left (le_trans hsqrt_cmp hblb)
              (pathWeight_nonneg (le_of_lt hx_pos) n 0 br.1 br.2)
      _ ≤ ∑ br ∈ (Finset.range (n + 1)).product (Finset.range (n + 1)),
            pathWeight x 0 n br.1 br.2 * (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro br _ _
            have hnn := pathWeight_nonneg (le_of_lt hx_pos) n 0 br.1 br.2
            have hbp : 0 ≤ (if 2 * br.2 ≤ g then binomProb br.1 p (g - 2 * br.2) else 0) := by
              split_ifs
              · exact binomProb_nonneg br.1 hp0 hp1' _
              · exact le_rfl
            exact mul_nonneg hnn hbp
  rw [← Finset.sum_mul] at hprod_ge
  have hgm : (1 / 4) * mgfSum x 0 n ≤ ∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2 := by
    have hmass : (1 : ℝ) / 4 ≤ (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) / mgfSum x 0 n := hGoodPaths_mass
    rwa [le_div_iff₀ hZpos] at hmass
  calc
    Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)) * mgfSum x 0 n
        = ((1 / 4) * mgfSum x 0 n) * (Real.exp (-7000) / (4 * Real.sqrt (n : ℝ))) := by ring
    _ ≤ (∑ br ∈ GoodPaths, pathWeight x 0 n br.1 br.2) * (Real.exp (-7000) / (4 * Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hgm (by positivity)
    _ ≤ _ := hprod_ge

private theorem tilt_lower_sum (n d : Nat) (hn2M : 2000000 ≤ n) (a t : ℝ)
    (ha_def : a = (5 : ℝ) * (n : ℝ) / 8 - (d : ℝ))
    (ha_lo : 100 * Real.sqrt (n : ℝ) ≤ a)
    (ht_def : t = (64 / 27) * (a / (n : ℝ)))
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hbad_b :
      (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b < n / 8),
        ∑ r ∈ Finset.range (n + 1), pathWeight (Real.exp (-t)) 0 n b r) / mgfSum (Real.exp (-t)) 0 n ≤
      1 / Real.sqrt (n : ℝ))
    (hconc_G : (3 : ℝ) / 4 ≤
      ∑ g ∈ (Finset.range (2 * n + 1)).filter (fun (g : Nat) => |(g : ℝ) - (d : ℝ)| ≤ 6 * Real.sqrt (n : ℝ)),
        ((countGain 0 n g : ℝ) * (Real.exp (-t)) ^ g) / mgfSum (Real.exp (-t)) 0 n) :
    let x : ℝ := Real.exp (-t)
    let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
    Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ))) ≤
      ∑ g ∈ Finset.range (2 * n + 1),
        qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
                   else (Real.exp t / 2) ^ (g - d)) := by
  intro x qAtom
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have ha_pos : 0 < a := by nlinarith
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  have hGoodPaths_mass := goodPaths_mass_lb n d hn2M t ht_pos ht_hi hbad_b hconc_G
  let K : Nat := Nat.floor (1 / t)
  have hK_le : (K : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have hK_gt : 1 / t - 1 < (K : ℝ) := by have := Nat.lt_floor_add_one (1 / t); linarith
  have hK_le_sq : (K : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h1 : 1 / t ≤ Real.sqrt (n : ℝ) := by
      rw [div_le_iff₀ ht_pos, ht_def]
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
      field_simp
      nlinarith [ha_lo, hsq]
    linarith
  have hd_ge_K : K ≤ d := by
    have hd_lo : (n : ℝ) / 2 ≤ (d : ℝ) := by
      have ha_n : a ≤ (n : ℝ) / 8 := by
        have h1 : (64 / 27 : ℝ) * a / (n : ℝ) ≤ 1 / 16 := by
          have : (64 / 27 : ℝ) * a / (n : ℝ) = t := by rw [ht_def]; ring
          linarith
        rw [div_le_iff₀ hnpos] at h1
        linarith
      linarith
    have hsq_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 2 := by
      have : (Real.sqrt (n : ℝ)) ^ 2 ≤ ((n : ℝ) / 2) ^ 2 := by rw [Real.sq_sqrt (le_of_lt hnpos)]; nlinarith
      nlinarith
    have : (K : ℝ) ≤ (d : ℝ) := by linarith
    exact_mod_cast this
  have hd_le_2n : d ≤ 2 * n := by
    have : (d : ℝ) ≤ (5 : ℝ) * (n : ℝ) / 8 := by linarith
    have : (d : ℝ) ≤ (2 * n : Nat) := by push_cast; linarith
    exact_mod_cast this
  let W := Finset.Icc (d - K) d
  have hW_sub : W ⊆ Finset.range (2 * n + 1) := by
    intro g hg
    have := (Finset.mem_Icc.mp hg).2
    exact Finset.mem_range.mpr (by omega)
  have hstep1 : Real.exp (-1) * ∑ g ∈ W, qAtom g ≤
      ∑ g ∈ Finset.range (2 * n + 1),
        qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
                   else (Real.exp t / 2) ^ (g - d)) := by
    calc
      Real.exp (-1) * ∑ g ∈ W, qAtom g
          = ∑ g ∈ W, qAtom g * Real.exp (-1) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
      _ ≤ ∑ g ∈ W, qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
            else (Real.exp t / 2) ^ (g - d)) := by
            apply Finset.sum_le_sum; intro g hg
            have hgd : g ≤ d := (Finset.mem_Icc.mp hg).2
            have hdg : d - g ≤ K := by have := (Finset.mem_Icc.mp hg).1; omega
            rw [if_pos hgd]
            have hexp_ge : Real.exp (-1) ≤ Real.exp (-t * ((d - g : Nat) : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hdgR : ((d - g : Nat) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdg
              have htk : t * (K : ℝ) ≤ 1 := by
                have := mul_le_mul_of_nonneg_left hK_le (le_of_lt ht_pos)
                rwa [mul_div_cancel₀ _ (ne_of_gt ht_pos)] at this
              nlinarith
            have hqnn : 0 ≤ qAtom g := div_nonneg (by positivity) (le_of_lt hZpos)
            exact mul_le_mul_of_nonneg_left hexp_ge hqnn
      _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hW_sub
            intro g _ _
            have hqnn : 0 ≤ qAtom g := div_nonneg (by positivity) (le_of_lt hZpos)
            have hwnn : 0 ≤ (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ)) else (Real.exp t / 2) ^ (g - d)) := by
              split_ifs <;> positivity
            exact mul_nonneg hqnn hwnn
  have hq_atom_lb : ∀ g ∈ W,
      Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)) ≤ qAtom g := by
    intro g hg
    have hgd_abs : |(g : ℝ) - (d : ℝ)| ≤ Real.sqrt (n : ℝ) := by
      have h1 : d - K ≤ g := (Finset.mem_Icc.mp hg).1
      have h2 : g ≤ d := (Finset.mem_Icc.mp hg).2
      have h1R : (d : ℝ) - (K : ℝ) ≤ (g : ℝ) := by
        have : ((d - K : Nat) : ℝ) ≤ (g : ℝ) := by exact_mod_cast h1
        rwa [Nat.cast_sub hd_ge_K] at this
      have h2R : (g : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
      rw [abs_le]; constructor <;> linarith
    exact goodPaths_atom_lb n d hn2M t ht_pos ht_hi hGoodPaths_mass g hgd_abs
  have hW_card : 1 / t ≤ (W.card : ℝ) := by
    dsimp only [W]
    rw [Nat.card_Icc, show d + 1 - (d - K) = K + 1 by omega]
    push_cast; linarith
  have hsum_W : (1 / t) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ))) ≤ ∑ g ∈ W, qAtom g := by
    calc
      (1 / t) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)))
          ≤ (W.card : ℝ) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hW_card (by positivity)
      _ = ∑ _g ∈ W, Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)) := by simp
      _ ≤ ∑ g ∈ W, qAtom g := Finset.sum_le_sum hq_atom_lb
  have hexp_comb : Real.exp (-1) * ((1 / t) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)))) =
      Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ))) := by
    have : Real.exp (-1) * Real.exp (-7000) = Real.exp (-7001) := by
      rw [← Real.exp_add]; norm_num
    calc
      Real.exp (-1) * ((1 / t) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ))))
          = (Real.exp (-1) * Real.exp (-7000)) / (16 * (t * Real.sqrt (n : ℝ))) := by ring
      _ = Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ))) := by rw [this]
  calc
    Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ)))
        = Real.exp (-1) * ((1 / t) * (Real.exp (-7000) / (16 * Real.sqrt (n : ℝ)))) := hexp_comb.symm
    _ ≤ Real.exp (-1) * ∑ g ∈ W, qAtom g :=
          mul_le_mul_of_nonneg_left hsum_W (le_of_lt (Real.exp_pos _))
    _ ≤ _ := hstep1

private theorem price_tilt_eq (n d : Nat) (t : ℝ) (hZpos : 0 < mgfSum (Real.exp (-t)) 0 n) :
    let x : ℝ := Real.exp (-t)
    let qAtom : Nat → ℝ := fun g => ((countGain 0 n g : ℝ) * x ^ g) / mgfSum x 0 n
    (price n d : ℝ) / (2 : ℝ) ^ (5 * n) =
      ((mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))) *
      (∑ g ∈ Finset.range (2 * n + 1),
        qAtom g * (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
                   else (Real.exp t / 2) ^ (g - d))) := by
  intro x qAtom
  rw [price_eq_sum_countGain n d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  dsimp only [qAtom]
  have hxpow : x ^ g = Real.exp (-t * (g : ℝ)) := by
    dsimp only [x]; rw [← Real.exp_nat_mul]; ring_nf
  have hZne : mgfSum x 0 n ≠ 0 := ne_of_gt hZpos
  have h8ne : (8 : ℝ) ^ n ≠ 0 := by positivity
  by_cases hgd : g ≤ d
  · rw [if_pos hgd, show g - d = 0 by omega, pow_zero, inv_one, mul_one]
    have hsub : ((d - g : Nat) : ℝ) = (d : ℝ) - (g : ℝ) := Nat.cast_sub hgd
    rw [hsub, hxpow]
    have hexp1 : Real.exp (t * (d : ℝ)) * (Real.exp (-t * (g : ℝ)) * Real.exp (-t * ((d : ℝ) - (g : ℝ)))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have : t * (d : ℝ) + (-t * (g : ℝ) + -t * ((d : ℝ) - (g : ℝ))) = 0 := by ring
      rw [this, Real.exp_zero]
    field_simp
    calc
      (countGain 0 n g : ℝ) = (countGain 0 n g : ℝ) * 1 := by ring
      _ = (countGain 0 n g : ℝ) * (Real.exp (t * (d : ℝ)) *
            (Real.exp (-t * (g : ℝ)) * Real.exp (-t * ((d : ℝ) - (g : ℝ))))) := by rw [hexp1]
      _ = _ := by ring
  · rw [if_neg hgd]
    have hsub : ((g - d : Nat) : ℝ) = (g : ℝ) - (d : ℝ) := Nat.cast_sub (by omega)
    have hexpgd : (Real.exp t) ^ (g - d) = Real.exp (((g : ℝ) - (d : ℝ)) * t) := by
      rw [← Real.exp_nat_mul, hsub]
    rw [div_pow, hexpgd, hxpow]
    have hexp1 : Real.exp (t * (d : ℝ)) * (Real.exp (-t * (g : ℝ)) * Real.exp (((g : ℝ) - (d : ℝ)) * t)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have : t * (d : ℝ) + (-t * (g : ℝ) + ((g : ℝ) - (d : ℝ)) * t) = 0 := by ring
      rw [this, Real.exp_zero]
    have h2ne : (2 : ℝ) ^ (g - d) ≠ 0 := by positivity
    field_simp
    calc
      (countGain 0 n g : ℝ) = (countGain 0 n g : ℝ) * 1 := by ring
      _ = (countGain 0 n g : ℝ) * (Real.exp (t * (d : ℝ)) *
            (Real.exp (-t * (g : ℝ)) * Real.exp (((g : ℝ) - (d : ℝ)) * t))) := by rw [hexp1]
      _ = _ := by ring

private theorem main_exp_factor (n d : Nat) (hnpos : (0 : ℝ) < (n : ℝ)) (a t : ℝ)
    (ha_def : a = (5 : ℝ) * (n : ℝ) / 8 - (d : ℝ))
    (ht_def : t = (64 / 27) * (a / (n : ℝ)))
    (ht_pos : 0 < t) (ht_hi : t ≤ 1 / 16)
    (hnt3 : (n : ℝ) * t ^ 3 ≤ 1 / 1000) :
    let x : ℝ := Real.exp (-t)
    (1 / 4) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1) ≤
      ((mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))) ∧
    ((mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))) ≤
      4 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) + 1) := by
  intro x
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hloglam := log_lam_expansion (le_of_lt ht_pos) (by linarith)
  have hd_eq : (d : ℝ) = (5 : ℝ) * (n : ℝ) / 8 - a := by linarith
  have hquad_id : (n : ℝ) * (-(5 / 8) * t + (27 / 128) * t ^ 2) + t * (d : ℝ) =
      -(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) := by
    rw [hd_eq, ht_def]; field_simp; ring
  have hlam_pow : (lam x) ^ n = Real.exp ((n : ℝ) * Real.log (lam x)) := by
    have hlp : 0 < lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    rw [Real.exp_nat_mul, Real.exp_log hlp]
  have h8div : (8 * lam x) ^ n / (8 : ℝ) ^ n = (lam x) ^ n := by
    rw [mul_pow, mul_div_cancel_left₀ _ (by positivity)]
  have hZ_div_lo : (1 / 4) * (lam x) ^ n ≤ mgfSum x 0 n / (8 : ℝ) ^ n := by
    rw [← h8div]
    calc
      (1 / 4) * ((8 * lam x) ^ n / (8 : ℝ) ^ n) = ((1 / 4) * (8 * lam x) ^ n) / (8 : ℝ) ^ n := by ring
      _ ≤ mgfSum x 0 n / (8 : ℝ) ^ n := div_le_div_of_nonneg_right hZ.1 (by positivity)
  have hZ_div_hi : mgfSum x 0 n / (8 : ℝ) ^ n ≤ 4 * (lam x) ^ n := by
    rw [← h8div]
    calc
      mgfSum x 0 n / (8 : ℝ) ^ n ≤ (4 * (8 * lam x) ^ n) / (8 : ℝ) ^ n :=
          div_le_div_of_nonneg_right hZ.2 (by positivity)
      _ = 4 * ((8 * lam x) ^ n / (8 : ℝ) ^ n) := by ring
  have hlo_e : Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1) ≤ (lam x) ^ n * Real.exp (t * (d : ℝ)) := by
    rw [hlam_pow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) * (-(5 / 8) * t + (27 / 128) * t ^ 2 - 20 * t ^ 3) ≤ (n : ℝ) * Real.log (lam x) :=
      mul_le_mul_of_nonneg_left hloglam.1 (le_of_lt hnpos)
    linarith
  have hhi_e : (lam x) ^ n * Real.exp (t * (d : ℝ)) ≤ Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) + 1) := by
    rw [hlam_pow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) * Real.log (lam x) ≤ (n : ℝ) * (-(5 / 8) * t + (27 / 128) * t ^ 2 + 20 * t ^ 3) :=
      mul_le_mul_of_nonneg_left hloglam.2 (le_of_lt hnpos)
    linarith
  constructor
  · calc
      (1 / 4 : ℝ) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1)
          ≤ (1 / 4 : ℝ) * ((lam x) ^ n * Real.exp (t * (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hlo_e (by norm_num)
      _ = ((1 / 4) * (lam x) ^ n) * Real.exp (t * (d : ℝ)) := by ring
      _ ≤ (mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hZ_div_lo (le_of_lt (Real.exp_pos _))
  · calc
      (mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))
          ≤ (4 * (lam x) ^ n) * Real.exp (t * (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hZ_div_hi (le_of_lt (Real.exp_pos _))
      _ = 4 * ((lam x) ^ n * Real.exp (t * (d : ℝ))) := by ring
      _ ≤ 4 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_left hhi_e (by norm_num)

private theorem main_log_bounds (n d : Nat) (hnpos : (0 : ℝ) < (n : ℝ))
    (a t : ℝ) (ha_pos : 0 < a) (ht_pos : 0 < t)
    (ht_def : t = (64 / 27) * (a / (n : ℝ)))
    (hZpos : 0 < mgfSum (Real.exp (-t)) 0 n)
    (hexp_main :
      (1 / 4) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1) ≤
        ((mgfSum (Real.exp (-t)) 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))) ∧
      ((mgfSum (Real.exp (-t)) 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ))) ≤
        4 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) + 1))
    (hS_ub :
      (∑ g ∈ Finset.range (2 * n + 1),
        (((countGain 0 n g : ℝ) * (Real.exp (-t)) ^ g) / mgfSum (Real.exp (-t)) 0 n) *
          (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
           else (Real.exp t / 2) ^ (g - d))) ≤
      120 / (t * Real.sqrt (n : ℝ)))
    (hS_lb :
      Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ))) ≤
      ∑ g ∈ Finset.range (2 * n + 1),
        (((countGain 0 n g : ℝ) * (Real.exp (-t)) ^ g) / mgfSum (Real.exp (-t)) 0 n) *
          (if g ≤ d then Real.exp (-t * ((d - g : Nat) : ℝ))
           else (Real.exp t / 2) ^ (g - d))) :
    |Real.log ((price n d : ℝ) / (2 : ℝ) ^ (5 * n)) +
      (32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) +
      Real.log (a / Real.sqrt (n : ℝ))| ≤ 8000 := by
  set x : ℝ := Real.exp (-t)
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hP_tilt := price_tilt_eq n d t hZpos
  have htsq : t * Real.sqrt (n : ℝ) = (64 / 27) * (a / Real.sqrt (n : ℝ)) := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
    have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqpos
    have h1 : (a / (n : ℝ)) * Real.sqrt (n : ℝ) = a / Real.sqrt (n : ℝ) := by
      rw [eq_div_iff hne, mul_assoc, hsq, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    rw [ht_def]; linarith
  have hP_pos : 0 < (price n d : ℝ) / (2 : ℝ) ^ (5 * n) := by
    rw [hP_tilt]
    have h1 : 0 < (mgfSum x 0 n / (8 : ℝ) ^ n) * Real.exp (t * (d : ℝ)) := by positivity
    have h2 : 0 < Real.exp (-7001) / (16 * (t * Real.sqrt (n : ℝ))) := by positivity
    exact mul_pos h1 (lt_of_lt_of_le h2 hS_lb)
  have hP_lo : Real.exp (-8000) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) ≤
      (price n d : ℝ) / (2 : ℝ) ^ (5 * n) := by
    rw [hP_tilt]
    have hmul := mul_le_mul hexp_main.1 hS_lb (by positivity) (by positivity)
    rw [htsq] at hmul
    have hc : Real.exp (-8000) ≤ (1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27))) := by
      have h1 : (1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27))) =
          Real.exp (-7002) / (64 * (64 / 27)) := by
        have : Real.exp (-1) * Real.exp (-7001) = Real.exp (-7002) := by rw [← Real.exp_add]; norm_num
        calc
          (1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27)))
              = (Real.exp (-1) * Real.exp (-7001)) / (64 * (64 / 27)) := by ring
          _ = Real.exp (-7002) / (64 * (64 / 27)) := by rw [this]
      rw [h1, le_div_iff₀ (by norm_num)]
      have h998 : (64 * (64 / 27 : ℝ)) ≤ Real.exp 998 := by
        have := Real.add_one_le_exp (998 : ℝ)
        linarith
      calc
        Real.exp (-8000) * (64 * (64 / 27))
            ≤ Real.exp (-8000) * Real.exp 998 := mul_le_mul_of_nonneg_left h998 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-7002) := by rw [← Real.exp_add]; norm_num
    have hrew : (1 / 4) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1) *
        (Real.exp (-7001) / (16 * ((64 / 27) * (a / Real.sqrt (n : ℝ))))) =
        ((1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27)))) *
          Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by
      have : Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - 1) =
          Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) * Real.exp (-1) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [hrew] at hmul
    have hpos_rhs : 0 ≤ Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by positivity
    calc
      Real.exp (-8000) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))
          = Real.exp (-8000) * (Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) := by ring
      _ ≤ ((1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27)))) *
            (Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hc hpos_rhs
      _ = ((1 / 4) * Real.exp (-1) * (Real.exp (-7001) / (16 * (64 / 27)))) *
            Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by ring
      _ ≤ _ := hmul
  have hP_hi : (price n d : ℝ) / (2 : ℝ) ^ (5 * n) ≤
      Real.exp 8000 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by
    rw [hP_tilt]
    have hmul := mul_le_mul hexp_main.2 hS_ub
      (Finset.sum_nonneg (fun g _ => mul_nonneg (div_nonneg (by positivity) (le_of_lt hZpos))
        (by split_ifs <;> positivity))) (by positivity)
    rw [htsq] at hmul
    have hc : 4 * Real.exp 1 * (120 / (64 / 27)) ≤ Real.exp 8000 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h8k : (8000 : ℝ) ≤ Real.exp 8000 := by linarith [Real.add_one_le_exp (8000 : ℝ)]
      linarith
    have hrew : 4 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) + 1) *
        (120 / ((64 / 27) * (a / Real.sqrt (n : ℝ)))) =
        (4 * Real.exp 1 * (120 / (64 / 27))) *
          Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by
      rw [Real.exp_add]; ring
    rw [hrew] at hmul
    have hpos_rhs : 0 ≤ Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by positivity
    calc
      _ ≤ (4 * Real.exp 1 * (120 / (64 / 27))) *
            Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := hmul
      _ = (4 * Real.exp 1 * (120 / (64 / 27))) *
            (Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) := by ring
      _ ≤ Real.exp 8000 * (Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hc hpos_rhs
      _ = Real.exp 8000 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ)) := by ring
  have hlog_rhs_lo : Real.log (Real.exp (-8000) * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) =
      -8000 - (32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - Real.log (a / Real.sqrt (n : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_exp, Real.log_exp]; ring
  have hlog_lo : -8000 - (32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - Real.log (a / Real.sqrt (n : ℝ)) ≤
      Real.log ((price n d : ℝ) / (2 : ℝ) ^ (5 * n)) := by
    rw [← hlog_rhs_lo]
    exact Real.log_le_log (by positivity) hP_lo
  have hlog_rhs_hi : Real.log (Real.exp 8000 * Real.exp (-(32 : ℝ) * a ^ 2 / (27 * (n : ℝ))) / (a / Real.sqrt (n : ℝ))) =
      8000 - (32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - Real.log (a / Real.sqrt (n : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_exp, Real.log_exp]; ring
  have hlog_hi : Real.log ((price n d : ℝ) / (2 : ℝ) ^ (5 * n)) ≤
      8000 - (32 : ℝ) * a ^ 2 / (27 * (n : ℝ)) - Real.log (a / Real.sqrt (n : ℝ)) := by
    rw [← hlog_rhs_hi]
    exact Real.log_le_log hP_pos hP_hi
  rw [abs_le]
  constructor <;> linarith

private theorem main (depth : Nat → Nat)
    (h_tendsto : Filter.Tendsto
      (fun time : Nat => ((5 : ℝ) * (time : ℝ) / 8 - (depth time : ℝ)) / Real.sqrt (time : ℝ))
      Filter.atTop Filter.atTop)
    (h_upper : ∃ (C : ℝ) (start : Nat), 0 < C ∧ ∀ time : Nat, start ≤ time →
      (5 : ℝ) * (time : ℝ) / 8 - (depth time : ℝ) ≤
        C * Real.sqrt ((time : ℝ) * Real.log (time : ℝ))) :
    ∃ (bound : ℝ) (start : Nat), 0 < bound ∧ ∀ time : Nat, start ≤ time →
      |Real.log ((price time (depth time) : ℝ) / (2 : ℝ) ^ (5 * time)) +
        (32 : ℝ) * ((5 : ℝ) * (time : ℝ) / 8 - (depth time : ℝ)) ^ 2 / (27 * (time : ℝ)) +
        Real.log (((5 : ℝ) * (time : ℝ) / 8 - (depth time : ℝ)) / Real.sqrt (time : ℝ))| ≤ bound := by
  rcases h_upper with ⟨C, N0, hCpos, hC⟩
  have hev : ∀ᶠ (n : Nat) in Filter.atTop,
      (100 : ℝ) ≤ ((5 : ℝ) * (n : ℝ) / 8 - (depth n : ℝ)) / Real.sqrt (n : ℝ) :=
    Filter.tendsto_atTop.mp h_tendsto 100
  rcases Filter.eventually_atTop.mp hev with ⟨N1, hN1⟩
  let U0 : Nat := Nat.ceil (10000 * (C + 1) ^ 6 + 10000)
  let Nstart : Nat := max (max N0 N1) (max (U0 ^ 8) 2000000)
  refine ⟨8000, Nstart, by norm_num, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnU : U0 ^ 8 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2M : 2000000 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (2000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2M
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  set d := depth n
  set a : ℝ := (5 : ℝ) * (n : ℝ) / 8 - (d : ℝ)
  have ha_lo : 100 * Real.sqrt (n : ℝ) ≤ a := by
    have h := hN1 n hn1
    rwa [le_div_iff₀ hsqpos] at h
  have ha_pos : 0 < a := by nlinarith
  have ha_hi : a ≤ C * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := hC n hn0
  set u := Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ)))
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnpos))
  have hu8 : u ^ 8 = (n : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (u ^ 2) ^ 2 = Real.sqrt (n : ℝ) := by rw [h1]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : ((u ^ 2) ^ 2) ^ 2 = (n : ℝ) := by rw [h2]; exact Real.sq_sqrt (le_of_lt hnpos)
    calc u ^ 8 = ((u ^ 2) ^ 2) ^ 2 := by ring
    _ = (n : ℝ) := h3
  have hu4 : u ^ 4 = Real.sqrt (n : ℝ) := by
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (u ^ 2) ^ 2 = Real.sqrt (n : ℝ) := by rw [h1]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
    _ = Real.sqrt (n : ℝ) := h2
  have hu_ge : 10000 * (C + 1) ^ 6 + 10000 ≤ u := by
    have hU0 : 10000 * (C + 1) ^ 6 + 10000 ≤ (U0 : ℝ) := Nat.le_ceil _
    have hU8 : ((U0 : ℝ)) ^ 8 ≤ u ^ 8 := by
      rw [hu8]; exact_mod_cast hnU
    by_contra hlt
    push_neg at hlt
    have hlt' : u < (U0 : ℝ) := by linarith
    have : u ^ 8 < ((U0 : ℝ)) ^ 8 := pow_lt_pow_left₀ hlt' (le_of_lt hu_pos) (by omega)
    linarith
  have hlog_le : Real.log (n : ℝ) ≤ 8 * u := log_le_eight_root8 (by omega)
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have ha_sq : a ^ 2 ≤ 8 * C ^ 2 * u ^ 9 := by
    have h1 : a ^ 2 ≤ (C * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 := by
      nlinarith
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h1
    have h2 : C ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) ≤ C ^ 2 * ((n : ℝ) * (8 * u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_le (le_of_lt hnpos)) (sq_nonneg C)
    have h3 : C ^ 2 * ((n : ℝ) * (8 * u)) = 8 * C ^ 2 * u ^ 9 := by rw [← hu8]; ring
    linarith
  have ha_cube_bound : a ^ 3 / (n : ℝ) ^ 2 ≤ 1 / 100000 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (a ^ 3) ^ 2 ≤ ((1 / 100000 : ℝ) * (n : ℝ) ^ 2) ^ 2 := by
      have ha6 : a ^ 6 ≤ (8 * C ^ 2 * u ^ 9) ^ 3 := by
        calc
          a ^ 6 = (a ^ 2) ^ 3 := by ring
          _ ≤ (8 * C ^ 2 * u ^ 9) ^ 3 := pow_le_pow_left₀ (sq_nonneg a) ha_sq 3
      have hC6 : C ^ 6 ≤ (C + 1) ^ 6 := pow_le_pow_left₀ (le_of_lt hCpos) (by linarith) 6
      have h512 : 512 * C ^ 6 ≤ u / 10 := by nlinarith
      have h1000 : (512 * C ^ 6) * 10000000000 ≤ u ^ 5 := by
        have h1 : 10000 ≤ u := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ C + 1) 6]
        have hu4_ge : (10000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
        have : (512 * C ^ 6) * 10000000000 ≤ (u / 10) * u ^ 4 := by nlinarith
        nlinarith
      calc
        (a ^ 3) ^ 2 = a ^ 6 := by ring
        _ ≤ (8 * C ^ 2 * u ^ 9) ^ 3 := ha6
        _ = (512 * C ^ 6) * u ^ 27 := by ring
        _ ≤ ((1 / 10000000000 : ℝ) * u ^ 5) * u ^ 27 := by
              apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt hu_pos) 27)
        _ = ((1 / 100000 : ℝ) * (u ^ 8) ^ 2) ^ 2 := by ring
        _ = ((1 / 100000 : ℝ) * (n : ℝ) ^ 2) ^ 2 := by rw [hu8]
    nlinarith [pow_pos ha_pos 3]
  set t : ℝ := (64 / 27) * (a / (n : ℝ))
  have ht_pos : 0 < t := by dsimp only [t]; positivity
  have ht_hi : t ≤ 1 / 16 := by
    dsimp only [t]
    have ha_n : a / (n : ℝ) ≤ 1 / 100 := by
      rw [div_le_iff₀ hnpos]
      have hsq : a ^ 2 ≤ ((1 / 100 : ℝ) * (n : ℝ)) ^ 2 := by
        have h1 : 10000 * (C + 1) ^ 6 ≤ u := by linarith
        have hC2 : C ^ 2 ≤ (C + 1) ^ 6 := by
          have : 1 ≤ C + 1 := by linarith
          calc C ^ 2 ≤ (C + 1) ^ 2 := pow_le_pow_left₀ (le_of_lt hCpos) (by linarith) 2
          _ ≤ (C + 1) ^ 6 := pow_le_pow_right₀ this (by omega)
        have hu7 : 80000 * C ^ 2 ≤ u ^ 7 := by
          have hu1 : 10000 ≤ u := by linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ C + 1) 6]
          have hu6 : 10000 ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ (by norm_num) hu1 6
          nlinarith
        calc
          a ^ 2 ≤ 8 * C ^ 2 * u ^ 9 := ha_sq
          _ ≤ ((1 / 10000 : ℝ) * u ^ 7) * u ^ 9 := by
                apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt hu_pos) 9)
          _ = ((1 / 100 : ℝ) * u ^ 8) ^ 2 := by ring
          _ = ((1 / 100 : ℝ) * (n : ℝ)) ^ 2 := by rw [hu8]
      nlinarith
    linarith
  have hnt3 : (n : ℝ) * t ^ 3 ≤ 1 / 1000 := by
    dsimp only [t]
    have : (n : ℝ) * ((64 / 27) * (a / (n : ℝ))) ^ 3 = (64 / 27) ^ 3 * (a ^ 3 / (n : ℝ) ^ 2) := by
      field_simp
    rw [this]
    have h64 : (64 / 27 : ℝ) ^ 3 ≤ 20 := by norm_num
    nlinarith
  set x : ℝ := Real.exp (-t)
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx_ge : 7 / 8 ≤ x := by
    have := Real.add_one_le_exp (-t)
    dsimp only [x]; linarith
  have hZ := mgfSum_0_bounds (x := x) (by linarith) hx_le1 n
  have hZpos : 0 < mgfSum x 0 n := by
    have hlam_pos : 0 < 8 * lam x := by linarith [(lam_quad (by linarith : 3 / 4 ≤ x) hx_le1).1]
    have : 0 < (1 / 4) * (8 * lam x) ^ n := by positivity
    linarith [hZ.1]
  have hexp_main := main_exp_factor n d hnpos a t rfl rfl ht_pos ht_hi hnt3
  obtain ⟨hbad_b, hS_ub⟩ := tilt_upper_sum n d hn2M t ht_pos ht_hi
  have hconc_G := tilt_conc n d hn2M a t rfl ha_lo rfl ht_pos ht_hi hnt3
  have hS_lb := tilt_lower_sum n d hn2M a t rfl ha_lo rfl ht_pos ht_hi hbad_b hconc_G
  exact main_log_bounds n d hnpos a t ha_pos ht_pos rfl hZpos hexp_main hS_ub hS_lb

private theorem cast_list_sum (l : List Nat) :
    ((l.sum : Nat) : ℝ) = (l.map (fun k : Nat => (k : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

private theorem price_eq_real (n d : Nat) :
    (price n d : ℝ) = ((List.range (8 ^ n)).map (fun codeWord =>
      (2 : ℝ) ^ (2 * n - ((summary codeWord n).2 - d)))).sum := by
  unfold price
  rw [cast_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left (fun codeWord _ => by simp)

end PEqualNP.Outside.L_meta_25556_aux

theorem PEqualNP.Outside.L_meta_25556 :
let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let price := fun (n depth : Nat) =>
    ((List.range (8 ^ n)).map (fun codeWord =>
      2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum
∀ depth : Nat → Nat,
  let shortfall := fun time : Nat => (5 : ℝ) * (time : ℝ) / 8 - (depth time : ℝ)
  Filter.Tendsto (fun time : Nat => shortfall time / Real.sqrt (time : ℝ))
    Filter.atTop Filter.atTop →
  (∃ (C : ℝ) (start : Nat), 0 < C ∧ ∀ time : Nat, start ≤ time →
    shortfall time ≤ C * Real.sqrt ((time : ℝ) * Real.log (time : ℝ))) →
  ∃ (bound : ℝ) (start : Nat), 0 < bound ∧ ∀ time : Nat, start ≤ time →
    |Real.log ((price time (depth time) : ℝ) / (2 : ℝ) ^ (5 * time)) +
      (32 : ℝ) * (shortfall time) ^ 2 / (27 * (time : ℝ)) +
      Real.log (shortfall time / Real.sqrt (time : ℝ))| ≤ bound := by
  intro move summary price depth shortfall h1 h2
  rcases PEqualNP.Outside.L_meta_25556_aux.main depth h1 h2 with ⟨B, N, hB, h⟩
  refine ⟨B, N, hB, fun t ht => ?_⟩
  have hpeq : (PEqualNP.Outside.L_meta_25556_aux.price t (depth t) : ℝ) = price t (depth t) :=
    PEqualNP.Outside.L_meta_25556_aux.price_eq_real t (depth t)
  simpa only [← hpeq] using h t ht
