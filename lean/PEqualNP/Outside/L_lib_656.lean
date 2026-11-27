import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_656_aux

def repeatedDigit (width digit count : ℕ) : ℕ :=
  digit * ∑ j ∈ Finset.range count, (2 ^ width) ^ j

theorem repeated_digit_succ (width digit count : ℕ) :
    repeatedDigit width digit (count + 1) = 2 ^ width * repeatedDigit width digit count + digit := by
  unfold repeatedDigit
  rw [geom_sum_succ]
  ring

theorem repeated_digit_bit (width digit count lane : ℕ) (fits : digit < 2 ^ width) :
    (repeatedDigit width digit count).testBit lane =
      (decide (lane < width * count) && digit.testBit (lane % width)) := by
  induction count generalizing lane with
  | zero => simp [repeatedDigit]
  | succ count ih =>
    rw [repeated_digit_succ, Nat.testBit_two_pow_mul_add _ fits]
    by_cases first : lane < width
    · have present : lane < width * (count + 1) := by rw [Nat.mul_succ]; omega
      simp [first, present, Nat.mod_eq_of_lt first]
    · rw [ite_eq_right first, ih]
      have wrapped : (lane - width) % width = lane % width := by
        calc
          (lane - width) % width = (lane - width + width) % width := (Nat.add_mod_right _ _).symm
          _ = lane % width := by rw [Nat.sub_add_cancel (Nat.le_of_not_gt first)]
      have present : lane - width < width * count ↔ lane < width * (count + 1) := by
        rw [Nat.mul_succ]
        omega
      simp only [wrapped, present]

theorem digit_fits (run : ℕ) : (2 ^ run - 1) <<< run < 2 ^ (2 * run) := by
  rw [Nat.shiftLeft_eq, two_mul, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one) (Nat.two_pow_pos _)

theorem digit_bit (run index : ℕ) (within : index < 2 * run) :
    ((2 ^ run - 1) <<< run).testBit index = decide (run ≤ index) := by
  have inRun : index - run < run := by omega
  simp [inRun]

theorem lane_bit_pattern (i lane : ℕ) :
    lane.testBit i = decide (2 ^ i ≤ lane % (2 * 2 ^ i)) := by
  let run := 2 ^ i
  have positive : 0 < run := Nat.two_pow_pos i
  have remBound : lane % (2 * run) < 2 * run := Nat.mod_lt _ (by omega)
  have quotientBound : lane % (2 * run) / run < 2 := by
    exact (Nat.div_lt_iff_lt_mul positive).mpr remBound
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.mod_mul_left_div_self lane (2 ^ i) 2]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change lane % (2 * run) / run = 1 ↔ run ≤ lane % (2 * run)
  calc
    lane % (2 * run) / run = 1 ↔ 1 ≤ lane % (2 * run) / run := by omega
    _ ↔ run ≤ lane % (2 * run) := by rw [Nat.le_div_iff_mul_le positive, one_mul]

theorem blocks_cover {k : ℕ} (i : Fin k) :
    (2 : ℕ) ^ k = (2 * 2 ^ i.val) * 2 ^ (k - (i.val + 1)) := by
  have width : i.val + 1 + (k - (i.val + 1)) = k := by have := i.isLt; omega
  calc
    (2 : ℕ) ^ k = 2 ^ (i.val + 1 + (k - (i.val + 1))) := congrArg (fun n : ℕ => 2 ^ n) width.symm
    _ = (2 * 2 ^ i.val) * 2 ^ (k - (i.val + 1)) := by rw [pow_add, pow_succ']

theorem tile_bit {k : ℕ} (i : Fin k) (lane : ℕ) :
    let run := 2 ^ i.val
    (((2 ^ run - 1) <<< run) * ((2 ^ (2 ^ k) - 1) / (2 ^ (2 * run) - 1))).testBit lane =
      (decide (lane < 2 ^ k) && lane.testBit i.val) := by
  intro run
  let count := 2 ^ (k - (i.val + 1))
  let digit := (2 ^ run - 1) <<< run
  have blockCount : 2 ^ k = (2 * run) * count := blocks_cover i
  have runPositive : 0 < run := Nat.two_pow_pos i.val
  have radix : 2 ≤ (2 : ℕ) ^ (2 * run) := Nat.one_lt_two_pow (by omega)
  have allBits : ((2 : ℕ) ^ (2 * run)) ^ count = 2 ^ (2 ^ k) := by
    rw [← pow_mul, ← blockCount]
  have repeated : repeatedDigit (2 * run) digit count =
      digit * ((2 ^ (2 ^ k) - 1) / (2 ^ (2 * run) - 1)) := by
    rw [repeatedDigit, Nat.geomSum_eq radix, allBits]
  change (digit * _).testBit lane = _
  rw [← repeated, repeated_digit_bit _ _ _ _ (digit_fits run), ← blockCount]
  have inside : lane % (2 * run) < 2 * run := Nat.mod_lt _ (by omega)
  rw [show digit.testBit (lane % (2 * run)) = decide (run ≤ lane % (2 * run)) from digit_bit _ _ inside]
  rw [← lane_bit_pattern i.val lane]

end PEqualNP.Outside.L_lib_656_aux

open PEqualNP.Outside.L_lib_656_aux in
theorem PEqualNP.Outside.L_lib_656 : (∀ (k : ℕ) (i : Fin k) (shift : Fin (2 ^ k)),
  let lanes := 2 ^ k
  let full := 2 ^ lanes - 1
  let run := 2 ^ i.val
  let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
  let plane := if shift.val.testBit i.val then full ^^^ tile else tile
  ∀ lane : ℕ, plane.testBit lane =
    (decide (lane < lanes) && (lane ^^^ shift.val).testBit i.val)) := by
  intro k i shift
  dsimp only
  intro lane
  rw [Nat.testBit_xor]
  have reads := tile_bit i lane
  dsimp only at reads
  by_cases inside : lane < 2 ^ k <;>
    cases shift.val.testBit i.val <;>
    cases bit : lane.testBit i.val <;>
    simp [inside, bit, reads]
