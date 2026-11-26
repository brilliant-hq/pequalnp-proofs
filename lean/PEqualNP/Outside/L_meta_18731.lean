import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18731

def route : Array Nat := #[0, 0, 0, 1, 1, 2, 3, 2, 4, 5, 0, 0, 0, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 6, 0, 7, 14, 15, 16, 11, 17, 18, 0, 1, 7, 7, 0, 19, 20, 21, 22, 20, 23, 0, 1, 8, 14, 19, 0, 24, 25, 26, 27, 28, 0, 2, 9, 15, 20, 24, 0, 29, 30, 31, 32, 0, 3, 10, 16, 21, 25, 29, 0, 33, 12, 13, 0, 2, 11, 11, 22, 26, 30, 33, 0, 34, 26, 0, 4, 12, 17, 20, 27, 31, 12, 34, 0, 35, 0, 5, 13, 18, 23, 28, 32, 13, 26, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def extra : Array Nat := #[2, 12, 12, 12, 12, 12, 12, 12, 12, 12, 2, 12, 3, 12, 12, 12, 12, 12, 12, 12, 12, 3, 12, 12, 4, 12, 12, 12, 12, 12, 12, 12, 4, 12, 12, 12, 5, 12, 12, 12, 12, 12, 12, 5, 12, 12, 12, 12, 6, 12, 12, 12, 12, 12, 6, 12, 12, 12, 12, 12, 7, 12, 12, 12, 12, 7, 12, 12, 12, 12, 12, 12, 8, 12, 12, 12, 8, 12, 12, 12, 12, 12, 12, 12, 9, 12, 12, 9, 12, 12, 12, 12, 12, 12, 12, 12, 10, 12, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 11, 11, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0]

def flags : Array Nat := #[0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def rows : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29], #[4, 3, 2, 1, 0, 5, 9, 8, 7, 6, 14, 13, 12, 11, 10, 15, 25, 26, 27, 22, 29, 28, 19, 23, 24, 16, 17, 18, 21, 20], #[5, 10, 7, 1, 0, 4, 14, 11, 2, 6, 9, 12, 13, 8, 3, 15, 23, 22, 24, 26, 29, 28, 19, 25, 27, 16, 21, 18, 17, 20], #[0, 6, 13, 14, 5, 4, 1, 12, 8, 10, 9, 11, 7, 2, 3, 15, 16, 22, 18, 28, 29, 26, 17, 25, 27, 23, 21, 24, 19, 20], #[5, 14, 13, 6, 0, 4, 10, 8, 12, 1, 3, 2, 7, 11, 9, 15, 23, 21, 24, 17, 20, 19, 28, 25, 27, 16, 22, 18, 26, 29], #[4, 9, 12, 6, 0, 5, 3, 11, 13, 1, 10, 7, 2, 8, 14, 15, 25, 17, 27, 21, 20, 19, 28, 23, 24, 16, 26, 18, 22, 29], #[1, 0, 4, 3, 2, 7, 6, 5, 9, 8, 10, 14, 13, 12, 11, 19, 16, 21, 20, 15, 18, 17, 25, 26, 27, 22, 23, 24, 28, 29], #[2, 1, 0, 4, 3, 8, 7, 6, 5, 9, 13, 12, 11, 10, 14, 22, 19, 23, 24, 16, 20, 21, 15, 17, 18, 25, 28, 29, 26, 27], #[0, 4, 3, 2, 1, 6, 5, 9, 8, 7, 12, 11, 10, 14, 13, 16, 15, 17, 18, 25, 27, 26, 22, 28, 29, 19, 21, 20, 23, 24], #[0, 5, 10, 7, 1, 6, 4, 14, 11, 2, 13, 8, 3, 9, 12, 16, 15, 21, 18, 23, 24, 22, 26, 28, 29, 19, 17, 20, 25, 27], #[6, 0, 4, 9, 12, 13, 1, 5, 3, 11, 14, 10, 7, 2, 8, 28, 16, 22, 29, 15, 18, 26, 25, 17, 27, 21, 23, 24, 19, 20], #[7, 1, 0, 5, 10, 11, 2, 6, 4, 14, 12, 13, 8, 3, 9, 26, 19, 25, 27, 16, 20, 17, 15, 21, 18, 23, 28, 29, 22, 24], #[13, 6, 0, 5, 14, 8, 12, 1, 4, 10, 2, 7, 11, 9, 3, 17, 28, 25, 27, 16, 29, 26, 15, 22, 18, 23, 19, 20, 21, 24], #[12, 6, 0, 4, 9, 11, 13, 1, 5, 3, 7, 2, 8, 14, 10, 21, 28, 23, 24, 16, 29, 22, 15, 26, 18, 25, 19, 20, 17, 27], #[2, 3, 4, 0, 1, 7, 8, 9, 5, 6, 11, 12, 13, 14, 10, 19, 22, 23, 24, 25, 29, 28, 15, 26, 27, 16, 21, 20, 17, 18], #[7, 10, 5, 0, 1, 2, 11, 14, 4, 6, 8, 13, 12, 9, 3, 19, 26, 25, 27, 23, 29, 28, 15, 22, 24, 16, 17, 20, 21, 18], #[1, 6, 13, 8, 2, 7, 0, 12, 14, 3, 11, 9, 4, 5, 10, 19, 16, 23, 20, 28, 29, 25, 17, 26, 27, 22, 21, 24, 15, 18], #[8, 2, 1, 6, 13, 14, 3, 7, 0, 12, 10, 11, 9, 4, 5, 17, 22, 15, 18, 19, 24, 21, 16, 23, 20, 28, 26, 27, 25, 29], #[11, 7, 1, 6, 12, 9, 10, 2, 0, 13, 3, 8, 14, 5, 4, 21, 26, 15, 18, 19, 27, 17, 16, 25, 20, 28, 22, 24, 23, 29], #[3, 4, 0, 1, 2, 8, 9, 5, 6, 7, 14, 10, 11, 12, 13, 22, 25, 28, 29, 15, 27, 26, 16, 17, 18, 19, 23, 24, 21, 20], #[8, 14, 5, 4, 3, 2, 13, 10, 0, 9, 7, 11, 12, 6, 1, 22, 17, 16, 18, 23, 20, 21, 15, 19, 24, 25, 26, 29, 28, 27], #[8, 13, 6, 1, 2, 3, 14, 12, 0, 7, 9, 11, 10, 5, 4, 22, 17, 15, 18, 28, 27, 26, 16, 25, 29, 19, 21, 24, 23, 20], #[2, 7, 10, 14, 8, 3, 1, 11, 5, 13, 9, 12, 6, 0, 4, 22, 19, 15, 24, 26, 27, 28, 23, 25, 29, 17, 21, 18, 16, 20], #[9, 3, 2, 7, 11, 12, 4, 8, 1, 10, 13, 14, 5, 0, 6, 21, 25, 16, 20, 22, 29, 23, 19, 28, 24, 26, 17, 18, 15, 27], #[5, 4, 3, 8, 14, 10, 0, 9, 2, 13, 11, 12, 6, 1, 7, 23, 15, 19, 24, 25, 27, 28, 22, 26, 29, 17, 21, 20, 16, 18], #[12, 9, 4, 0, 6, 13, 11, 3, 5, 1, 8, 2, 7, 10, 14, 28, 21, 23, 24, 25, 20, 19, 15, 17, 27, 16, 22, 29, 26, 18], #[11, 9, 4, 5, 10, 7, 12, 3, 0, 14, 2, 8, 13, 6, 1, 26, 21, 16, 18, 25, 20, 17, 15, 19, 27, 23, 22, 29, 28, 24], #[8, 3, 4, 5, 14, 13, 2, 9, 0, 10, 12, 11, 7, 1, 6, 17, 22, 16, 18, 25, 29, 26, 15, 28, 27, 23, 21, 20, 19, 24], #[9, 4, 0, 6, 12, 11, 3, 5, 1, 13, 10, 14, 8, 2, 7, 21, 25, 19, 20, 15, 27, 17, 16, 26, 18, 28, 23, 24, 22, 29], #[13, 14, 5, 0, 6, 12, 8, 10, 4, 1, 11, 7, 2, 3, 9, 28, 17, 25, 27, 23, 20, 19, 15, 21, 24, 16, 26, 29, 22, 18], #[10, 5, 0, 1, 7, 11, 14, 4, 6, 2, 9, 3, 8, 13, 12, 26, 23, 28, 29, 15, 24, 22, 16, 21, 18, 19, 25, 27, 17, 20], #[14, 5, 0, 6, 13, 8, 10, 4, 1, 12, 3, 9, 11, 7, 2, 17, 23, 19, 20, 15, 24, 21, 16, 22, 18, 28, 25, 27, 26, 29], #[11, 10, 5, 4, 9, 12, 7, 14, 0, 3, 13, 8, 2, 1, 6, 21, 26, 16, 18, 23, 29, 22, 15, 28, 24, 25, 17, 20, 19, 27], #[11, 12, 6, 1, 7, 10, 9, 13, 0, 2, 14, 8, 3, 4, 5, 26, 21, 15, 18, 28, 24, 22, 16, 23, 29, 19, 17, 27, 25, 20], #[14, 10, 7, 2, 8, 13, 5, 11, 1, 3, 12, 9, 4, 0, 6, 17, 23, 16, 20, 26, 29, 25, 19, 28, 27, 22, 21, 18, 15, 24], #[13, 12, 9, 3, 8, 14, 6, 11, 4, 2, 10, 7, 1, 0, 5, 17, 28, 15, 27, 21, 24, 19, 25, 23, 20, 22, 26, 18, 16, 29]]

def columns : Array (Array Nat) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[0, 1, 2, 6, 5, 4, 3, 7, 11, 10, 9, 8], #[0, 1, 2, 6, 5, 10, 7, 3, 11, 4, 8, 9], #[0, 1, 2, 3, 8, 10, 7, 6, 4, 11, 5, 9], #[0, 1, 2, 6, 11, 9, 7, 3, 5, 8, 4, 10], #[0, 1, 2, 6, 11, 8, 3, 7, 5, 9, 10, 4], #[0, 1, 4, 3, 2, 6, 5, 9, 8, 7, 11, 10], #[0, 1, 5, 4, 3, 2, 6, 10, 9, 8, 7, 11], #[0, 1, 3, 2, 6, 5, 4, 8, 7, 11, 10, 9], #[0, 1, 3, 2, 6, 11, 8, 4, 7, 5, 9, 10], #[0, 1, 4, 3, 8, 10, 5, 9, 2, 11, 7, 6], #[0, 1, 5, 4, 3, 8, 10, 6, 9, 2, 11, 7], #[0, 1, 5, 4, 9, 7, 10, 6, 3, 11, 2, 8], #[0, 1, 5, 4, 9, 11, 6, 10, 3, 7, 8, 2], #[0, 1, 5, 6, 2, 3, 4, 10, 11, 7, 8, 9], #[0, 1, 5, 6, 2, 7, 10, 4, 11, 3, 9, 8], #[0, 1, 8, 3, 2, 6, 11, 10, 4, 7, 5, 9], #[0, 1, 10, 5, 4, 3, 8, 7, 6, 9, 2, 11], #[0, 1, 10, 5, 4, 9, 7, 8, 6, 3, 11, 2], #[0, 1, 4, 5, 6, 2, 3, 9, 10, 11, 7, 8], #[0, 1, 5, 10, 7, 2, 6, 4, 8, 9, 3, 11], #[0, 1, 10, 5, 6, 2, 7, 8, 4, 11, 3, 9], #[0, 1, 10, 8, 3, 2, 7, 5, 11, 4, 6, 9], #[0, 1, 8, 10, 5, 4, 3, 11, 7, 6, 9, 2], #[0, 1, 3, 8, 10, 5, 4, 2, 11, 7, 6, 9], #[0, 1, 5, 6, 11, 9, 4, 10, 2, 8, 7, 3], #[0, 1, 5, 10, 7, 9, 4, 6, 8, 2, 11, 3], #[0, 1, 5, 10, 8, 3, 4, 6, 7, 11, 2, 9], #[0, 1, 4, 5, 10, 8, 3, 9, 6, 7, 11, 2], #[0, 1, 5, 6, 11, 8, 10, 4, 2, 9, 3, 7], #[0, 1, 4, 5, 6, 11, 9, 3, 10, 2, 8, 7], #[0, 1, 4, 5, 10, 7, 9, 3, 6, 8, 2, 11], #[0, 1, 5, 10, 8, 11, 6, 4, 7, 3, 9, 2], #[0, 1, 10, 5, 6, 11, 8, 7, 4, 2, 9, 3], #[0, 1, 8, 10, 5, 6, 11, 3, 7, 4, 2, 9], #[0, 1, 10, 8, 11, 6, 5, 7, 3, 9, 2, 4]]

def idx (a b : Fin 11) : Nat := a.val * 11 + b.val

def side (a b : Fin 11) : Bool := flags[idx a b]?.getD 0 == 1

def col (a b : Fin 11) (j : Fin 13) : Fin 13 := Fin.ofNat 13
  (if j.val = 12 then extra[idx a b]?.getD 0 else
    ((columns[route[idx a b]?.getD 0]?.getD #[])[j.val]?).getD 0)

def row (a b : Fin 11) (k : Fin 30) : Fin 30 := Fin.ofNat 30
  (((rows[route[idx a b]?.getD 0]?.getD #[])[k.val]?).getD 0)

def inputs (a b : Nat) : List Nat :=
  let c := [579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048]
  0 :: 1073741823 :: (c ++ [c.getD a 0 ||| c.getD b 0])

def good (a b : Fin 11) : Prop :=
  (∀ k : Fin 30, (row a b k).val < 15 ↔ k.val < 15) ∧
    ∀ (j : Fin 13) (k : Fin 30), ((inputs a b).getD j.val 0).testBit (row a b k).val =
      ((inputs 0 (if side a b then 1 else 2)).getD (col a b j).val 0).testBit k.val

instance (a b : Fin 11) : Decidable (good a b) := by unfold good; infer_instance

theorem case_0_0 : good 0 0 := by decide +kernel

theorem case_0_1 : good 0 1 := by decide +kernel

theorem case_0_2 : good 0 2 := by decide +kernel

theorem case_0_3 : good 0 3 := by decide +kernel

theorem case_0_4 : good 0 4 := by decide +kernel

theorem case_0_5 : good 0 5 := by decide +kernel

theorem case_0_6 : good 0 6 := by decide +kernel

theorem case_0_7 : good 0 7 := by decide +kernel

theorem case_0_8 : good 0 8 := by decide +kernel

theorem case_0_9 : good 0 9 := by decide +kernel

theorem case_0_10 : good 0 10 := by decide +kernel

theorem block_0 (b : Fin 11) : good 0 b := by
  fin_cases b
  · exact case_0_0
  · exact case_0_1
  · exact case_0_2
  · exact case_0_3
  · exact case_0_4
  · exact case_0_5
  · exact case_0_6
  · exact case_0_7
  · exact case_0_8
  · exact case_0_9
  · exact case_0_10

theorem case_1_0 : good 1 0 := by decide +kernel

theorem case_1_1 : good 1 1 := by decide +kernel

theorem case_1_2 : good 1 2 := by decide +kernel

theorem case_1_3 : good 1 3 := by decide +kernel

theorem case_1_4 : good 1 4 := by decide +kernel

theorem case_1_5 : good 1 5 := by decide +kernel

theorem case_1_6 : good 1 6 := by decide +kernel

theorem case_1_7 : good 1 7 := by decide +kernel

theorem case_1_8 : good 1 8 := by decide +kernel

theorem case_1_9 : good 1 9 := by decide +kernel

theorem case_1_10 : good 1 10 := by decide +kernel

theorem block_1 (b : Fin 11) : good 1 b := by
  fin_cases b
  · exact case_1_0
  · exact case_1_1
  · exact case_1_2
  · exact case_1_3
  · exact case_1_4
  · exact case_1_5
  · exact case_1_6
  · exact case_1_7
  · exact case_1_8
  · exact case_1_9
  · exact case_1_10

theorem case_2_0 : good 2 0 := by decide +kernel

theorem case_2_1 : good 2 1 := by decide +kernel

theorem case_2_2 : good 2 2 := by decide +kernel

theorem case_2_3 : good 2 3 := by decide +kernel

theorem case_2_4 : good 2 4 := by decide +kernel

theorem case_2_5 : good 2 5 := by decide +kernel

theorem case_2_6 : good 2 6 := by decide +kernel

theorem case_2_7 : good 2 7 := by decide +kernel

theorem case_2_8 : good 2 8 := by decide +kernel

theorem case_2_9 : good 2 9 := by decide +kernel

theorem case_2_10 : good 2 10 := by decide +kernel

theorem block_2 (b : Fin 11) : good 2 b := by
  fin_cases b
  · exact case_2_0
  · exact case_2_1
  · exact case_2_2
  · exact case_2_3
  · exact case_2_4
  · exact case_2_5
  · exact case_2_6
  · exact case_2_7
  · exact case_2_8
  · exact case_2_9
  · exact case_2_10

theorem case_3_0 : good 3 0 := by decide +kernel

theorem case_3_1 : good 3 1 := by decide +kernel

theorem case_3_2 : good 3 2 := by decide +kernel

theorem case_3_3 : good 3 3 := by decide +kernel

theorem case_3_4 : good 3 4 := by decide +kernel

theorem case_3_5 : good 3 5 := by decide +kernel

theorem case_3_6 : good 3 6 := by decide +kernel

theorem case_3_7 : good 3 7 := by decide +kernel

theorem case_3_8 : good 3 8 := by decide +kernel

theorem case_3_9 : good 3 9 := by decide +kernel

theorem case_3_10 : good 3 10 := by decide +kernel

theorem block_3 (b : Fin 11) : good 3 b := by
  fin_cases b
  · exact case_3_0
  · exact case_3_1
  · exact case_3_2
  · exact case_3_3
  · exact case_3_4
  · exact case_3_5
  · exact case_3_6
  · exact case_3_7
  · exact case_3_8
  · exact case_3_9
  · exact case_3_10

theorem case_4_0 : good 4 0 := by decide +kernel

theorem case_4_1 : good 4 1 := by decide +kernel

theorem case_4_2 : good 4 2 := by decide +kernel

theorem case_4_3 : good 4 3 := by decide +kernel

theorem case_4_4 : good 4 4 := by decide +kernel

theorem case_4_5 : good 4 5 := by decide +kernel

theorem case_4_6 : good 4 6 := by decide +kernel

theorem case_4_7 : good 4 7 := by decide +kernel

theorem case_4_8 : good 4 8 := by decide +kernel

theorem case_4_9 : good 4 9 := by decide +kernel

theorem case_4_10 : good 4 10 := by decide +kernel

theorem block_4 (b : Fin 11) : good 4 b := by
  fin_cases b
  · exact case_4_0
  · exact case_4_1
  · exact case_4_2
  · exact case_4_3
  · exact case_4_4
  · exact case_4_5
  · exact case_4_6
  · exact case_4_7
  · exact case_4_8
  · exact case_4_9
  · exact case_4_10

theorem case_5_0 : good 5 0 := by decide +kernel

theorem case_5_1 : good 5 1 := by decide +kernel

theorem case_5_2 : good 5 2 := by decide +kernel

theorem case_5_3 : good 5 3 := by decide +kernel

theorem case_5_4 : good 5 4 := by decide +kernel

theorem case_5_5 : good 5 5 := by decide +kernel

theorem case_5_6 : good 5 6 := by decide +kernel

theorem case_5_7 : good 5 7 := by decide +kernel

theorem case_5_8 : good 5 8 := by decide +kernel

theorem case_5_9 : good 5 9 := by decide +kernel

theorem case_5_10 : good 5 10 := by decide +kernel

theorem block_5 (b : Fin 11) : good 5 b := by
  fin_cases b
  · exact case_5_0
  · exact case_5_1
  · exact case_5_2
  · exact case_5_3
  · exact case_5_4
  · exact case_5_5
  · exact case_5_6
  · exact case_5_7
  · exact case_5_8
  · exact case_5_9
  · exact case_5_10

theorem case_6_0 : good 6 0 := by decide +kernel

theorem case_6_1 : good 6 1 := by decide +kernel

theorem case_6_2 : good 6 2 := by decide +kernel

theorem case_6_3 : good 6 3 := by decide +kernel

theorem case_6_4 : good 6 4 := by decide +kernel

theorem case_6_5 : good 6 5 := by decide +kernel

theorem case_6_6 : good 6 6 := by decide +kernel

theorem case_6_7 : good 6 7 := by decide +kernel

theorem case_6_8 : good 6 8 := by decide +kernel

theorem case_6_9 : good 6 9 := by decide +kernel

theorem case_6_10 : good 6 10 := by decide +kernel

theorem block_6 (b : Fin 11) : good 6 b := by
  fin_cases b
  · exact case_6_0
  · exact case_6_1
  · exact case_6_2
  · exact case_6_3
  · exact case_6_4
  · exact case_6_5
  · exact case_6_6
  · exact case_6_7
  · exact case_6_8
  · exact case_6_9
  · exact case_6_10

theorem case_7_0 : good 7 0 := by decide +kernel

theorem case_7_1 : good 7 1 := by decide +kernel

theorem case_7_2 : good 7 2 := by decide +kernel

theorem case_7_3 : good 7 3 := by decide +kernel

theorem case_7_4 : good 7 4 := by decide +kernel

theorem case_7_5 : good 7 5 := by decide +kernel

theorem case_7_6 : good 7 6 := by decide +kernel

theorem case_7_7 : good 7 7 := by decide +kernel

theorem case_7_8 : good 7 8 := by decide +kernel

theorem case_7_9 : good 7 9 := by decide +kernel

theorem case_7_10 : good 7 10 := by decide +kernel

theorem block_7 (b : Fin 11) : good 7 b := by
  fin_cases b
  · exact case_7_0
  · exact case_7_1
  · exact case_7_2
  · exact case_7_3
  · exact case_7_4
  · exact case_7_5
  · exact case_7_6
  · exact case_7_7
  · exact case_7_8
  · exact case_7_9
  · exact case_7_10

theorem case_8_0 : good 8 0 := by decide +kernel

theorem case_8_1 : good 8 1 := by decide +kernel

theorem case_8_2 : good 8 2 := by decide +kernel

theorem case_8_3 : good 8 3 := by decide +kernel

theorem case_8_4 : good 8 4 := by decide +kernel

theorem case_8_5 : good 8 5 := by decide +kernel

theorem case_8_6 : good 8 6 := by decide +kernel

theorem case_8_7 : good 8 7 := by decide +kernel

theorem case_8_8 : good 8 8 := by decide +kernel

theorem case_8_9 : good 8 9 := by decide +kernel

theorem case_8_10 : good 8 10 := by decide +kernel

theorem block_8 (b : Fin 11) : good 8 b := by
  fin_cases b
  · exact case_8_0
  · exact case_8_1
  · exact case_8_2
  · exact case_8_3
  · exact case_8_4
  · exact case_8_5
  · exact case_8_6
  · exact case_8_7
  · exact case_8_8
  · exact case_8_9
  · exact case_8_10

theorem case_9_0 : good 9 0 := by decide +kernel

theorem case_9_1 : good 9 1 := by decide +kernel

theorem case_9_2 : good 9 2 := by decide +kernel

theorem case_9_3 : good 9 3 := by decide +kernel

theorem case_9_4 : good 9 4 := by decide +kernel

theorem case_9_5 : good 9 5 := by decide +kernel

theorem case_9_6 : good 9 6 := by decide +kernel

theorem case_9_7 : good 9 7 := by decide +kernel

theorem case_9_8 : good 9 8 := by decide +kernel

theorem case_9_9 : good 9 9 := by decide +kernel

theorem case_9_10 : good 9 10 := by decide +kernel

theorem block_9 (b : Fin 11) : good 9 b := by
  fin_cases b
  · exact case_9_0
  · exact case_9_1
  · exact case_9_2
  · exact case_9_3
  · exact case_9_4
  · exact case_9_5
  · exact case_9_6
  · exact case_9_7
  · exact case_9_8
  · exact case_9_9
  · exact case_9_10

theorem case_10_0 : good 10 0 := by decide +kernel

theorem case_10_1 : good 10 1 := by decide +kernel

theorem case_10_2 : good 10 2 := by decide +kernel

theorem case_10_3 : good 10 3 := by decide +kernel

theorem case_10_4 : good 10 4 := by decide +kernel

theorem case_10_5 : good 10 5 := by decide +kernel

theorem case_10_6 : good 10 6 := by decide +kernel

theorem case_10_7 : good 10 7 := by decide +kernel

theorem case_10_8 : good 10 8 := by decide +kernel

theorem case_10_9 : good 10 9 := by decide +kernel

theorem case_10_10 : good 10 10 := by decide +kernel

theorem block_10 (b : Fin 11) : good 10 b := by
  fin_cases b
  · exact case_10_0
  · exact case_10_1
  · exact case_10_2
  · exact case_10_3
  · exact case_10_4
  · exact case_10_5
  · exact case_10_6
  · exact case_10_7
  · exact case_10_8
  · exact case_10_9
  · exact case_10_10

theorem verify (a b : Fin 11) : good a b := by
  fin_cases a
  · exact block_0 b
  · exact block_1 b
  · exact block_2 b
  · exact block_3 b
  · exact block_4 b
  · exact block_5 b
  · exact block_6 b
  · exact block_7 b
  · exact block_8 b
  · exact block_9 b
  · exact block_10 b

end PEqualNP.Outside.L_meta_18731

open PEqualNP.Outside.L_meta_18731 in
theorem PEqualNP.Outside.L_meta_18731 : have x1 : List ℕ := [(579928113 : ℕ), (419987523 : ℕ), (608501894 : ℕ), (169476364 : ℕ), (23364120 : ℕ), (201770016 : ℕ), (3616832 : ℕ), (28839040 : ℕ), (834691328 : ℕ), (1040194048 : ℕ)]; have x2 : ℕ → ℕ → List ℕ := fun (x2 x3 : ℕ) => (0 : ℕ) :: (1073741823 : ℕ) :: (x1 ++ [x1.getD x2 (0 : ℕ) ||| x1.getD x3 (0 : ℕ)]); ∀ (x3 x4 : Fin (11 : ℕ)), ∃ (x5 : Bool) (x6 : Fin (13 : ℕ) → Fin (13 : ℕ)) (x7 : Fin (30 : ℕ) → Fin (30 : ℕ)), (∀ (x8 : Fin (30 : ℕ)), ↑(x7 x8) < (15 : ℕ) ↔ ↑x8 < (15 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)) (x9 : Fin (30 : ℕ)), ((x2 ↑x3 ↑x4).getD ↑x8 (0 : ℕ)).testBit ↑(x7 x9) = ((x2 (0 : ℕ) (if x5 = Bool.true then (1 : ℕ) else (2 : ℕ))).getD ↑(x6 x8) (0 : ℕ)).testBit ↑x9 := by
  dsimp only
  intro a b
  exact ⟨side a b, col a b, row a b, verify a b⟩
