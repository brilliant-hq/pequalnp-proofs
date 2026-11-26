import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18637

private def offsets : Finset (Fin 13) := {0, 1, 3, 9}
private def hit (d : Bool) (x y : Fin 13) : Prop :=
  if d then x - y ∈ offsets else y - x ∈ offsets

instance (d : Bool) (x y : Fin 13) : Decidable (hit d x y) := by
  unfold hit
  infer_instance

private def neighbors (d : Bool) (x : Fin 13) : List (Fin 13) :=
  if d then [x, x - 1, x - 3, x - 9] else [x, x + 1, x + 3, x + 9]

private theorem neighborsSpec : ∀ (d : Bool) (x y : Fin 13), y ∈ neighbors d x ↔ hit d x y := by
  decide +kernel

private theorem neighborsNodup : ∀ (d : Bool) (x : Fin 13), (neighbors d x).Nodup := by
  decide +kernel

private def intCode (xs : List (Fin 13)) : ℕ := xs.foldr (fun i r => 2^i.val ||| r) 0

private theorem intCodeBit (xs : List (Fin 13)) (i : Fin 13) :
    (intCode xs).testBit i.val = decide (i ∈ xs) := by
  induction xs with
  | nil => simp [intCode]
  | cons a as ih =>
    change (2^a.val ||| intCode as).testBit i.val = decide (i ∈ a :: as)
    rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
    simp [Fin.val_inj, eq_comm]

private noncomputable def encode (S : Finset (Fin 13)) : BitVec 13 := BitVec.ofNat 13 (intCode S.toList)

private theorem encodeBit (S : Finset (Fin 13)) (i : Fin 13) :
    (encode S).getLsbD i.val = decide (i ∈ S) := by
  rw [encode, BitVec.getLsbD_ofNat, intCodeBit]
  simp only [i.isLt, decide_true, Bool.true_and, Finset.mem_toList]

private def arcCheck (d : Bool) (w : BitVec 13) : Bool :=
  (List.finRange 13).all fun x => decide ((neighbors d x).countP (fun y => w.getLsbD y.val) ≤ 2)

private def freeCheck (d : Bool) (w : BitVec 13) (x : Fin 13) : Bool :=
  (neighbors d x).all (fun y => !(w.getLsbD y.val))


private theorem countMatches (d : Bool) (S : Finset (Fin 13)) (x : Fin 13) :
    (neighbors d x).countP (fun y => (encode S).getLsbD y.val) =
      (S.filter (fun y => hit d x y)).card := by
  rw [List.countP_eq_length_filter]
  let ls := (neighbors d x).filter (fun y => (encode S).getLsbD y.val)
  have equal : ls.toFinset = S.filter (fun y => hit d x y) := by
    ext y
    simp only [ls, List.mem_toFinset, List.mem_filter, neighborsSpec, encodeBit,
      decide_eq_true_eq, Finset.mem_filter, and_comm]
  rw [← equal]
  exact (List.toFinset_card_of_nodup ((neighborsNodup d x).filter _)).symm

private theorem arcMatches (d : Bool) (S : Finset (Fin 13))
    (h : ∀ x, (S.filter (fun y => hit d x y)).card ≤ 2) :
    arcCheck d (encode S) = true := by
  apply List.all_eq_true.mpr
  intro x _
  apply decide_eq_true
  rw [countMatches]
  exact h x

private theorem offMatches (d : Bool) (S : Finset (Fin 13)) (x : Fin 13)
    (ok : freeCheck d (encode S) x = true) : ∀ y ∈ S, ¬ hit d x y := by
  intro y hy h
  have edge := (neighborsSpec d x y).mpr h
  have bad := List.all_eq_true.mp ok y edge
  change (!(encode S).getLsbD y.val) = true at bad
  simp only [encodeBit, decide_eq_true hy, Bool.not_true, Bool.false_eq_true] at bad


private def countBits (w : BitVec 13) : ℕ :=
  (List.finRange 13).countP (fun i => w.getLsbD i.val)

private theorem countBitsEncode (S : Finset (Fin 13)) : countBits (encode S) = S.card := by
  unfold countBits
  rw [List.countP_eq_length_filter]
  let ls := (List.finRange 13).filter (fun i => (encode S).getLsbD i.val)
  have equal : ls.toFinset = S := by
    ext i
    simp only [ls, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      encodeBit, decide_eq_true_eq]
  change ls.length = S.card
  rw [← equal]
  exact (List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter _)).symm

private def table : List ℕ := [22282261, 5799955, 23330829, 7405575, 3211303, 19988517, 3735587, 21233693, 21757977, 7340103, 24117317, 7372867, 19415081, 22020181, 5275731, 22052945, 23068749, 23085129, 6389891, 18890857, 19923045, 19939425, 6324419, 6553741, 6570121, 6357127, 6619269, 4751635, 21528849, 21512457, 6308041, 17891877, 21004625, 20988233, 17318185, 21496089]

private def writtenTable : List ℕ := [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587, 19988517, 3211303, 19415081, 7372867, 24117317, 7340103, 23085129, 23068749, 22052945, 5275731, 22020181, 19939425, 19923045, 18890857, 6389891, 6619269, 6357127, 6570121, 6553741, 6324419, 6308041, 21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]

private theorem writtenAgreement : table.toFinset = writtenTable.toFinset := by decide +kernel


private theorem tableLength : table.length = 36 := by decide +kernel

private def pick (w : ℕ) : Fin 36 × Fin 13 :=
  if w < 1664 then if w < 533 then if w < 170 then if w < 82 then if w < 42 then if w < 28 then if w < 19 then if w < 13 then (32, 0) else if w < 14 then (33, 0) else (32, 1) else if w < 25 then if w < 21 then (34, 0) else (35, 0) else if w < 26 then (27, 0) else (33, 1) else if w < 37 then if w < 29 then (32, 2) else if w < 35 then (28, 0) else (29, 0) else if w < 39 then if w < 38 then (30, 0) else (34, 1) else if w < 41 then (31, 0) else (23, 0) else if w < 70 then if w < 56 then if w < 50 then (35, 1) else if w < 52 then (27, 1) else (33, 2) else if w < 67 then if w < 58 then (32, 3) else (28, 1) else if w < 69 then (24, 0) else (25, 0) else if w < 76 then if w < 73 then if w < 71 then (29, 1) else (26, 0) else if w < 74 then (18, 0) else (30, 1) else if w < 78 then if w < 77 then (34, 2) else (19, 0) else if w < 81 then (31, 1) else (20, 0) else if w < 135 then if w < 104 then if w < 85 then if w < 83 then (23, 1) else if w < 84 then (21, 0) else (35, 2) else if w < 100 then if w < 97 then (22, 0) else (14, 0) else if w < 101 then (27, 2) else (15, 0) else if w < 116 then if w < 105 then (33, 3) else if w < 112 then (16, 0) else (32, 4) else if w < 133 then if w < 131 then (28, 2) else (17, 0) else if w < 134 then (9, 0) else (24, 1) else if w < 148 then if w < 140 then if w < 137 then (10, 0) else if w < 138 then (11, 0) else (25, 1) else if w < 142 then if w < 141 then (29, 2) else (12, 0) else if w < 146 then (26, 1) else (18, 1) else if w < 162 then if w < 154 then if w < 152 then (30, 2) else (34, 3) else if w < 156 then (19, 1) else (31, 2) else if w < 166 then if w < 164 then (20, 1) else (23, 2) else if w < 168 then (21, 1) else (35, 3) else if w < 304 then if w < 266 then if w < 208 then if w < 195 then if w < 193 then (22, 1) else if w < 194 then (17, 6) else (14, 1) else if w < 201 then if w < 200 then (13, 0) else (27, 3) else if w < 202 then (5, 0) else (15, 1) else if w < 232 then if w < 210 then (33, 4) else if w < 224 then (16, 1) else (32, 5) else if w < 262 then if w < 259 then (28, 3) else (14, 8) else if w < 265 then (17, 1) else (6, 0) else if w < 280 then if w < 273 then if w < 268 then (9, 1) else if w < 270 then (24, 2) else (10, 1) else if w < 275 then if w < 274 then (7, 0) else (11, 1) else if w < 276 then (8, 0) else (25, 2) else if w < 289 then if w < 282 then if w < 281 then (29, 3) else (0, 0) else if w < 284 then (12, 1) else (26, 2) else if w < 296 then if w < 292 then (6, 5) else (18, 2) else if w < 297 then (30, 3) else (1, 0) else if w < 390 then if w < 332 then if w < 321 then if w < 308 then (34, 4) else if w < 312 then (19, 2) else (31, 3) else if w < 328 then if w < 324 then (9, 6) else (20, 2) else if w < 329 then (23, 3) else (2, 0) else if w < 385 then if w < 337 then if w < 336 then (21, 2) else (35, 4) else if w < 340 then (3, 0) else (22, 2) else if w < 387 then if w < 386 then (24, 7) else (17, 7) else if w < 388 then (13, 7) else (14, 2) else if w < 449 then if w < 404 then if w < 400 then (13, 1) else if w < 402 then (27, 4) else (5, 1) else if w < 420 then if w < 416 then (15, 2) else (33, 5) else if w < 448 then (16, 2) else (32, 6) else if w < 524 then if w < 517 then if w < 464 then (10, 6) else (28, 4) else if w < 518 then (20, 9) else (14, 9) else if w < 530 then if w < 529 then (17, 2) else (7, 9) else if w < 532 then (6, 1) else (9, 2) else if w < 1057 then if w < 672 then if w < 578 then if w < 550 then if w < 545 then if w < 536 then (3, 9) else if w < 540 then (24, 3) else (10, 2) else if w < 548 then if w < 546 then (7, 5) else (7, 1) else if w < 549 then (11, 2) else (4, 0) else if w < 562 then if w < 552 then (8, 1) else if w < 560 then (25, 3) else (29, 4) else if w < 568 then if w < 564 then (0, 1) else (12, 2) else if w < 577 then (26, 3) else (11, 6) else if w < 616 then if w < 593 then if w < 584 then (6, 6) else if w < 592 then (18, 3) else (30, 4) else if w < 608 then if w < 594 then (4, 4) else (1, 1) else if w < 609 then (34, 5) else (8, 5) else if w < 648 then if w < 641 then if w < 624 then (19, 3) else (31, 4) else if w < 642 then (25, 7) else (9, 7) else if w < 658 then if w < 656 then (20, 3) else (23, 4) else if w < 664 then (2, 1) else (21, 3) else if w < 833 then if w < 776 then if w < 769 then if w < 674 then (35, 5) else if w < 680 then (3, 1) else (22, 3) else if w < 772 then if w < 770 then (29, 8) else (24, 8) else if w < 774 then (17, 8) else (13, 8) else if w < 801 then if w < 780 then (14, 3) else if w < 800 then (13, 2) else (27, 5) else if w < 808 then if w < 804 then (0, 5) else (5, 2) else if w < 832 then (15, 3) else (33, 6) else if w < 1029 then if w < 897 then if w < 840 then (12, 6) else if w < 896 then (16, 3) else (32, 7) else if w < 928 then if w < 898 then (26, 7) else (10, 7) else if w < 1027 then (28, 5) else (27, 10) else if w < 1037 then if w < 1034 then if w < 1033 then (23, 10) else (18, 10) else if w < 1036 then (20, 10) else (14, 10) else if w < 1048 then if w < 1041 then (16, 10) else (11, 10) else if w < 1049 then (17, 3) else (5, 10) else if w < 1216 then if w < 1100 then if w < 1066 then if w < 1060 then if w < 1058 then (6, 10) else if w < 1059 then (7, 10) else (0, 10) else if w < 1064 then if w < 1061 then (6, 2) else (1, 10) else if w < 1065 then (9, 3) else (2, 10) else if w < 1090 then if w < 1072 then (3, 10) else if w < 1080 then (24, 4) else (10, 3) else if w < 1096 then if w < 1092 then (7, 6) else (7, 2) else if w < 1098 then (11, 3) else (4, 1) else if w < 1154 then if w < 1124 then if w < 1104 then (8, 2) else if w < 1120 then (25, 4) else (29, 5) else if w < 1136 then if w < 1128 then (0, 2) else (12, 3) else if w < 1153 then (26, 4) else (18, 7) else if w < 1168 then if w < 1156 then if w < 1155 then (11, 7) else (5, 7) else if w < 1157 then (6, 7) else (2, 7) else if w < 1186 then if w < 1184 then (18, 4) else (30, 5) else if w < 1188 then (4, 5) else (1, 2) else if w < 1348 then if w < 1284 then if w < 1248 then if w < 1218 then (34, 6) else if w < 1232 then (8, 6) else (19, 4) else if w < 1282 then if w < 1281 then (31, 5) else (30, 8) else if w < 1283 then (25, 8) else (15, 8) else if w < 1313 then if w < 1297 then if w < 1296 then (9, 8) else (20, 4) else if w < 1312 then (4, 8) else (23, 5) else if w < 1328 then if w < 1316 then (1, 5) else (2, 2) else if w < 1344 then (21, 4) else (35, 6) else if w < 1548 then if w < 1538 then if w < 1360 then (3, 2) else if w < 1537 then (22, 4) else (34, 9) else if w < 1541 then if w < 1540 then (29, 9) else (24, 9) else if w < 1544 then (21, 9) else (17, 9) else if w < 1600 then if w < 1553 then if w < 1552 then (13, 9) else (14, 4) else if w < 1560 then (8, 9) else (13, 3) else if w < 1608 then if w < 1602 then (27, 6) else (0, 6) else if w < 1616 then (5, 3) else (15, 4) else if w < 4116 then if w < 2314 then if w < 2116 then if w < 2058 then if w < 1796 then if w < 1680 then if w < 1665 then (33, 7) else if w < 1666 then (19, 7) else (12, 7) else if w < 1793 then if w < 1792 then (16, 4) else (32, 8) else if w < 1794 then (31, 8) else (26, 8) else if w < 2053 then if w < 1856 then (10, 8) else if w < 2051 then (28, 6) else (33, 11) else if w < 2055 then if w < 2054 then (35, 11) else (27, 11) else if w < 2057 then (28, 11) else (30, 11) else if w < 2073 then if w < 2067 then if w < 2065 then (23, 11) else if w < 2066 then (25, 11) else (18, 11) else if w < 2069 then if w < 2068 then (19, 11) else (20, 11) else if w < 2072 then (22, 11) else (14, 11) else if w < 2083 then if w < 2081 then if w < 2074 then (15, 11) else (16, 11) else if w < 2082 then (9, 11) else (11, 11) else if w < 2098 then if w < 2096 then (12, 11) else (17, 4) else if w < 2114 then (5, 11) else (6, 11) else if w < 2192 then if w < 2144 then if w < 2122 then if w < 2118 then (7, 11) else if w < 2120 then (0, 11) else (6, 3) else if w < 2130 then if w < 2128 then (1, 11) else (9, 4) else if w < 2132 then (2, 11) else (3, 11) else if w < 2180 then if w < 2160 then (24, 5) else if w < 2177 then (10, 4) else (20, 7) else if w < 2184 then if w < 2181 then (7, 7) else (3, 7) else if w < 2185 then (7, 3) else (4, 11) else if w < 2272 then if w < 2208 then if w < 2196 then (11, 4) else if w < 2200 then (4, 2) else (8, 3) else if w < 2248 then if w < 2240 then (25, 5) else (29, 6) else if w < 2256 then (0, 3) else (12, 4) else if w < 2308 then if w < 2306 then if w < 2305 then (26, 5) else (23, 8) else if w < 2307 then (18, 8) else (16, 8) else if w < 2312 then if w < 2310 then (11, 8) else (5, 8) else if w < 2313 then (6, 8) else (1, 8) else if w < 3076 then if w < 2565 then if w < 2433 then if w < 2368 then if w < 2336 then (2, 8) else if w < 2337 then (18, 5) else (2, 5) else if w < 2376 then if w < 2372 then (30, 6) else (4, 6) else if w < 2432 then (1, 3) else (34, 7) else if w < 2496 then if w < 2436 then (21, 7) else if w < 2464 then (8, 7) else (19, 5) else if w < 2562 then if w < 2561 then (31, 6) else (35, 9) else if w < 2564 then (30, 9) else (25, 9) else if w < 2626 then if w < 2592 then if w < 2566 then (22, 9) else if w < 2568 then (15, 9) else (9, 9) else if w < 2594 then if w < 2593 then (20, 5) else (3, 5) else if w < 2624 then (4, 9) else (23, 6) else if w < 2689 then if w < 2656 then if w < 2632 then (1, 6) else (2, 3) else if w < 2688 then (21, 5) else (35, 7) else if w < 2720 then if w < 2696 then (22, 7) else (3, 3) else if w < 3074 then (22, 5) else (34, 10) else if w < 3360 then if w < 3120 then if w < 3088 then if w < 3080 then (29, 10) else if w < 3082 then (24, 10) else (21, 10) else if w < 3104 then if w < 3096 then (17, 10) else (13, 10) else if w < 3106 then (14, 5) else (8, 10) else if w < 3232 then if w < 3204 then if w < 3200 then (13, 4) else (27, 7) else if w < 3216 then (0, 7) else (5, 4) else if w < 3330 then if w < 3328 then (15, 5) else (33, 8) else if w < 3332 then (19, 8) else (12, 8) else if w < 4102 then if w < 3588 then if w < 3584 then (16, 5) else if w < 3586 then (32, 9) else (31, 9) else if w < 3712 then if w < 3592 then (26, 9) else (10, 9) else if w < 4099 then (28, 7) else (32, 12) else if w < 4110 then if w < 4106 then if w < 4105 then (33, 12) else (34, 12) else if w < 4108 then (35, 12) else (27, 12) else if w < 4114 then if w < 4113 then (28, 12) else (29, 12) else if w < 4115 then (30, 12) else (31, 12) else if w < 4674 then if w < 4264 then if w < 4163 then if w < 4137 then if w < 4131 then if w < 4129 then (23, 12) else if w < 4130 then (24, 12) else (25, 12) else if w < 4134 then if w < 4132 then (26, 12) else (18, 12) else if w < 4136 then (19, 12) else (20, 12) else if w < 4146 then if w < 4138 then (21, 12) else if w < 4144 then (22, 12) else (14, 12) else if w < 4161 then if w < 4148 then (15, 12) else (16, 12) else if w < 4162 then (17, 12) else (9, 12) else if w < 4228 then if w < 4192 then if w < 4164 then (10, 12) else if w < 4166 then (11, 12) else (12, 12) else if w < 4196 then if w < 4193 then (17, 5) else (13, 12) else if w < 4225 then (5, 12) else (14, 7) else if w < 4240 then if w < 4233 then if w < 4232 then (6, 12) else (7, 12) else if w < 4236 then (8, 12) else (0, 12) else if w < 4256 then if w < 4244 then (6, 4) else (1, 12) else if w < 4260 then (9, 5) else (2, 12) else if w < 4496 then if w < 4368 then if w < 4320 then if w < 4288 then (3, 12) else if w < 4289 then (24, 6) else (13, 6) else if w < 4360 then if w < 4354 then (10, 5) else (20, 8) else if w < 4362 then (7, 8) else (3, 8) else if w < 4392 then if w < 4370 then (7, 4) else if w < 4384 then (4, 12) else (11, 5) else if w < 4416 then if w < 4400 then (4, 3) else (8, 4) else if w < 4480 then (25, 6) else (29, 7) else if w < 4616 then if w < 4609 then if w < 4512 then (0, 4) else if w < 4544 then (12, 5) else (26, 6) else if w < 4612 then if w < 4610 then (27, 9) else (23, 9) else if w < 4614 then (18, 9) else (16, 9) else if w < 4626 then if w < 4624 then if w < 4620 then (11, 9) else (5, 9) else if w < 4625 then (6, 9) else (0, 9) else if w < 4672 then if w < 4628 then (1, 9) else (2, 9) else if w < 4673 then (18, 6) else (5, 6) else if w < 5378 then if w < 5128 then if w < 4872 then if w < 4744 then if w < 4736 then (2, 6) else if w < 4737 then (30, 7) else (15, 7) else if w < 4864 then if w < 4752 then (4, 7) else (1, 4) else if w < 4866 then (34, 8) else (21, 8) else if w < 5121 then if w < 4928 then (8, 8) else if w < 4992 then (19, 6) else (31, 7) else if w < 5123 then if w < 5122 then (33, 10) else (35, 10) else if w < 5124 then (28, 10) else (30, 10) else if w < 5186 then if w < 5132 then if w < 5129 then (25, 10) else if w < 5130 then (19, 10) else (22, 10) else if w < 5137 then if w < 5136 then (15, 10) else (9, 10) else if w < 5184 then (12, 10) else (20, 6) else if w < 5252 then if w < 5248 then if w < 5188 then (3, 6) else (4, 10) else if w < 5249 then (23, 7) else (16, 7) else if w < 5312 then if w < 5264 then (1, 7) else (2, 4) else if w < 5376 then (21, 6) else (35, 8) else if w < 6240 then if w < 6160 then if w < 6145 then if w < 5392 then (22, 8) else if w < 5440 then (3, 4) else (22, 6) else if w < 6152 then if w < 6148 then (32, 11) else (34, 11) else if w < 6153 then (29, 11) else (31, 11) else if w < 6177 then if w < 6164 then if w < 6161 then (24, 11) else (26, 11) else if w < 6176 then (21, 11) else (17, 11) else if w < 6208 then if w < 6192 then (10, 11) else (13, 11) else if w < 6212 then (14, 6) else (8, 11) else if w < 6660 then if w < 6432 then if w < 6400 then (13, 5) else if w < 6408 then (27, 8) else (0, 8) else if w < 6656 then if w < 6464 then (5, 5) else (15, 6) else if w < 6657 then (33, 9) else (28, 9) else if w < 7172 then if w < 6720 then if w < 6664 then (19, 9) else (12, 9) else if w < 7168 then (16, 6) else (32, 10) else if w < 7184 then if w < 7176 then (31, 10) else (26, 10) else if w < 7424 then (10, 10) else (28, 8)

private def checked (w : BitVec 13) : Bool :=
  let (i, r) := pick w.toNat
  let entry := table.getD i.rev.val 0
  (List.finRange 13).all fun x =>
    (entry.testBit (x - r).val == w.getLsbD x.val) &&
      (entry.testBit (13 + (x - r).val) == freeCheck false w x)

private def row (w : BitVec 13) : Bool :=
  if countBits w = 3 ∨ countBits w = 4 then !arcCheck false w || checked w else true

set_option maxRecDepth 60000 in
set_option maxHeartbeats 75000000 in
private theorem certificate : ∀ w : BitVec 13, row w = true := by
  decide +kernel

private theorem fromCheck (S : Finset (Fin 13))
    (size : S.card = 3 ∨ S.card = 4)
    (arc : ∀ x, (S.filter (fun y => hit false x y)).card ≤ 2) :
    ∃ n ∈ table, ∃ r : Fin 13,
      (∀ p : Fin 13, n.testBit (p-r).val = decide (p ∈ S)) ∧
      ∀ l : Fin 13, n.testBit (13 + (l-r).val) = decide (∀ p ∈ S, ¬hit false l p) := by
  let w := encode S
  have hw : countBits w = 3 ∨ countBits w = 4 := by
    simpa only [w, countBitsEncode] using size
  have ha := arcMatches false S arc
  have c := certificate w
  have hh : checked w = true := by
    simpa only [row, ite_eq_left hw, w, ha, Bool.not_true, Bool.false_or] using c
  let i : Fin 36 := (pick w.toNat).1.rev
  let r : Fin 13 := (pick w.toNat).2
  let n := table.getD i.val 0
  have hn : n ∈ table := by
    have hl : i.val < table.length := tableLength.symm ▸ i.isLt
    change table.getD i.val 0 ∈ table
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem (l := table) hl
  have hf (x : Fin 13) : ((n.testBit (x-r).val == w.getLsbD x.val) &&
      (n.testBit (13 + (x-r).val) == freeCheck false w x)) = true := by
    apply List.all_eq_true.mp hh x (by simp)
  have freeEq (x : Fin 13) : freeCheck false w x = decide (∀ p ∈ S, ¬hit false x p) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    refine ⟨offMatches false S x, ?_⟩
    intro h
    apply List.all_eq_true.mpr
    intro y hy
    have absent : y ∉ S := fun hm => h y hm ((neighborsSpec false x y).mp hy)
    rw [show w.getLsbD y.val = decide (y ∈ S) from encodeBit S y, decide_eq_false absent]
    rfl
  refine ⟨n, hn, r, fun p => ?_, fun l => ?_⟩
  · exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp (hf p)).1).trans (encodeBit S p)
  · exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp (hf l)).2).trans (freeEq l)

end PEqualNP.Outside.L_meta_18637

open PEqualNP.Outside.L_meta_18637 in
theorem PEqualNP.Outside.L_meta_18637 : have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (3 : ℕ) ∨ x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x2}.card ≤ (2 : ℕ)) → ∃ x6 ∈ x1, ∃ (x7 : Fin (13 : ℕ)), (∀ (x8 : Fin (13 : ℕ)), x6.testBit ↑(x8 - x7) = Decidable.decide (x8 ∈ x3)) ∧ ∀ (x8 : Fin (13 : ℕ)), x6.testBit ((13 : ℕ) + ↑(x8 - x7)) = Decidable.decide (∀ x9 ∈ x3, x9 - x8 ∉ x2) := by
  dsimp only
  intro S size arc
  obtain ⟨n, hn, r, h⟩ := fromCheck S size arc
  have hTable : n ∈ writtenTable.toFinset := by
    rw [← writtenAgreement]
    exact List.mem_toFinset.mpr hn
  exact ⟨n, List.mem_toFinset.mp hTable, r, h⟩

