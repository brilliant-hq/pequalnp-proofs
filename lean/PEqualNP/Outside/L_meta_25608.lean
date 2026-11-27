import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25608

abbrev ev5 (t0 t1 t2 t3 t4 k : Bool) : Bool :=
  xor (xor (xor (xor t0 t1) t2) (!(xor (xor t1 t2) t3) && xor (xor t2 t3) t4)) k

abbrev Tp (u1 u2 u3 j2 j1 j0 a b c : Bool) : Prop :=
  ∃ c0 c1 c2 : Bool, (u1 = true → ev5 false false false false c0 j2 = a) ∧
    (u2 = true → ev5 false false false c0 c1 j1 = b) ∧
    (u3 = true → ev5 false false c0 c1 c2 j0 = c)

abbrev Gx (o : Nat) (j6 j5 j4 j3 a b c k : Bool) : Bool :=
  match o with
  | 0 => ev5 j6 j5 j4 j3 a k
  | 1 => ev5 j5 j4 j3 a b k
  | _ => ev5 j4 j3 a b c k

abbrev Fp (o : Nat) (u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k : Bool) : Prop :=
  ∀ a b c : Bool, Tp u1 u2 u3 j2 j1 j0 a b c →
    Gx o j6 j5 j4 j3 a b c k = Gx o j6 j5 j4 j3 j2 j1 j0 k

abbrev Ef (j5 j4 j3 j2 j1 : Bool) : Int :=
  if xor (xor j5 j4) j3 then (if (xor j4 j3 == !j2) && (j4 == j1) then -4 else -5) else -6

abbrev Rv (u2 j5 j4 j3 j2 j1 : Bool) : Int :=
  if (u2 = false ∧ xor (xor j5 j4) j3 = true) then -5 else Ef j5 j4 j3 j2 j1

abbrev Core (u1 u2 u3 : Bool) : Prop :=
  ∀ j6 j5 j4 j3 j2 j1 j0 k5 k4 k3 : Bool,
    (¬ Fp 0 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k5 → -6 = Rv u2 j5 j4 j3 j2 j1) ∧
    (Fp 0 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k5 → ¬ Fp 1 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k4 → -5 = Rv u2 j5 j4 j3 j2 j1) ∧
    (Fp 0 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k5 → Fp 1 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k4 →
      ¬ Fp 2 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k3 → -4 = Rv u2 j5 j4 j3 j2 j1) ∧
    ¬ (Fp 0 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k5 ∧ Fp 1 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k4 ∧
      Fp 2 u1 u2 u3 j6 j5 j4 j3 j2 j1 j0 k3)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core000 : Core false false false := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core100 : Core true false false := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core110 : Core true true false := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core111 : Core true true true := by decide +kernel

theorem coreAll (w : Nat) : Core (decide (1 ≤ w)) (decide (2 ≤ w)) (decide (3 ≤ w)) := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ 3 ≤ w by omega) with rfl | rfl | rfl | h
  · exact core000
  · exact core100
  · exact core110
  · rw [decide_eq_true (show 1 ≤ w by omega), decide_eq_true (show 2 ≤ w by omega),
      decide_eq_true h]
    exact core111

def mixF (x : Int → Bool) (z : Int) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evolveF (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (injection z)

theorem ev_eq (x inj : Int → Bool) (z : Int) :
    evolveF x inj z = ev5 (x (z-1)) (x z) (x (z+1)) (x (z+2)) (x (z+3)) (inj z) := by
  have h1 : z + 1 - 1 = z := by ring
  have h2 : z + 1 + 1 = z + 2 := by ring
  have h3 : z + 2 - 1 = z + 1 := by ring
  have h4 : z + 2 + 1 = z + 3 := by ring
  simp only [evolveF, mixF, ev5, h1, h2, h3, h4]

theorem evolve_congr {x x' inj inj' : Int → Bool} {z : Int}
    (h : ∀ s, z - 1 ≤ s → s ≤ z + 3 → x s = x' s) (hi : inj z = inj' z) :
    evolveF x inj z = evolveF x' inj' z := by
  rw [ev_eq, ev_eq, h (z-1) (by omega) (by omega), h z (by omega) (by omega),
    h (z+1) (by omega) (by omega), h (z+2) (by omega) (by omega),
    h (z+3) (by omega) (by omega), hi]

theorem phys_congr {x x' J J' K K' : Int → Bool} {j : Int}
    (hx : ∀ s, j - 2 ≤ s → s ≤ j + 6 → x s = x' s)
    (hJ : ∀ s, j - 1 ≤ s → s ≤ j + 3 → J s = J' s) (hK : K j = K' j) :
    evolveF (evolveF x J) K j = evolveF (evolveF x' J') K' j := by
  apply evolve_congr _ hK
  intro s h1 h2
  exact evolve_congr (fun t t1 t2 => hx t (by omega) (by omega)) (hJ s h1 h2)

def win (lo : Int) (v : List Bool) (s : Int) : Bool :=
  if lo ≤ s then v.getD (s - lo).toNat false else false

def winJ (J : Int → Bool) : Int → Bool :=
  win (-8) [J (-8), J (-7), J (-6), J (-5), J (-4), J (-3), J (-2), J (-1), J 0]

theorem winJ_eq (J : Int → Bool) (s : Int) (h1 : -8 ≤ s) (h2 : s ≤ 0) : winJ J s = J s := by
  interval_cases s <;> rfl

theorem win_neg (lo : Int) (v : List Bool) (s : Int) (h : s < lo) : win lo v s = false := by
  simp only [win]
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

abbrev P1 (j : Int) : Prop := ∀ a b j8 j7 j6 j5 j4 j3 j2 j1 j0 k : Bool,
  j ≤ Ef j5 j4 j3 j2 j1 →
  evolveF (evolveF (win 1 [a, b]) (win (-8) [j8, j7, j6, j5, j4, j3, j2, j1, j0])) (fun _ => k) j =
  evolveF (evolveF (fun _ => false) (win (-8) [j8, j7, j6, j5, j4, j3, j2, j1, j0]))
    (fun _ => k) j

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p1a : P1 (-6) := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p1b : P1 (-5) := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p1c : P1 (-4) := by decide +kernel

abbrev P2 : Prop := ∀ j8 j7 j6 j5 j4 j3 j2 j1 j0 k : Bool, ∃ a b c : Bool,
  evolveF (evolveF (win 1 [a, b, c]) (win (-8) [j8, j7, j6, j5, j4, j3, j2, j1, j0]))
    (fun _ => k) (Ef j5 j4 j3 j2 j1 + 1) ≠
  evolveF (evolveF (fun _ => false) (win (-8) [j8, j7, j6, j5, j4, j3, j2, j1, j0]))
    (fun _ => k) (Ef j5 j4 j3 j2 j1 + 1)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p2 : P2 := by decide +kernel

theorem Ef_range (j5 j4 j3 j2 j1 : Bool) : -6 ≤ Ef j5 j4 j3 j2 j1 ∧ Ef j5 j4 j3 j2 j1 ≤ -4 := by
  unfold Ef
  split_ifs <;> norm_num

theorem part1 (J K x : Int → Bool) (hx : ∀ j ≤ (0:Int), x j = false) (j : Int)
    (hj : j ≤ Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1))) :
    evolveF (evolveF x J) K j = evolveF (evolveF (fun _ => false) J) K j := by
  by_cases h7 : j ≤ -7
  · exact phys_congr (fun s _ h2 => hx s (by omega)) (fun _ _ _ => rfl) rfl
  · have hE := Ef_range (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1))
    have hrange : j = -6 ∨ j = -5 ∨ j = -4 := by omega
    have e1 : evolveF (evolveF x J) K j =
        evolveF (evolveF (win 1 [x 1, x 2]) (winJ J)) (fun _ => K j) j := by
      apply phys_congr _ (fun s h1 h2 => (winJ_eq J s (by omega) (by omega)).symm) rfl
      intro s h1 h2
      rcases (show s ≤ 0 ∨ s = 1 ∨ s = 2 by omega) with h | rfl | rfl
      · rw [hx s h, win_neg _ _ _ (by omega)]
      · rfl
      · rfl
    have e2 : evolveF (evolveF (fun _ => false) J) K j =
        evolveF (evolveF (fun _ => false) (winJ J)) (fun _ => K j) j :=
      phys_congr (fun _ _ _ => rfl) (fun s h1 h2 => (winJ_eq J s (by omega) (by omega)).symm) rfl
    rw [e1, e2]
    rcases hrange with rfl | rfl | rfl
    · exact p1a (x 1) (x 2) (J (-8)) (J (-7)) (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2))
        (J (-1)) (J 0) (K (-6)) hj
    · exact p1b (x 1) (x 2) (J (-8)) (J (-7)) (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2))
        (J (-1)) (J 0) (K (-5)) hj
    · exact p1c (x 1) (x 2) (J (-8)) (J (-7)) (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2))
        (J (-1)) (J 0) (K (-4)) hj

theorem part2 (J K : Int → Bool) : ∃ x : Int → Bool, (∀ j ≤ (0:Int), x j = false) ∧
    evolveF (evolveF x J) K (Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) + 1) ≠
    evolveF (evolveF (fun _ => false) J) K (Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) + 1) := by
  obtain ⟨a, b, c, h⟩ := p2 (J (-8)) (J (-7)) (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2))
    (J (-1)) (J 0) (K (Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) + 1))
  refine ⟨win 1 [a, b, c], fun j hj => win_neg _ _ _ (by omega), ?_⟩
  have hE := Ef_range (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1))
  rw [phys_congr (x' := win 1 [a, b, c]) (J' := winJ J)
      (K' := fun _ => K (Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) + 1))
      (fun _ _ _ => rfl) (fun s h1 h2 => (winJ_eq J s (by omega) (by omega)).symm) rfl,
    phys_congr (x' := fun _ => false) (J' := winJ J)
      (K' := fun _ => K (Ef (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) + 1))
      (fun _ _ _ => rfl) (fun s h1 h2 => (winJ_eq J s (by omega) (by omega)).symm) rfl]
  exact h

def blockF (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0

def tailsF (w admit : Nat) : List Nat :=
  (List.range (2 ^ (2*w+5))).filter (fun pattern => admit.testBit (pattern % 2^w))

def trialF (x : Int → Bool) (b : Int) (completionCode : Nat) (site : Int) : Bool :=
  if site ≤ b then x site else completionCode.testBit (site-b-1).toNat

def fixedF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) (offset : Nat) : Bool :=
  (tailsF w admit).all (fun comparisonCode =>
    evolveF (trialF x b comparisonCode) inj (b-2+(offset : Int)) ==
      evolveF x inj (b-2+(offset : Int)))

def edgeF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) : Int :=
  b-3+(((List.range (w+5)).takeWhile (fixedF w b x inj admit)).length : Int)

def advF (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) : Int × Nat :=
  (edgeF w b x inj admit, (tailsF w admit).foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< blockF w (evolveF (trialF x b outputCode) inj)
      (edgeF w b x inj admit))) 0)

theorem fixed_iff (w : Nat) (b : Int) (x inj : Int → Bool) (A o : Nat) :
    fixedF w b x inj A o = true ↔ ∀ p, p < 2 ^ (2*w+5) → A.testBit (p % 2^w) = true →
      evolveF (trialF x b p) inj (b-2+(o:Int)) = evolveF x inj (b-2+(o:Int)) := by
  simp only [fixedF, tailsF, List.all_eq_true, List.mem_filter, List.mem_range, beq_iff_eq,
    and_imp]

theorem fold_bit (l : List Nat) (f : Nat → Nat) (acc n : Nat) :
    (l.foldl (fun a p => a ||| ((1 : Nat) <<< f p)) acc).testBit n =
      (acc.testBit n || l.any (fun p => decide (f p = n))) := by
  induction l generalizing acc with
  | nil => simp
  | cons p t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.any_cons, Bool.or_assoc]

theorem snd_bit (w : Nat) (b : Int) (x inj : Int → Bool) (A n : Nat) :
    (advF w b x inj A).2.testBit n = true ↔ ∃ p, p < 2 ^ (2*w+5) ∧ A.testBit (p % 2^w) = true ∧
      blockF w (evolveF (trialF x b p) inj) (edgeF w b x inj A) = n := by
  simp only [advF, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq, tailsF, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, h3⟩
    exact ⟨p, h1, h2, h3⟩
  · rintro ⟨p, h1, h2, h3⟩
    exact ⟨p, ⟨h1, h2⟩, h3⟩

theorem block_succ (w : Nat) (t : Int → Bool) (e : Int) :
    blockF (w+1) t e = blockF w t e ||| ((t (e+1+(w:Int))).toNat <<< w) := by
  simp only [blockF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_bit (w : Nat) (t : Int → Bool) (e : Int) (i : Nat) :
    (blockF w t e).testBit i = (decide (i < w) && t (e+1+(i:Int))) := by
  induction w with
  | zero => simp [blockF]
  | succ w ih =>
    rw [block_succ, Nat.testBit_or, ih]
    rcases lt_trichotomy i w with h | rfl | h
    · cases t (e+1+(w:Int)) <;> simp [Nat.testBit_shiftLeft, h, show i < w + 1 by omega] <;> omega
    · cases t (e+1+(i:Int)) <;> simp [Nat.testBit_shiftLeft]
    · cases t (e+1+(w:Int)) <;>
        simp [Nat.one_shiftLeft, Nat.testBit_two_pow, show ¬ i < w by omega,
          show ¬ i < w + 1 by omega, show w ≠ i by omega]

theorem block_lt (w : Nat) (t : Int → Bool) (e : Int) : blockF w t e < 2 ^ w := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [block_bit]
  simp [show ¬ i < w by omega]

theorem blk_bits {w p : Nat} {t : Int → Bool} {e : Int} (h : blockF w t e = p % 2 ^ w)
    (i : Nat) (hi : i < w) : t (e+1+(i:Int)) = p.testBit i := by
  have := congrArg (fun n => n.testBit i) h
  simpa only [block_bit, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] using this

theorem N32 (w : Nat) : 32 ≤ 2 ^ (2*w+5) := by
  calc 32 = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ (2*w+5) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem A0_bit (w p : Nat) : (2 ^ (2 ^ w) - 1).testBit (p % 2 ^ w) = true := by
  rw [Nat.testBit_two_pow_sub_one]
  simp [Nat.mod_lt _ (Nat.two_pow_pos w)]

theorem one_edge (w : Nat) (J : Int → Bool) :
    edgeF w 0 (fun _ => false) J (2 ^ (2 ^ w) - 1) = -3 := by
  have hf : fixedF w 0 (fun _ => false) J (2 ^ (2 ^ w) - 1) 0 = false := by
    rw [← Bool.not_eq_true, fixed_iff]
    intro h
    have := h 1 (by have := N32 w; omega) (A0_bit w 1)
    rw [ev_eq, ev_eq] at this
    norm_num [trialF, ev5] at this
  unfold edgeF
  rw [List.range_eq_range', show w + 5 = (w + 4) + 1 from rfl, List.range'_succ,
    List.takeWhile_cons, hf]
  simp

theorem X0_eq (J : Int → Bool) (s : Int) : evolveF (fun _ => false) J s = J s := by
  rw [ev_eq]
  simp [ev5]

theorem bridgeG (J K : Int → Bool) (p o : Nat) (ho : o ≤ 2) :
    evolveF (trialF (evolveF (fun _ => false) J) (-3) p) K (-3-2+(o:Int)) =
      Gx o (J (-6)) (J (-5)) (J (-4)) (J (-3)) (p.testBit 0) (p.testBit 1) (p.testBit 2)
        (K (-3-2+(o:Int))) ∧
    evolveF (evolveF (fun _ => false) J) K (-3-2+(o:Int)) =
      Gx o (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) (J 0) (K (-3-2+(o:Int))) := by
  interval_cases o <;> refine ⟨?_, ?_⟩ <;> rw [ev_eq] <;> norm_num [trialF, X0_eq, Gx]

theorem Y_bridge (J : Int → Bool) (p : Nat) :
    evolveF (trialF (fun _ => false) 0 p) J (-2) =
      ev5 false false false false (p.testBit 0) (J (-2)) ∧
    evolveF (trialF (fun _ => false) 0 p) J (-1) =
      ev5 false false false (p.testBit 0) (p.testBit 1) (J (-1)) ∧
    evolveF (trialF (fun _ => false) 0 p) J 0 =
      ev5 false false (p.testBit 0) (p.testBit 1) (p.testBit 2) (J 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ev_eq] <;> norm_num [trialF]

theorem T_iff (w : Nat) (J : Int → Bool) (a b c : Bool) :
    (∃ p, p < 2 ^ (2*w+5) ∧
      (advF w 0 (fun _ => false) J (2 ^ (2 ^ w) - 1)).2.testBit (p % 2^w) = true ∧
      p.testBit 0 = a ∧ p.testBit 1 = b ∧ p.testBit 2 = c) ↔
    Tp (decide (1 ≤ w)) (decide (2 ≤ w)) (decide (3 ≤ w)) (J (-2)) (J (-1)) (J 0) a b c := by
  constructor
  · rintro ⟨p, hp, hM, ha, hb, hc⟩
    rw [snd_bit, one_edge] at hM
    obtain ⟨q, -, -, hblk⟩ := hM
    obtain ⟨y2, y1, y0⟩ := Y_bridge J q
    refine ⟨q.testBit 0, q.testBit 1, q.testBit 2, ?_, ?_, ?_⟩
    · intro hw
      have h := blk_bits hblk 0 (by simp at hw; omega)
      rw [show (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 by norm_num, y2] at h
      rw [h, ha]
    · intro hw
      have h := blk_bits hblk 1 (by simp at hw; omega)
      rw [show (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 by norm_num, y1] at h
      rw [h, hb]
    · intro hw
      have h := blk_bits hblk 2 (by simp at hw; omega)
      rw [show (-3 : Int) + 1 + ((2 : Nat) : Int) = 0 by norm_num, y0] at h
      rw [h, hc]
  · rintro ⟨c0, c1, c2, h0, h1, h2⟩
    obtain ⟨q, qb0, qb1, qb2, q8⟩ : ∃ q : Nat, q.testBit 0 = c0 ∧ q.testBit 1 = c1 ∧
        q.testBit 2 = c2 ∧ q < 8 :=
      ⟨c0.toNat + 2 * c1.toNat + 4 * c2.toNat, by cases c0 <;> cases c1 <;> cases c2 <;> decide⟩
    obtain ⟨p0, pb0, pb1, pb2, p8⟩ : ∃ q : Nat, q.testBit 0 = a ∧ q.testBit 1 = b ∧
        q.testBit 2 = c ∧ q < 8 :=
      ⟨a.toNat + 2 * b.toNat + 4 * c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩
    obtain ⟨y2, y1, y0⟩ := Y_bridge J q
    simp only [qb0, qb1, qb2] at y2 y1 y0
    have hrl := block_lt w (evolveF (trialF (fun _ => false) 0 q) J) (-3)
    have hbit := block_bit w (evolveF (trialF (fun _ => false) 0 q) J) (-3)
    refine ⟨2 ^ w * (p0 / 2 ^ w) + blockF w (evolveF (trialF (fun _ => false) 0 q) J) (-3),
      ?_, ?_, ?_, ?_, ?_⟩
    · have hd : p0 / 2 ^ w ≤ 7 := le_trans (Nat.div_le_self _ _) (by omega)
      have hm : 2 ^ w * (p0 / 2 ^ w) ≤ 2 ^ w * 7 := Nat.mul_le_mul_left _ hd
      have h8 : 2 ^ w * 8 ≤ 2 ^ (2*w+5) := by
        rw [show 2*w+5 = w + (w+5) by ring, pow_add]
        apply Nat.mul_le_mul_left
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (w+5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      linarith
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrl, snd_bit, one_edge]
      exact ⟨q, by have := N32 w; omega, A0_bit w q, rfl⟩
    · rw [Nat.testBit_two_pow_mul_add _ hrl]
      split_ifs with hi
      · rw [hbit, decide_eq_true hi, Bool.true_and,
          show (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 by norm_num, y2]
        exact h0 (by simp; omega)
      · rw [Nat.testBit_div_two_pow, show 0 - w + w = 0 by omega]
        exact pb0
    · rw [Nat.testBit_two_pow_mul_add _ hrl]
      split_ifs with hi
      · rw [hbit, decide_eq_true hi, Bool.true_and,
          show (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 by norm_num, y1]
        exact h1 (by simp; omega)
      · rw [Nat.testBit_div_two_pow, show 1 - w + w = 1 by omega]
        exact pb1
    · rw [Nat.testBit_two_pow_mul_add _ hrl]
      split_ifs with hi
      · rw [hbit, decide_eq_true hi, Bool.true_and,
          show (-3 : Int) + 1 + ((2 : Nat) : Int) = 0 by norm_num, y0]
        exact h2 (by simp; omega)
      · rw [Nat.testBit_div_two_pow, show 2 - w + w = 2 by omega]
        exact pb2

theorem tw3 (w : Nat) (f : Nat → Bool) (h : ¬ (f 0 = true ∧ f 1 = true ∧ f 2 = true)) :
    (((List.range (w+5)).takeWhile f).length : Int) =
      if f 0 = false then 0 else if f 1 = false then 1 else 2 := by
  rw [List.range_eq_range', show w + 5 = (w + 2) + 1 + 1 + 1 from rfl, List.range'_succ,
    List.range'_succ, List.range'_succ]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> simp_all [List.takeWhile_cons]

theorem finish (f : Nat → Bool) (P0 P1 P2 : Prop) (R : Int) (F0 : f 0 = true ↔ P0)
    (F1 : f 1 = true ↔ P1) (F2 : f 2 = true ↔ P2) (c0 : ¬P0 → -6 = R)
    (c1 : P0 → ¬P1 → -5 = R) (c2 : P0 → P1 → ¬P2 → -4 = R) (c3 : ¬(P0 ∧ P1 ∧ P2)) (w : Nat) :
    (-3 : Int) - 3 + (((List.range (w+5)).takeWhile f).length : Int) = R := by
  rw [tw3 w f (fun ⟨a0, a1, a2⟩ => c3 ⟨F0.1 a0, F1.1 a1, F2.1 a2⟩)]
  by_cases g0 : P0
  · have e0 : f 0 = true := F0.2 g0
    by_cases g1 : P1
    · have e1 : f 1 = true := F1.2 g1
      by_cases g2 : P2
      · exact absurd ⟨g0, g1, g2⟩ c3
      · have e2 : f 2 = false := Bool.eq_false_iff.mpr (fun h => g2 (F2.1 h))
        simp only [e0, e1, e2]
        rw [← c2 g0 g1 g2]
        norm_num
    · have e1 : f 1 = false := Bool.eq_false_iff.mpr (fun h => g1 (F1.1 h))
      simp only [e0, e1]
      rw [← c1 g0 g1]
      norm_num
  · have e0 : f 0 = false := Bool.eq_false_iff.mpr (fun h => g0 (F0.1 h))
    simp only [e0]
    rw [← c0 g0]
    norm_num

theorem two_edge (w : Nat) (J K : Int → Bool) :
    edgeF w (-3) (evolveF (fun _ => false) J) K
      (advF w 0 (fun _ => false) J (2 ^ (2 ^ w) - 1)).2 =
      Rv (decide (2 ≤ w)) (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1)) := by
  have hF : ∀ o, o ≤ 2 → (fixedF w (-3) (evolveF (fun _ => false) J) K
      (advF w 0 (fun _ => false) J (2 ^ (2 ^ w) - 1)).2 o = true ↔
      Fp o (decide (1 ≤ w)) (decide (2 ≤ w)) (decide (3 ≤ w)) (J (-6)) (J (-5)) (J (-4))
        (J (-3)) (J (-2)) (J (-1)) (J 0) (K (-3-2+(o:Int)))) := by
    intro o ho
    rw [fixed_iff]
    constructor
    · intro h a b c hT
      obtain ⟨p, hp, hM, ha, hb, hc⟩ := (T_iff w J a b c).2 hT
      have := h p hp hM
      rw [(bridgeG J K p o ho).1, (bridgeG J K p o ho).2, ha, hb, hc] at this
      exact this
    · intro h p hp hM
      rw [(bridgeG J K p o ho).1, (bridgeG J K p o ho).2]
      exact h _ _ _ ((T_iff w J _ _ _).1 ⟨p, hp, hM, rfl, rfl, rfl⟩)
  obtain ⟨c0, c1, c2, c3⟩ := coreAll w (J (-6)) (J (-5)) (J (-4)) (J (-3)) (J (-2)) (J (-1))
    (J 0) (K (-3-2+((0:Nat):Int))) (K (-3-2+((1:Nat):Int))) (K (-3-2+((2:Nat):Int)))
  unfold edgeF
  exact finish _ _ _ _ _ (hF 0 (by norm_num)) (hF 1 (by norm_num)) (hF 2 (by norm_num))
    c0 c1 c2 c3 w

theorem Rv_eq (w : Nat) (j5 j4 j3 j2 j1 : Bool) :
    Rv (decide (2 ≤ w)) j5 j4 j3 j2 j1 =
      if w < 2 ∧ xor (xor j5 j4) j3 = true then (-5 : Int) else Ef j5 j4 j3 j2 j1 := by
  unfold Rv
  apply if_congr _ rfl rfl
  rw [decide_eq_false_iff_not, not_le]

end PEqualNP.Outside.L_meta_25608

open PEqualNP.Outside.L_meta_25608 in
theorem PEqualNP.Outside.L_meta_25608 :
    let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let evolve := fun (x injection : Int → Bool) (z : Int) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
    let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
      (List.range width).foldl (fun (number bitIndex : Nat) =>
        number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
    let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
      (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
    let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (admit : Nat) =>
      let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => admit.testBit (pattern % 2^w))
      let trial := fun (completionCode : Nat) (site : Int) =>
        if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
      let reference := evolve x inj
      let fixed := fun (offset : Nat) =>
        let site := b-2+(offset : Int)
        tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
      let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
      let newMask := tails.foldl (fun acc outputCode =>
        acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
      (newEdge, newMask)
    ∀ (first second : Int → Bool),
      let flat : Int → Bool := fun _ => false
      let admissible := fun (x : Int → Bool) => ∀ j ≤ (0 : Int), x j = false
      let physical := fun (x : Int → Bool) => evolve (evolve x first) second
      let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
      let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
        (first (-4) == first (-1))
      let E : Int := if guard then (if hidden then -4 else -5) else -6
      (∀ x, admissible x → ∀ j ≤ E, physical x j = physical flat j) ∧
      (∃ x, admissible x ∧ physical x (E+1) ≠ physical flat (E+1)) ∧
      (∀ w : Nat,
        let allWords := 2^(2^w) - 1
        let one := advance w 0 flat first allWords
        let two := advance w one.1 (evolve flat first) second one.2
        one.1 = -3 ∧
        two.1 = (if w < 2 ∧ guard = true then (-5 : Int) else E)) := by
  intro mix evolve block fits advance first second flat admissible physical guard hidden E
  refine ⟨?_, ?_, ?_⟩
  · intro x hx j hj
    exact part1 first second x hx j hj
  · exact part2 first second
  · intro w allWords one two
    refine ⟨one_edge w first, ?_⟩
    show (advF w (advF w 0 (fun _ => false) first (2 ^ (2 ^ w) - 1)).1
      (evolveF (fun _ => false) first) second
      (advF w 0 (fun _ => false) first (2 ^ (2 ^ w) - 1)).2).1 =
        (if w < 2 ∧ guard = true then (-5 : Int) else E)
    rw [show (advF w 0 (fun _ => false) first (2 ^ (2 ^ w) - 1)).1 = -3 from one_edge w first]
    exact (two_edge w first second).trans (Rv_eq w _ _ _ _ _)
