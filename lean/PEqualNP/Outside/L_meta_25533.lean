import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25514

namespace PEqualNP.Outside.L_meta_25533_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0

def constW (k j : Nat) : Nat := 3 ^ (k + j) % 2 ^ k

def state1 (k u key : Nat) : Nat → Nat
  | 0 => rot k 1 key ^^^ u
  | t + 1 =>
      let prev := state1 k u key t
      step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
        rot k (2 * t) key ^^^ constW k (t + 1)

def state2 (k r v key : Nat) : Nat → Nat
  | 0 => rot k 3 key ^^^ v
  | t + 1 =>
      let prev := state2 k r v key t
      step k (prev ^^^ rot k 2 prev ^^^ rot k (k - 2) prev) ^^^
        rot k (3 * (t + 1) + 1) key ^^^ constW k (r + (t + 1))

def before1 (k r u i key : Nat) : Bool :=
  let prev := state1 k u key (r - 1)
  (step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev)).testBit i

def guardAt (k r u i key t δ : Nat) : Bool :=
  let z := state1 k u key (t - 1)
  let b := i + 3 * (r - t) + k - δ
  xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k))) (z.testBit ((b + 2) % k))

def keyOfStart (k u st : Nat) : Nat := rot k (k - 1) (st ^^^ u)

def testWord (k r u v key : Nat) : Bool :=
  let h := (k + 1) / 2
  decide (state1 k u key r < 2 ^ (k - h)) && decide (state2 k r v key r < 2 ^ (k - h))

def writeBit (w p : Nat) (b : Bool) : Nat :=
  if b then w ||| (1 <<< p) else w

lemma xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

lemma testBit_one_shiftLeft (p j : Nat) : (1 <<< p).testBit j = decide (j = p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hj : j < p
  · have h1 : ¬ (p ≤ j) := by omega
    have h2 : j ≠ p := by omega
    simp [h1, h2]
  · by_cases hjp : j = p
    · subst hjp; simp
    · have h1 : p ≤ j := by omega
      have h2 : j - p ≠ 0 := by omega
      have h3 : (1 : Nat).testBit (j - p) = false := by
        cases h : j - p with
        | zero => omega
        | succ m => simp [Nat.testBit_succ]
      simp [h1, hjp, h3]

lemma testBit_bool_toNat_shiftLeft (b : Bool) (m j : Nat) :
    (b.toNat <<< m).testBit j = (decide (j = m) && b) := by
  cases b
  · simp
  · simpa using testBit_one_shiftLeft m j

lemma nat_eq_of_testBit_lt (k a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : ∀ j < k, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))]

lemma rot_lt (k s w : Nat) : rot k s w < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)

lemma constW_lt (k j : Nat) : constW k j < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)

lemma keyOfStart_lt (k u st : Nat) : keyOfStart k u st < 2 ^ k := rot_lt k (k - 1) _

lemma writeBit_lt (k w p : Nat) (b : Bool) (hw : w < 2 ^ k) (hp : p < k) :
    writeBit w p b < 2 ^ k := by
  unfold writeBit
  cases b
  · exact hw
  · have h1 : 1 <<< p < 2 ^ k := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by omega) hp
    exact Nat.or_lt_two_pow hw h1

lemma testBit_writeBit (w p : Nat) (b : Bool) (hzero : w.testBit p = false) (j : Nat) :
    (writeBit w p b).testBit j = if j = p then b else w.testBit j := by
  unfold writeBit
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h : j = p
    · subst h; simp [hzero]
    · simp [h]
  · simp only [↓reduceIte]
    rw [Nat.testBit_or, testBit_one_shiftLeft]
    by_cases h : j = p
    · subst h; simp
    · simp [h]

lemma cancel_mod_add (k x y c : Nat) (hk : 0 < k) (h : (x + c) % k = (y + c) % k) :
    x % k = y % k := by
  have h1 : (x % k + c % k) % k = (y % k + c % k) % k := by
    rw [← Nat.add_mod, ← Nat.add_mod]; exact h
  have hx : x % k < k := Nat.mod_lt x hk
  have hy : y % k < k := Nat.mod_lt y hk
  have hc : c % k < k := Nat.mod_lt c hk
  have hcase : ∀ a < k, (a + c % k) % k = if a + c % k < k then a + c % k else a + c % k - k := by
    intro a ha
    by_cases hlt : a + c % k < k
    · simp [hlt, Nat.mod_eq_of_lt hlt]
    · simp only [hlt, ↓reduceIte]
      have hge : k ≤ a + c % k := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  rw [hcase (x % k) hx, hcase (y % k) hy] at h1
  split at h1 <;> split at h1 <;> omega

lemma testBit_rot (k s w j : Nat) (hw : w < 2 ^ k) (hj : j < k) :
    (rot k s w).testBit j = w.testBit ((j + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt s hk
  unfold rot
  rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hge : s % k ≤ j
  · have hhigh : k ≤ k - s % k + j := by omega
    have hhi0 : w.testBit (k - s % k + j) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hhigh))
    have hidx : (j + k - s % k) % k = j - s % k := by
      have : j + k - s % k = (j - s % k) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hge, Bool.true_and, hhi0, Bool.or_false, hidx]
  · have hlt : j < s % k := by omega
    have hidx : (j + k - s % k) % k = k - s % k + j := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [decide_eq_false hge, Bool.false_and, Bool.false_or, hidx]

lemma rot_inv_comp (k s w : Nat) (hk : 0 < k) (hw : w < 2 ^ k) :
    rot k (k - s % k) (rot k s w) = w := by
  apply nat_eq_of_testBit_lt k _ _ (rot_lt k _ _) hw
  intro j hj
  rw [testBit_rot k (k - s % k) (rot k s w) j (rot_lt k s w) hj,
      testBit_rot k s w _ hw (Nat.mod_lt _ hk)]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · simp [hs0, Nat.mod_eq_of_lt hj]
  · have hsub : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    have h1 : ((j + k - (k - s % k)) % k + k - s % k) % k = j := by
      have h2 : (j + k - (k - s % k)) % k = (j + s % k) % k := by congr 1; omega
      rw [h2]
      by_cases hlt : j + s % k < k
      · rw [Nat.mod_eq_of_lt hlt]
        have : j + s % k + k - s % k = j + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      · have h3 : (j + s % k) % k = j + s % k - k := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h3]
        have : j + s % k - k + k - s % k = j := by omega
        rw [this, Nat.mod_eq_of_lt hj]
    rw [h1]

lemma rot_comp_inv (k s w : Nat) (hk : 0 < k) (hw : w < 2 ^ k) :
    rot k s (rot k (k - s % k) w) = w := by
  apply nat_eq_of_testBit_lt k _ _ (rot_lt k _ _) hw
  intro j hj
  rw [testBit_rot k s (rot k (k - s % k) w) j (rot_lt k _ _) hj,
      testBit_rot k (k - s % k) w _ hw (Nat.mod_lt _ hk)]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · simp [hs0, Nat.mod_eq_of_lt hj]
  · have hsub : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    have h1 : ((j + k - s % k) % k + k - (k - s % k)) % k = j := by
      by_cases hlt : s % k ≤ j
      · have h2 : (j + k - s % k) % k = j - s % k := by
          have : j + k - s % k = (j - s % k) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h2]
        have : j - s % k + k - (k - s % k) = j := by omega
        rw [this, Nat.mod_eq_of_lt hj]
      · have h2 : (j + k - s % k) % k = j + k - s % k := Nat.mod_eq_of_lt (by omega)
        rw [h2]
        have : j + k - s % k + k - (k - s % k) = j + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    rw [h1]

lemma rot_inv_1 (k w : Nat) (hk : 2 ≤ k) (hw : w < 2 ^ k) :
    rot k (k - 1) (rot k 1 w) = w := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simpa [h1] using rot_inv_comp k 1 w (by omega) hw

lemma rot_1_inv (k w : Nat) (hk : 2 ≤ k) (hw : w < 2 ^ k) :
    rot k 1 (rot k (k - 1) w) = w := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simpa [h1] using rot_comp_inv k 1 w (by omega) hw

lemma foldl_or_bits (f : Nat → Bool) (m acc j : Nat) :
    ((List.range m).foldl (fun a b => a ||| ((f b).toNat <<< b)) acc).testBit j =
      (acc.testBit j || (decide (j < m) && f j)) := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.testBit_or, ih, testBit_bool_toNat_shiftLeft]
    by_cases hjm : j < m
    · have h1 : j < m + 1 := by omega
      have h2 : j ≠ m := by omega
      simp [hjm, h1, h2]
    · by_cases heq : j = m
      · subst heq; simp
      · have h1 : ¬ (j < m + 1) := by omega
        simp [hjm, heq, h1]

lemma foldl_or_lt (k : Nat) (f : Nat → Bool) (m acc : Nat) (hm : m ≤ k) (hacc : acc < 2 ^ k) :
    (List.range m).foldl (fun a b => a ||| ((f b).toNat <<< b)) acc < 2 ^ k := by
  induction m generalizing acc with
  | zero => simpa using hacc
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih acc (by omega) hacc
    have hbit : (f m).toNat <<< m < 2 ^ k := by
      cases f m
      · simp
      · rw [Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact Nat.or_lt_two_pow hprev hbit

lemma step_lt (k w : Nat) : step k w < 2 ^ k :=
  foldl_or_lt k _ k 0 (Nat.le_refl k) (Nat.two_pow_pos k)

lemma testBit_step (k w j : Nat) (hj : j < k) :
    (step k w).testBit j =
      xor (w.testBit j) (!(w.testBit ((j + 1) % k)) && w.testBit ((j + 2) % k)) := by
  unfold step
  rw [foldl_or_bits]
  simp [hj]

lemma state1_lt (k u key t : Nat) (hu : u < 2 ^ k) : state1 k u key t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 1 key) hu
  | succ m =>
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k (2 * m) key)) (constW_lt k _)

lemma state2_lt (k r v key t : Nat) (hv : v < 2 ^ k) : state2 k r v key t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 3 key) hv
  | succ m =>
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k (3 * (m + 1) + 1) key))
      (constW_lt k _)

lemma state1_succ (k u key t : Nat) :
    state1 k u key (t + 1) =
      step k (state1 k u key t ^^^ rot k 1 (state1 k u key t) ^^^ rot k (k - 1) (state1 k u key t)) ^^^
        rot k (2 * t) key ^^^ constW k (t + 1) := rfl

lemma state1_eq_fold (k u key rounds : Nat) :
    state1 k u key rounds =
      (List.range rounds).foldl (fun prev t =>
        step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
          rot k (2 * t) key ^^^ constW k (t + 1)) (rot k 1 key ^^^ u) := by
  induction rounds with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    rfl

lemma state2_eq_fold (k r v key rounds : Nat) :
    state2 k r v key rounds =
      (List.range rounds).foldl (fun prev t =>
        step k (prev ^^^ rot k 2 prev ^^^ rot k (k - 2) prev) ^^^
          rot k (3 * (t + 1) + 1) key ^^^ constW k (r + (t + 1))) (rot k 3 key ^^^ v) := by
  induction rounds with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    rfl

lemma state1_keyOfStart_zero (k u st : Nat) (hk : 2 ≤ k) (hu : u < 2 ^ k) (hst : st < 2 ^ k) :
    state1 k u (keyOfStart k u st) 0 = st := by
  change rot k 1 (rot k (k - 1) (st ^^^ u)) ^^^ u = st
  rw [rot_1_inv k (st ^^^ u) hk (Nat.xor_lt_two_pow hst hu)]
  apply nat_eq_of_testBit_lt k _ _ (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hst hu) hu) hst
  intro j _
  rw [Nat.testBit_xor, Nat.testBit_xor]
  cases st.testBit j <;> cases u.testBit j <;> rfl

lemma keyOfStart_start (k u w : Nat) (hk : 2 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) :
    keyOfStart k u (rot k 1 w ^^^ u) = w := by
  unfold keyOfStart
  have hxu : (rot k 1 w ^^^ u) ^^^ u = rot k 1 w := by
    apply nat_eq_of_testBit_lt k _ _
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rot_lt k 1 w) hu) hu) (rot_lt k 1 w)
    intro j _
    rw [Nat.testBit_xor, Nat.testBit_xor]
    cases (rot k 1 w).testBit j <;> cases u.testBit j <;> rfl
  rw [hxu]
  exact rot_inv_1 k w hk hw

lemma lt_two_pow_sub_iff (k h w : Nat) (hh : h ≤ k) (hw : w < 2 ^ k) :
    w < 2 ^ (k - h) ↔ ∀ j, k - h ≤ j → j < k → w.testBit j = false := by
  constructor
  · intro hlt j hj1 _
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hj1))
  · intro hall
    have heq : w = w % 2 ^ (k - h) := by
      apply nat_eq_of_testBit_lt k w (w % 2 ^ (k - h)) hw
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega)))
      intro j hj
      rw [Nat.testBit_mod_two_pow]
      by_cases hjm : j < k - h
      · simp [hjm]
      · simp [hjm, hall j (by omega) hj]
    rw [heq]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma testBit_mix (k w base x : Nat) (hk : 2 ≤ k) (hw : w < 2 ^ k) (hx : 1 ≤ x) :
    (w ^^^ rot k 1 w ^^^ rot k (k - 1) w).testBit ((base + x) % k) =
      xor (xor (w.testBit ((base + x) % k)) (w.testBit ((base + (x - 1)) % k)))
          (w.testBit ((base + (x + 1)) % k)) := by
  have hq : (base + x) % k < k := Nat.mod_lt _ (by omega)
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot k 1 w _ hw hq, testBit_rot k (k - 1) w _ hw hq]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hk1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, hk1]
  have hm : ((base + x) % k + k - 1) % k = (base + (x - 1)) % k := by
    have hadd : (((base + x) % k + k - 1) + 1) % k = ((base + (x - 1)) + 1) % k := by
      have hl : (base + x) % k + k - 1 + 1 = (base + x) % k + k := by omega
      have hr : base + (x - 1) + 1 = base + x := by omega
      rw [hl, hr, Nat.add_mod_right, Nat.mod_mod]
    exact cancel_mod_add k _ _ 1 (by omega) hadd
  have hp : ((base + x) % k + k - (k - 1)) % k = (base + (x + 1)) % k := by
    have hsub : (base + x) % k + k - (k - 1) = (base + x) % k + 1 := by omega
    rw [hsub, Nat.mod_add_mod, Nat.add_assoc]
  rw [hm, hp]

lemma step_left_lin_xor (k w1 w2 base x : Nat) (hk : 2 ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hx : 1 ≤ x)
    (h0 : w1.testBit ((base + x) % k) = w2.testBit ((base + x) % k))
    (h1 : w1.testBit ((base + (x + 1)) % k) = w2.testBit ((base + (x + 1)) % k))
    (h2 : w1.testBit ((base + (x + 2)) % k) = w2.testBit ((base + (x + 2)) % k))
    (h3 : w1.testBit ((base + (x + 3)) % k) = w2.testBit ((base + (x + 3)) % k)) :
    let l1 := w1 ^^^ rot k 1 w1 ^^^ rot k (k - 1) w1
    let l2 := w2 ^^^ rot k 1 w2 ^^^ rot k (k - 1) w2
    xor ((step k l1).testBit ((base + x) % k)) ((step k l2).testBit ((base + x) % k)) =
      xor (w1.testBit ((base + (x - 1)) % k)) (w2.testBit ((base + (x - 1)) % k)) := by
  intro l1 l2
  have hq : (base + x) % k < k := Nat.mod_lt _ (by omega)
  rw [testBit_step k l1 _ hq, testBit_step k l2 _ hq]
  have hq1 : ((base + x) % k + 1) % k = (base + (x + 1)) % k := by
    rw [Nat.mod_add_mod, Nat.add_assoc]
  have hq2 : ((base + x) % k + 2) % k = (base + (x + 2)) % k := by
    rw [Nat.mod_add_mod, Nat.add_assoc]
  rw [hq1, hq2]
  have hl1_1 : l1.testBit ((base + (x + 1)) % k) = l2.testBit ((base + (x + 1)) % k) := by
    dsimp only [l1, l2]
    rw [testBit_mix k w1 base (x + 1) hk hw1 (by omega),
        testBit_mix k w2 base (x + 1) hk hw2 (by omega)]
    simp only [Nat.add_sub_cancel, show x + 1 + 1 = x + 2 by omega]
    rw [h0, h1, h2]
  have hl1_2 : l1.testBit ((base + (x + 2)) % k) = l2.testBit ((base + (x + 2)) % k) := by
    dsimp only [l1, l2]
    rw [testBit_mix k w1 base (x + 2) hk hw1 (by omega),
        testBit_mix k w2 base (x + 2) hk hw2 (by omega)]
    simp only [show x + 2 - 1 = x + 1 by omega, show x + 2 + 1 = x + 3 by omega]
    rw [h1, h2, h3]
  rw [hl1_1, hl1_2]
  dsimp only [l1, l2]
  rw [testBit_mix k w1 base x hk hw1 hx, testBit_mix k w2 base x hk hw2 hx, h0, h1]
  cases w2.testBit ((base + x) % k) <;>
  cases w1.testBit ((base + (x - 1)) % k) <;>
  cases w2.testBit ((base + (x - 1)) % k) <;>
  cases w2.testBit ((base + (x + 1)) % k) <;>
  cases (l2.testBit ((base + (x + 1)) % k)) <;>
  cases (l2.testBit ((base + (x + 2)) % k)) <;> rfl

lemma key_rot_testBit_from_start (k u st1 st2 t base x : Nat) (hk : 2 ≤ k)
    (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k) (hx : 2 * t ≤ x + 1) :
    xor ((rot k (2 * t) (keyOfStart k u st1)).testBit ((base + x) % k))
        ((rot k (2 * t) (keyOfStart k u st2)).testBit ((base + x) % k)) =
      xor (st1.testBit ((base + (x + 1 - 2 * t)) % k))
          (st2.testBit ((base + (x + 1 - 2 * t)) % k)) := by
  have hq : (base + x) % k < k := Nat.mod_lt _ (by omega)
  have h1 : ∀ st < 2 ^ k, (rot k (2 * t) (keyOfStart k u st)).testBit ((base + x) % k) =
      xor (st.testBit ((base + (x + 1 - 2 * t)) % k)) (u.testBit ((base + (x + 1 - 2 * t)) % k)) := by
    intro st hst
    unfold keyOfStart
    rw [testBit_rot k (2 * t) _ _ (rot_lt k (k - 1) _) hq,
        testBit_rot k (k - 1) _ _ (Nat.xor_lt_two_pow hst hu) (Nat.mod_lt _ (by omega)),
        Nat.testBit_xor]
    have hk1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hk1]
    have hidx : (((base + x) % k + k - (2 * t) % k) % k + k - (k - 1)) % k =
        (base + (x + 1 - 2 * t)) % k := by
      have hsub : ((base + x) % k + k - (2 * t) % k) % k + k - (k - 1) =
          ((base + x) % k + k - (2 * t) % k) % k + 1 := by omega
      rw [hsub, Nat.mod_add_mod]
      have hlt : (2 * t) % k < k := Nat.mod_lt _ (by omega)
      have hadd : (((base + x) % k + k - (2 * t) % k + 1) + (2 * t) % k) % k =
          ((base + (x + 1 - 2 * t)) + (2 * t) % k) % k := by
        have hl : (base + x) % k + k - (2 * t) % k + 1 + (2 * t) % k = ((base + x) % k + 1) + k := by omega
        rw [hl, Nat.add_mod_right, Nat.mod_add_mod, Nat.add_mod_mod]
        congr 1; omega
      exact cancel_mod_add k _ _ ((2 * t) % k) (by omega) hadd
    rw [hidx]
  rw [h1 st1 hs1, h1 st2 hs2]
  cases st1.testBit ((base + (x + 1 - 2 * t)) % k) <;>
  cases st2.testBit ((base + (x + 1 - 2 * t)) % k) <;>
  cases u.testBit ((base + (x + 1 - 2 * t)) % k) <;> rfl

lemma state1_agree_start_window (k u base st1 st2 lo hi : Nat) (hk : 2 ≤ k)
    (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k)
    (hwin : ∀ x, lo ≤ x → x ≤ hi →
      st1.testBit ((base + x) % k) = st2.testBit ((base + x) % k)) :
    ∀ t x, lo + max t (2 * t - 3) ≤ x → x + 3 * t ≤ hi →
      (state1 k u (keyOfStart k u st1) t).testBit ((base + x) % k) =
      (state1 k u (keyOfStart k u st2) t).testBit ((base + x) % k) := by
  intro t
  induction t with
  | zero =>
    intro x hx1 hx2
    rw [state1_keyOfStart_zero k u st1 hk hu hs1, state1_keyOfStart_zero k u st2 hk hu hs2]
    exact hwin x (by omega) (by omega)
  | succ m ih =>
    intro x hx1 hx2
    have h1 := ih (x - 1) (by omega) (by omega)
    have h2 := ih x (by omega) (by omega)
    have h3 := ih (x + 1) (by omega) (by omega)
    have h4 := ih (x + 2) (by omega) (by omega)
    have h5 := ih (x + 3) (by omega) (by omega)
    have hst := step_left_lin_xor k
      (state1 k u (keyOfStart k u st1) m)
      (state1 k u (keyOfStart k u st2) m)
      base x hk (state1_lt k u _ m hu) (state1_lt k u _ m hu) (by omega)
      h2 h3 h4 h5
    rw [h1, Bool.xor_self] at hst
    have hst_eq := (xor_eq_false_iff _ _).mp hst
    have hky := key_rot_testBit_from_start k u st1 st2 m base x hk hu hs1 hs2 (by omega)
    have hkw := hwin (x + 1 - 2 * m) (by omega) (by omega)
    rw [hkw, Bool.xor_self] at hky
    have hky_eq := (xor_eq_false_iff _ _).mp hky
    rw [state1_succ k u _ m, state1_succ k u _ m, Nat.testBit_xor, Nat.testBit_xor,
        Nat.testBit_xor, Nat.testBit_xor, hst_eq, hky_eq]

lemma guardAt_linear_pivot (k r u i st1 st2 t δ : Nat)
    (ht5 : 5 ≤ t) (htr : t ≤ r) (hbound : 5 * t + δ ≤ k + 4)
    (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k)
    (hright : ∀ x, k + 6 - (5 * t + δ) ≤ x → x ≤ k - 1 →
      st1.testBit ((i + 3 * r + x) % k) = st2.testBit ((i + 3 * r + x) % k)) :
    xor (guardAt k r u i (keyOfStart k u st1) t δ)
        (guardAt k r u i (keyOfStart k u st2) t δ) =
      xor (st1.testBit ((i + 3 * r + (k + 5 - (5 * t + δ))) % k))
          (st2.testBit ((i + 3 * r + (k + 5 - (5 * t + δ))) % k)) := by
  have hk2 : 2 ≤ k := by omega
  let base := i + 3 * r
  let x0 := k - 3 * t - δ
  have hx0 : x0 = k - 3 * t - δ := rfl
  have hconv : ∀ d : Nat, d ≤ 2 →
      (i + 3 * (r - t) + k - δ + d) % k = (base + (x0 + d)) % k := by
    intro d hd
    dsimp only [base, x0]
    congr 1; omega
  have h0 : (i + 3 * (r - t) + k - δ) % k = (base + x0) % k := by
    simpa using hconv 0 (by omega)
  have h1 := hconv 1 (by omega)
  have h2 := hconv 2 (by omega)
  unfold guardAt
  dsimp only
  rw [h0, h1, h2]
  have a1 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright (t - 1) (x0 + 1) (by omega) (by omega)
  have a2 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright (t - 1) (x0 + 2) (by omega) (by omega)
  obtain ⟨m0, hm0⟩ : ∃ m0, t - 1 = m0 + 1 := ⟨t - 2, by omega⟩
  have bm1 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright m0 (x0 - 1) (by omega) (by omega)
  have b0 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright m0 x0 (by omega) (by omega)
  have b1 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright m0 (x0 + 1) (by omega) (by omega)
  have b2 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright m0 (x0 + 2) (by omega) (by omega)
  have b3 := state1_agree_start_window k u base st1 st2 (k + 6 - (5 * t + δ)) (k - 1) hk2 hu hs1 hs2
    hright m0 (x0 + 3) (by omega) (by omega)
  have hstep := step_left_lin_xor k (state1 k u (keyOfStart k u st1) m0)
    (state1 k u (keyOfStart k u st2) m0) base x0 hk2
    (state1_lt k u _ m0 hu) (state1_lt k u _ m0 hu) (by omega) b0 b1 b2 b3
  rw [bm1, Bool.xor_self] at hstep
  have hky := key_rot_testBit_from_start k u st1 st2 m0 base x0 hk2 hu hs1 hs2 (by omega)
  have hpiv_eq : x0 + 1 - 2 * m0 = k + 5 - (5 * t + δ) := by omega
  rw [hpiv_eq] at hky
  have hre : ∀ s1 s2 k1 k2 cc : Bool,
      xor (xor (xor s1 k1) cc) (xor (xor s2 k2) cc) = xor (xor s1 s2) (xor k1 k2) := by
    intro s1 s2 k1 k2 cc; cases s1 <;> cases s2 <;> cases k1 <;> cases k2 <;> cases cc <;> rfl
  have hz0 : xor ((state1 k u (keyOfStart k u st1) (t - 1)).testBit ((base + x0) % k))
                 ((state1 k u (keyOfStart k u st2) (t - 1)).testBit ((base + x0) % k)) =
             xor (st1.testBit ((base + (k + 5 - (5 * t + δ))) % k))
                 (st2.testBit ((base + (k + 5 - (5 * t + δ))) % k)) := by
    rw [hm0, state1_succ k u (keyOfStart k u st1) m0, state1_succ k u (keyOfStart k u st2) m0,
        Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hre, hstep, hky,
        Bool.false_xor]
  rw [← a1, ← a2]
  have hre3 : ∀ p1 p2 q1 q2 : Bool,
      xor (xor (xor p1 q1) q2) (xor (xor p2 q1) q2) = xor p1 p2 := by
    intro p1 p2 q1 q2; cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> rfl
  rw [hre3, hz0]

lemma tableIndex_lt : ∀ {n : Nat} (y : Fin n → Bool), tableIndex y < 2 ^ n
  | 0, _ => by simp [tableIndex]
  | n + 1, y => by
    unfold tableIndex
    rw [Fin.sum_univ_castSucc]
    have ih : (∑ i : Fin n, if y i.castSucc = true then 2 ^ i.val else 0) < 2 ^ n :=
      tableIndex_lt (fun i : Fin n => y i.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last]
    cases y (Fin.last n)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))
    · simp only [↓reduceIte]
      rw [Nat.pow_succ, Nat.mul_two]
      omega

lemma testBit_tableIndex : ∀ {n : Nat} (y : Fin n → Bool) (j : Nat) (hj : j < n),
    (tableIndex y).testBit j = y ⟨j, hj⟩
  | 0, _, _, hj => by omega
  | n + 1, y, j, hj => by
    unfold tableIndex
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlt : (∑ x : Fin n, if y x.castSucc = true then 2 ^ x.val else 0) < 2 ^ n :=
      tableIndex_lt (fun x : Fin n => y x.castSucc)
    have hadd_or : ∀ a < 2 ^ n, ∀ b : Bool,
        (a + if b = true then 2 ^ n else 0).testBit j =
          if j = n then b else a.testBit j := by
      intro a ha b
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        by_cases hjn : j = n
        · subst hjn; simp [Nat.testBit_lt_two_pow ha]
        · simp [hjn]
      · simp only [↓reduceIte]
        have hdisj : a + 2 ^ n = a ||| (1 <<< n) := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          apply nat_eq_of_testBit_lt (n + 1) _ _ (by rw [Nat.pow_succ, Nat.mul_two]; omega)
            (Nat.or_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
              (Nat.pow_lt_pow_right (by omega) (by omega)))
          intro t ht
          have h2n : (2 ^ n).testBit t = decide (t = n) := by
            simpa [Nat.shiftLeft_eq, Nat.one_mul] using testBit_one_shiftLeft n t
          rw [Nat.testBit_or, h2n]
          by_cases htn : t = n
          · subst htn
            rw [Nat.testBit_lt_two_pow ha, decide_eq_true rfl, Bool.false_or]
            have hdiv : (a + 2 ^ t) / 2 ^ t = 1 := by
              rw [Nat.add_div_right _ (Nat.two_pow_pos t), Nat.div_eq_of_lt ha]
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
          · have htlt : t < n := by omega
            rw [decide_eq_false htn, Bool.or_false]
            have hpow : 2 ^ n = 2 ^ t * 2 ^ (n - t) := by rw [← Nat.pow_add]; congr 1; omega
            have heven : 2 ^ (n - t) = 2 * 2 ^ (n - t - 1) := by
              rw [← Nat.pow_succ']; congr 1; omega
            have hdiv : (a + 2 ^ n) / 2 ^ t = a / 2 ^ t + 2 * 2 ^ (n - t - 1) := by
              rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos t), heven]
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, Nat.add_mod]
        rw [hdisj, Nat.testBit_or, testBit_one_shiftLeft]
        by_cases hjn : j = n
        · subst hjn; simp
        · simp [hjn]
    rw [hadd_or _ hlt (y (Fin.last n))]
    by_cases hjn : j = n
    · subst hjn
      simp only [↓reduceIte]
      congr 1
    · simp only [hjn, ↓reduceIte]
      have hrec := testBit_tableIndex (fun x : Fin n => y x.castSucc) j (by omega)
      simpa [tableIndex] using hrec

def weightN (N w : Nat) : Nat :=
  (List.range N).countP (fun j => w.testBit j)

def lowWeightSet (N D : Nat) : Finset (Fin (2 ^ N)) :=
  Finset.univ.filter (fun v => weightN N v.val ≤ D)

lemma weightN_succ (N w : Nat) :
    weightN (N + 1) w = weightN N w + (w.testBit N).toNat := by
  unfold weightN
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  cases w.testBit N <;> simp

lemma weightN_add_two_pow (N w : Nat) (hw : w < 2 ^ N) :
    weightN (N + 1) (w + 2 ^ N) = weightN N w + 1 := by
  rw [weightN_succ]
  have hbitN : (w + 2 ^ N).testBit N = true := by
    have hdiv : (w + 2 ^ N) / 2 ^ N = 1 := by
      rw [Nat.add_div_right _ (Nat.two_pow_pos N), Nat.div_eq_of_lt hw]
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  have hlow : ∀ j < N, (w + 2 ^ N).testBit j = w.testBit j := by
    intro j hj
    have hmod : (w + 2 ^ N) % 2 ^ N = w := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hw]
    have h1 := congrArg (fun n => n.testBit j) hmod
    rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and] at h1
    exact h1
  have hcnt : weightN N (w + 2 ^ N) = weightN N w := by
    unfold weightN
    apply List.countP_congr
    intro j hj
    rw [List.mem_range] at hj
    rw [hlow j hj]
  rw [hcnt, hbitN]; rfl

lemma card_lowWeightSet : ∀ (N D : Nat),
    (lowWeightSet N D).card = ∑ j ∈ Finset.range (D + 1), Nat.choose N j
  | 0, D => by
    have h1 : lowWeightSet 0 D = Finset.univ := by
      ext v; simp [lowWeightSet, weightN]
    rw [h1, Finset.card_univ, Fintype.card_fin]
    clear h1
    induction D with
    | zero => simp
    | succ d ih => rw [Finset.sum_range_succ, ← ih]; simp
  | N + 1, 0 => by
    have h1 : lowWeightSet (N + 1) 0 = {⟨0, Nat.two_pow_pos _⟩} := by
      ext v
      simp only [lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hw
        ext
        apply nat_eq_of_testBit_lt (N + 1) v.val 0 v.isLt (Nat.two_pow_pos _)
        intro j hj
        have h0 : (List.range (N + 1)).countP (fun b => v.val.testBit b) = 0 := by
          unfold weightN at hw; omega
        rw [List.countP_eq_zero] at h0
        have hf := h0 j (List.mem_range.mpr hj)
        cases hb : v.val.testBit j <;> simp [hb] at hf ⊢
      · intro hv; subst hv; simp [weightN]
    rw [h1, Finset.card_singleton]; simp
  | N + 1, d + 1 => by
    let S0 := (lowWeightSet (N + 1) (d + 1)).filter (fun v => v.val < 2 ^ N)
    let S1 := (lowWeightSet (N + 1) (d + 1)).filter (fun v => !(decide (v.val < 2 ^ N)))
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro v h0 h1
      simp only [S0, S1, Finset.mem_filter] at h0 h1
      simp [h0.2] at h1
    have hunion : S0 ∪ S1 = lowWeightSet (N + 1) (d + 1) := by
      ext v
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      by_cases h : v.val < 2 ^ N <;> simp [h]
    have hcard0 : S0.card = (lowWeightSet N (d + 1)).card := by
      symm
      apply Finset.card_bij (fun v _ => ⟨v.val, Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) (by omega))⟩)
      · intro v hv
        simp only [S0, lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        refine ⟨?_, v.isLt⟩
        rw [weightN_succ, Nat.testBit_lt_two_pow v.isLt]
        simpa using hv
      · intro v1 _ v2 _ h; exact Fin.ext (congrArg (fun x : Fin (2 ^ (N + 1)) => x.val) h)
      · intro v hv
        simp only [S0, lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨⟨v.val, hv.2⟩, ?_, Fin.ext rfl⟩
        simp only [lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hle := hv.1
        rw [weightN_succ, Nat.testBit_lt_two_pow hv.2] at hle
        simpa using hle
    have hcard1 : S1.card = (lowWeightSet N d).card := by
      symm
      apply Finset.card_bij (fun v _ => ⟨v.val + 2 ^ N, by rw [Nat.pow_succ, Nat.mul_two]; have := v.isLt; omega⟩)
      · intro v hv
        simp only [S1, lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        refine ⟨?_, by simp⟩
        rw [weightN_add_two_pow N v.val v.isLt]
        omega
      · intro v1 _ v2 _ h
        have hv : v1.val + 2 ^ N = v2.val + 2 ^ N := congrArg (fun x : Fin (2 ^ (N + 1)) => x.val) h
        exact Fin.ext (by omega)
      · intro v hv
        simp only [S1, lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and,
                   Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hv
        have hsub_lt : v.val - 2 ^ N < 2 ^ N := by
          have hpow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [Nat.pow_succ, Nat.mul_two]
          have := v.isLt; omega
        have heq : (v.val - 2 ^ N) + 2 ^ N = v.val := by omega
        refine ⟨⟨v.val - 2 ^ N, hsub_lt⟩, ?_, Fin.ext heq⟩
        simp only [lowWeightSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hle := hv.1
        rw [← heq, weightN_add_two_pow N _ hsub_lt] at hle
        omega
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hcard0, hcard1,
        card_lowWeightSet N (d + 1), card_lowWeightSet N d,
        Finset.sum_range_succ' (fun j => Nat.choose N j) (d + 1),
        Finset.sum_range_succ' (fun j => Nat.choose (N + 1) j) (d + 1),
        Nat.choose_zero_right, Nat.choose_zero_right]
    have hsum : (∑ j ∈ Finset.range (d + 1), Nat.choose N (j + 1)) +
        ∑ j ∈ Finset.range (d + 1), Nat.choose N j =
        ∑ j ∈ Finset.range (d + 1), Nat.choose (N + 1) (j + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.choose_succ_succ, Nat.add_comm]
    omega

lemma testBit_rot_inv (k s w t : Nat) (hk : 0 < k) (hw : w < 2 ^ k) (ht : t < k) :
    (rot k (k - s % k) w).testBit t = w.testBit ((s + t) % k) := by
  rw [testBit_rot k (k - s % k) w t hw ht]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · simp [hs0, Nat.mod_eq_of_lt ht]
    have h1 : (s + t) % k = t := by
      rw [Nat.add_mod, hs0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ht]
    rw [h1]
  · have hsub : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    have hidx : (t + k - (k - s % k)) % k = (s + t) % k := by
      have h1 : t + k - (k - s % k) = s % k + t := by omega
      rw [h1, Nat.mod_add_mod]
    rw [hidx]

def ordBase (r e q : Nat) : Nat := 3 * r - e - q - 1

def ordInit (k r e q raw : Nat) : Nat := rot k (ordBase r e q + q) raw

def ordStep (k r e q u stepIdx curW : Nat) : Nat :=
  let i := k - 1 - stepIdx
  let p := ordBase r e q + (q - 1 - stepIdx)
  writeBit curW p (xor (before1 k r u i curW) ((constW k r).testBit i))

def ordKey (k r e q u raw : Nat) : Nat → Nat
  | 0 => ordInit k r e q raw
  | j + 1 => ordStep k r e q u j (ordKey k r e q u raw j)

def reconstructOrd (k r e q u raw : Nat) : Nat := ordKey k r e q u raw q

lemma ordKey_lt (k r e q u raw : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) :
    ∀ j ≤ q, ordKey k r e q u raw j < 2 ^ k := by
  intro j
  induction j with
  | zero => intro _; exact rot_lt k _ _
  | succ j ih =>
    intro hj
    unfold ordKey ordStep
    dsimp only
    exact writeBit_lt k _ _ _ (ih (by omega)) (by unfold ordBase; omega)

lemma ordInit_extract (k r e q w : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) (hw : w < 2 ^ k) :
    let sh := ordBase r e q + q
    let raw := (rot k (k - sh % k) w) % 2 ^ (k - q)
    raw < 2 ^ (k - q) ∧
    ∀ pos < k, (ordInit k r e q raw).testBit pos =
      if ordBase r e q ≤ pos ∧ pos < ordBase r e q + q then false else w.testBit pos := by
  intro sh raw
  have hsh_lt : sh < k := by dsimp only [sh]; unfold ordBase; omega
  have hsh_mod : sh % k = sh := Nat.mod_eq_of_lt hsh_lt
  have hraw_lt : raw < 2 ^ (k - q) := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨hraw_lt, ?_⟩
  intro pos hpos
  unfold ordInit
  have hraw_ltk : raw < 2 ^ k :=
    Nat.lt_of_lt_of_le hraw_lt (Nat.pow_le_pow_right (by omega) (by omega))
  change (rot k sh raw).testBit pos = _
  rw [testBit_rot k sh raw pos hraw_ltk hpos, hsh_mod]
  dsimp only [raw]
  rw [Nat.testBit_mod_two_pow]
  by_cases hin : ordBase r e q ≤ pos ∧ pos < ordBase r e q + q
  · simp only [hin]
    have hge : k - q ≤ (pos + k - sh) % k := by
      have hlt : pos + k - sh < k := by dsimp only [sh]; omega
      rw [Nat.mod_eq_of_lt hlt]
      dsimp only [sh]; omega
    simp [show ¬ ((pos + k - sh) % k < k - q) by omega]
  · simp only [hin, ↓reduceIte]
    have hltq : (pos + k - sh) % k < k - q := by
      by_cases h1 : sh ≤ pos
      · have h2 : pos + k - sh = (pos - sh) + k := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        dsimp only [sh]; omega
      · have h2 : pos < ordBase r e q := by dsimp only [sh] at h1; omega
        rw [Nat.mod_eq_of_lt (by omega)]
        dsimp only [sh]; omega
    rw [decide_eq_true hltq, Bool.true_and,
        testBit_rot_inv k sh w _ (by omega) hw (Nat.mod_lt _ (by omega))]
    have hback : (sh + (pos + k - sh) % k) % k = pos := by
      rw [Nat.add_mod_mod]
      have h1 : sh + (pos + k - sh) = pos + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hpos]
    rw [hback]

lemma ord_or_exceptional (k r e q u w : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) (hu : u < 2 ^ k) (hw : w < 2 ^ k)
    (hpass : state1 k u w r < 2 ^ (k - (k + 1) / 2)) :
    (∃ raw : Fin (2 ^ (k - q)), reconstructOrd k r e q u raw.val = w) ∨
    (∃ idx < q, ∃ mask : Fin (2 ^ q),
      let i := k - 1 - idx
      before1 k r u i w ≠ before1 k r u i (w ^^^ rot k (i + 3 * r + k - e - q) mask.val)) := by
  let sh := ordBase r e q + q
  let rawNat := (rot k (k - sh % k) w) % 2 ^ (k - q)
  have hex := ordInit_extract k r e q w hq hr hkr hw
  dsimp only at hex
  have hraw_lt : rawNat < 2 ^ (k - q) := hex.1
  have hstep_ind : ∀ j ≤ q,
      (∀ pos < k, (ordKey k r e q u rawNat j).testBit pos =
        if ordBase r e q ≤ pos ∧ pos < ordBase r e q + (q - j) then false else w.testBit pos) ∨
      (∃ idx < q, ∃ mask : Fin (2 ^ q),
        let i := k - 1 - idx
        before1 k r u i w ≠ before1 k r u i (w ^^^ rot k (i + 3 * r + k - e - q) mask.val)) := by
    intro j
    induction j with
    | zero =>
      intro _
      left
      simpa [ordKey, sh, rawNat] using hex.2
    | succ j ih =>
      intro hjq
      rcases ih (by omega) with hinv | hexc
      · let i := k - 1 - j
        let p := ordBase r e q + (q - 1 - j)
        by_cases hbef : before1 k r u i w = before1 k r u i (ordKey k r e q u rawNat j)
        · left
          intro pos hpos
          unfold ordKey ordStep
          dsimp only
          have hp_zero : (ordKey k r e q u rawNat j).testBit p = false := by
            rw [hinv p (by dsimp only [p]; unfold ordBase; omega)]
            have hinp : ordBase r e q ≤ p ∧ p < ordBase r e q + (q - j) := by dsimp only [p]; omega
            simp [hinp]
          rw [testBit_writeBit _ p _ hp_zero pos]
          by_cases hpos_p : pos = p
          · subst hpos_p
            have hnotp : ¬ (ordBase r e q ≤ p ∧ p < ordBase r e q + (q - (j + 1))) := by dsimp only [p]; omega
            simp only [↓reduceIte, hnotp]
            have htop : (state1 k u w r).testBit i = false := by
              have hiff := (lt_two_pow_sub_iff k ((k + 1) / 2) (state1 k u w r) (by omega)
                (state1_lt k u w r hu)).mp hpass
              exact hiff i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
            have hr_eq : r = (r - 1) + 1 := by omega
            have hst_r : (state1 k u w r).testBit i =
                xor (xor (before1 k r u i w) ((rot k (2 * (r - 1)) w).testBit i))
                    ((constW k r).testBit i) := by
              conv_lhs => rw [hr_eq, state1_succ]
              rw [Nat.testBit_xor, Nat.testBit_xor]
              have h1 : r - 1 + 1 = r := by omega
              rw [h1]; rfl
            have hrot_i : (rot k (2 * (r - 1)) w).testBit i = w.testBit p := by
              rw [testBit_rot k (2 * (r - 1)) w i hw (by dsimp only [i]; omega)]
              have h2r : (2 * (r - 1)) % k = 2 * (r - 1) := Nat.mod_eq_of_lt (by omega)
              rw [h2r]
              have hidx : (i + k - 2 * (r - 1)) % k = p := by
                have h1 : i + k - 2 * (r - 1) = p + k := by
                  dsimp only [i, p]; unfold ordBase; omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p]; unfold ordBase; omega)]
              rw [hidx]
            rw [hst_r, hrot_i] at htop
            rw [← hbef]
            cases hb1 : before1 k r u i w <;> cases hwp : w.testBit p <;>
              cases hcr : (constW k r).testBit i <;> simp [hb1, hwp, hcr] at htop ⊢
          · simp only [hpos_p, ↓reduceIte, hinv pos hpos]
            by_cases hin : ordBase r e q ≤ pos ∧ pos < ordBase r e q + (q - (j + 1))
            · have hin' : ordBase r e q ≤ pos ∧ pos < ordBase r e q + (q - j) := by omega
              simp [hin, hin']
            · have hin' : ¬ (ordBase r e q ≤ pos ∧ pos < ordBase r e q + (q - j)) := by
                dsimp only [p] at hpos_p; omega
              simp [hin, hin']
        · right
          let shift := i + 3 * r + k - e - q
          let diff := w ^^^ ordKey k r e q u rawNat j
          have hdiff_lt : diff < 2 ^ k :=
            Nat.xor_lt_two_pow hw (ordKey_lt k r e q u rawNat hq hr hkr j (by omega))
          let maskNat := rot k (k - shift % k) diff
          have hmask_lt : maskNat < 2 ^ q := by
            have hiff := (lt_two_pow_sub_iff k (k - q) maskNat (by omega) (rot_lt k _ _)).mpr
            have hkq : k - (k - q) = q := by omega
            rw [hkq] at hiff
            apply hiff
            intro t ht1 ht2
            dsimp only [maskNat]
            rw [testBit_rot_inv k shift diff t (by omega) hdiff_lt ht2]
            dsimp only [diff]
            rw [Nat.testBit_xor, hinv _ (Nat.mod_lt _ (by omega))]
            have hout : ¬ (ordBase r e q ≤ (shift + t) % k ∧ (shift + t) % k < ordBase r e q + (q - j)) := by
              have hsum : shift + t = 2 * k + (ordBase r e q - j + t) := by
                dsimp only [shift, i]; unfold ordBase; omega
              have hmod : (shift + t) % k = (ordBase r e q - j + t) % k := by
                rw [hsum, show 2 * k + (ordBase r e q - j + t) = (ordBase r e q - j + t) + k * 2 by omega,
                    Nat.add_mul_mod_self_left]
              rw [hmod]
              by_cases hlt : ordBase r e q - j + t < k
              · rw [Nat.mod_eq_of_lt hlt]; unfold ordBase; omega
              · have hsub : (ordBase r e q - j + t) % k = ordBase r e q - j + t - k := by
                  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by unfold ordBase; omega)]
                rw [hsub]; unfold ordBase; omega
            simp only [hout, ↓reduceIte, Bool.xor_self]
          have hxor_eq : w ^^^ rot k shift maskNat = ordKey k r e q u rawNat j := by
            dsimp only [maskNat]
            rw [rot_comp_inv k shift diff (by omega) hdiff_lt]
            apply nat_eq_of_testBit_lt k _ _ (Nat.xor_lt_two_pow hw hdiff_lt)
              (ordKey_lt k r e q u rawNat hq hr hkr j (by omega))
            intro t _
            dsimp only [diff]
            rw [Nat.testBit_xor, Nat.testBit_xor]
            cases w.testBit t <;> cases (ordKey k r e q u rawNat j).testBit t <;> rfl
          refine ⟨j, by omega, ⟨maskNat, hmask_lt⟩, ?_⟩
          dsimp only
          change before1 k r u i w ≠ before1 k r u i (w ^^^ rot k shift maskNat)
          rw [hxor_eq]
          exact hbef
      · right; exact hexc
  rcases hstep_ind q (Nat.le_refl q) with hall | hexc
  · left
    refine ⟨⟨rawNat, hraw_lt⟩, ?_⟩
    apply nat_eq_of_testBit_lt k _ _ (ordKey_lt k r e q u rawNat hq hr hkr q (Nat.le_refl q)) hw
    intro pos hpos
    have h := hall pos hpos
    simp only [Nat.sub_self, Nat.add_zero] at h
    have hnot : ¬ (ordBase r e q ≤ pos ∧ pos < ordBase r e q) := by omega
    simp only [hnot, ↓reduceIte] at h
    exact h
  · right; exact hexc

def stopPosRec (m v : Nat) : Nat → Nat → Nat → Nat
  | 0, s, _ => s
  | fuel + 1, s, zeros =>
    let zeros' := if v.testBit s then zeros else zeros + 1
    if m ≤ zeros' then s + 1 else stopPosRec m v fuel (s + 1) zeros'

def stopPos (N m v : Nat) : Nat := stopPosRec m v N 0 0

def onesBefore (v s : Nat) : Nat := (List.range s).countP (fun j => v.testBit j)

def zerosBefore (v s : Nat) : Nat := (List.range s).countP (fun j => !(v.testBit j))

lemma ones_add_zeros (v s : Nat) : onesBefore v s + zerosBefore v s = s := by
  induction s with
  | zero => simp [onesBefore, zerosBefore]
  | succ s ih =>
    unfold onesBefore zerosBefore at ih ⊢
    rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_cons, List.countP_cons, List.countP_nil, List.countP_nil]
    cases v.testBit s <;> simp <;> omega

lemma onesBefore_succ (v s : Nat) :
    onesBefore v (s + 1) = onesBefore v s + (v.testBit s).toNat := by
  unfold onesBefore
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  cases v.testBit s <;> simp

lemma zerosBefore_succ (v s : Nat) :
    zerosBefore v (s + 1) = zerosBefore v s + (!(v.testBit s)).toNat := by
  unfold zerosBefore
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  cases v.testBit s <;> simp

lemma onesBefore_mono (v s1 s2 : Nat) (h : s1 ≤ s2) : onesBefore v s1 ≤ onesBefore v s2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [onesBefore_succ]; omega

lemma zerosBefore_mono (v s1 s2 : Nat) (h : s1 ≤ s2) : zerosBefore v s1 ≤ zerosBefore v s2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [zerosBefore_succ]; omega

lemma onesBefore_congr (v1 v2 s : Nat) (h : ∀ j < s, v1.testBit j = v2.testBit j) :
    onesBefore v1 s = onesBefore v2 s := by
  unfold onesBefore
  apply List.countP_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [h j hj]

lemma stopPosRec_props (m v : Nat) :
    ∀ fuel s,
      stopPosRec m v fuel s (zerosBefore v s) ≤ s + fuel ∧
      (zerosBefore v s < m → m ≤ zerosBefore v (s + fuel) →
        let a := stopPosRec m v fuel s (zerosBefore v s)
        s < a ∧ zerosBefore v a = m ∧ ∀ t < a, zerosBefore v t < m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    refine ⟨by simp [stopPosRec], fun h1 h2 => by simp at h2; omega⟩
  | succ fuel ih =>
    intro s
    unfold stopPosRec
    dsimp only
    have hz' : (if v.testBit s = true then zerosBefore v s else zerosBefore v s + 1) =
        zerosBefore v (s + 1) := by
      rw [zerosBefore_succ]; cases v.testBit s <;> simp
    rw [hz']
    by_cases hm : m ≤ zerosBefore v (s + 1)
    · simp only [hm, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      intro hlt _
      have heq : zerosBefore v (s + 1) = m := by
        have hzs := zerosBefore_succ v s
        cases hb : v.testBit s <;> simp [hb] at hzs hm ⊢ <;> omega
      refine ⟨by omega, heq, ?_⟩
      intro t ht
      have htle : t ≤ s := by omega
      exact Nat.lt_of_le_of_lt (zerosBefore_mono v t s htle) hlt
    · simp only [hm, ↓reduceIte]
      have hrec := ih (s + 1)
      have hle : stopPosRec m v fuel (s + 1) (zerosBefore v (s + 1)) ≤ s + 1 + fuel := hrec.1
      refine ⟨by omega, ?_⟩
      intro _ htot
      have hrec2 := hrec.2 (by omega) (by simpa [Nat.add_assoc, Nat.add_comm 1 fuel] using htot)
      dsimp only at hrec2 ⊢
      exact ⟨by omega, hrec2.2.1, hrec2.2.2⟩

lemma stopPos_props (N m v : Nat) (hm : 0 < m) (hwt : weightN N v + m ≤ N) :
    let a := stopPos N m v
    m ≤ a ∧ a ≤ N ∧ zerosBefore v a = m ∧ onesBefore v a + m = a ∧
    ∀ s < a, zerosBefore v s < m := by
  have hzN : m ≤ zerosBefore v N := by
    have h1 := ones_add_zeros v N
    have h2 : onesBefore v N = weightN N v := rfl
    omega
  have hp := stopPosRec_props m v N 0
  have hz0 : zerosBefore v 0 = 0 := by simp [zerosBefore]
  rw [hz0] at hp
  have h1 : stopPos N m v ≤ N := by simpa [stopPos] using hp.1
  have h2 := hp.2 hm (by simpa using hzN)
  dsimp only [stopPos] at h2 ⊢
  have hoz := ones_add_zeros v (stopPosRec m v N 0 0)
  have hma : m ≤ stopPosRec m v N 0 0 := by omega
  exact ⟨hma, h1, h2.2.1, by omega, h2.2.2⟩

lemma stopPosRec_congr (m v1 v2 : Nat) :
    ∀ fuel s zeros,
      (∀ j, s ≤ j → j < stopPosRec m v1 fuel s zeros → v1.testBit j = v2.testBit j) →
      stopPosRec m v1 fuel s zeros = stopPosRec m v2 fuel s zeros := by
  intro fuel
  induction fuel with
  | zero => intro s zeros _; rfl
  | succ fuel ih =>
    intro s zeros hagree
    unfold stopPosRec at hagree ⊢
    dsimp only at hagree ⊢
    have hs_lt : s < (if m ≤ (if v1.testBit s = true then zeros else zeros + 1)
        then s + 1 else stopPosRec m v1 fuel (s + 1)
          (if v1.testBit s = true then zeros else zeros + 1)) := by
      by_cases hm : m ≤ (if v1.testBit s = true then zeros else zeros + 1)
      · simp only [hm, ↓reduceIte]; omega
      · simp only [hm, ↓reduceIte]
        have hge : ∀ f s0 z0, s0 ≤ stopPosRec m v1 f s0 z0 := by
          intro f
          induction f with
          | zero => intro s0 z0; exact Nat.le_refl s0
          | succ f ihf =>
            intro s0 z0; unfold stopPosRec; dsimp only
            by_cases hm0 : m ≤ (if v1.testBit s0 = true then z0 else z0 + 1)
            · simp only [hm0, ↓reduceIte]; omega
            · simp only [hm0, ↓reduceIte]
              have := ihf (s0 + 1) (if v1.testBit s0 = true then z0 else z0 + 1); omega
        have := hge fuel (s + 1) (if v1.testBit s = true then zeros else zeros + 1); omega
    have hbit : v1.testBit s = v2.testBit s := hagree s (Nat.le_refl s) hs_lt
    rw [← hbit]
    by_cases hm : m ≤ (if v1.testBit s = true then zeros else zeros + 1)
    · simp only [hm, ↓reduceIte]
    · simp only [hm, ↓reduceIte]
      apply ih
      intro j hj1 hj2
      apply hagree j (by omega)
      simp only [hm, ↓reduceIte]; exact hj2

lemma stopPos_congr (N m v1 v2 : Nat)
    (h : ∀ j < stopPos N m v1, v1.testBit j = v2.testBit j) :
    stopPos N m v1 = stopPos N m v2 :=
  stopPosRec_congr m v1 v2 N 0 0 (fun j _ hj => h j hj)

def excDelta (e q v s : Nat) : Nat := (e + q - 1) - onesBefore v s

def excXPiv (k e q v s : Nat) : Nat := k + 5 - (5 * (e + q + 4 + s) + excDelta e q v s)

def excPivPos (k r e q i v s : Nat) : Nat := (i + 3 * r + excXPiv k e q v s) % k

def excPivList (k r e q i v a : Nat) : List Nat := (List.range a).map (excPivPos k r e q i v)

def excNonPivList (k r e q i v a : Nat) : List Nat :=
  (List.range k).filter (fun pos => !(excPivList k r e q i v a).contains pos)

def excDataBit (N v extra a idx : Nat) : Bool :=
  if idx < N - a then v.testBit (a + idx) else extra.testBit (idx - (N - a))

def excInitStart (k r e q i v extra : Nat) : Nat :=
  let N := (r - e) - (e + q + 3)
  let m := N - (e + q - 1)
  let a := stopPos N m v
  let np := excNonPivList k r e q i v a
  (List.range (k - a)).foldl (fun acc idx =>
    if excDataBit N v extra a idx then acc ||| (1 <<< np.getD idx 0) else acc) 0

def excStep (k r e q u i v s curSt : Nat) : Nat :=
  let t := e + q + 4 + s
  let δ := excDelta e q v s
  let p := excPivPos k r e q i v s
  let g := guardAt k r u i (keyOfStart k u curSt) t δ
  writeBit curSt p (xor g (v.testBit s))

def excState (k r e q u i v extra : Nat) : Nat → Nat
  | 0 => excInitStart k r e q i v extra
  | s + 1 => excStep k r e q u i v s (excState k r e q u i v extra s)

def reconstructExc (k r e q u i v extra : Nat) : Nat :=
  let N := (r - e) - (e + q + 3)
  let m := N - (e + q - 1)
  let a := stopPos N m v
  keyOfStart k u (excState k r e q u i v extra a)

lemma excXPiv_bounds (k r e q v s : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r)
    (hones : onesBefore v s ≤ e + q - 1)
    (hzeros : zerosBefore v s < ((r - e) - (e + q + 3)) - (e + q - 1)) :
    5 * (e + q + 4 + s) + excDelta e q v s ≤ k + 3 ∧
    2 ≤ excXPiv k e q v s ∧ excXPiv k e q v s < k := by
  have hoz := ones_add_zeros v s
  unfold excXPiv excDelta
  omega

lemma excXPiv_strict_dec (k r e q v s1 s2 : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) (hlt : s1 < s2)
    (hones2 : onesBefore v s2 ≤ e + q - 1)
    (hzeros2 : zerosBefore v s2 < ((r - e) - (e + q + 3)) - (e + q - 1)) :
    excXPiv k e q v s2 + 4 * (s2 - s1) ≤ excXPiv k e q v s1 := by
  have hones1 : onesBefore v s1 ≤ onesBefore v s2 := onesBefore_mono v s1 s2 (by omega)
  have hzeros1 : zerosBefore v s1 ≤ zerosBefore v s2 := zerosBefore_mono v s1 s2 (by omega)
  have hoz1 := ones_add_zeros v s1
  have hoz2 := ones_add_zeros v s2
  have hb1 := excXPiv_bounds k r e q v s1 hq hr hkr (by omega) (by omega)
  have hb2 := excXPiv_bounds k r e q v s2 hq hr hkr hones2 hzeros2
  unfold excXPiv excDelta at hb1 hb2 ⊢
  omega

lemma mod_ne_of_lt_k (k base x y : Nat) (hx : x < k) (hy : y < k) (hne : x ≠ y) :
    (base + x) % k ≠ (base + y) % k := by
  intro heq
  have h1 := cancel_mod_add k x y base (by omega) (by simpa [Nat.add_comm] using heq)
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
  exact hne h1

lemma excPivPos_inj (k r e q i v a : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r)
    (hones : onesBefore v a ≤ e + q - 1)
    (hzeros : ∀ s < a, zerosBefore v s < ((r - e) - (e + q + 3)) - (e + q - 1)) :
    ∀ s1 < a, ∀ s2 < a, excPivPos k r e q i v s1 = excPivPos k r e q i v s2 → s1 = s2 := by
  intro s1 hs1 s2 hs2 heq
  by_contra hne
  have h1 := excXPiv_bounds k r e q v s1 hq hr hkr
    (Nat.le_trans (onesBefore_mono v s1 a (by omega)) hones) (hzeros s1 hs1)
  have h2 := excXPiv_bounds k r e q v s2 hq hr hkr
    (Nat.le_trans (onesBefore_mono v s2 a (by omega)) hones) (hzeros s2 hs2)
  have hne_x : excXPiv k e q v s1 ≠ excXPiv k e q v s2 := by
    by_cases hlt : s1 < s2
    · have hd := excXPiv_strict_dec k r e q v s1 s2 hq hr hkr hlt
        (Nat.le_trans (onesBefore_mono v s2 a (by omega)) hones) (hzeros s2 hs2)
      omega
    · have hd := excXPiv_strict_dec k r e q v s2 s1 hq hr hkr (by omega)
        (Nat.le_trans (onesBefore_mono v s1 a (by omega)) hones) (hzeros s1 hs1)
      omega
  exact mod_ne_of_lt_k k (i + 3 * r) _ _ h1.2.2 h2.2.2 hne_x heq

lemma nodup_excPivList (k r e q i v a : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r)
    (hones : onesBefore v a ≤ e + q - 1)
    (hzeros : ∀ s < a, zerosBefore v s < ((r - e) - (e + q + 3)) - (e + q - 1)) :
    (excPivList k r e q i v a).Nodup := by
  unfold excPivList
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro s1 hs1 s2 hs2 heq
  rw [List.mem_range] at hs1 hs2
  exact excPivPos_inj k r e q i v a hq hr hkr hones hzeros s1 hs1 s2 hs2 heq

lemma length_excNonPivList (k r e q i v a : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r)
    (hones : onesBefore v a ≤ e + q - 1)
    (hzeros : ∀ s < a, zerosBefore v s < ((r - e) - (e + q + 3)) - (e + q - 1)) :
    (excNonPivList k r e q i v a).length = k - a := by
  have hnd_piv := nodup_excPivList k r e q i v a hq hr hkr hones hzeros
  have hnd_np : (excNonPivList k r e q i v a).Nodup := List.Nodup.filter _ List.nodup_range
  have hlen_piv : (excPivList k r e q i v a).length = a := by simp [excPivList]
  have hcard_np : (excNonPivList k r e q i v a).toFinset.card =
      (excNonPivList k r e q i v a).length := List.toFinset_card_of_nodup hnd_np
  have hcard_piv : (excPivList k r e q i v a).toFinset.card = a := by
    rw [List.toFinset_card_of_nodup hnd_piv, hlen_piv]
  have hsub : (excPivList k r e q i v a).toFinset ⊆ Finset.range k := by
    intro pos hpos
    rw [List.mem_toFinset] at hpos
    unfold excPivList at hpos
    rw [List.mem_map] at hpos
    rcases hpos with ⟨s, _, rfl⟩
    rw [Finset.mem_range]
    exact Nat.mod_lt _ (by omega)
  have hsdiff : (excNonPivList k r e q i v a).toFinset =
      Finset.range k \ (excPivList k r e q i v a).toFinset := by
    ext pos
    simp [excNonPivList, List.mem_toFinset]
  rw [← hcard_np, hsdiff, Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard_piv]

lemma foldl_or_pos_lt (k : Nat) (L : List Nat) (f : Nat → Bool) (m acc : Nat)
    (hL : ∀ j < m, L.getD j 0 < k) (hacc : acc < 2 ^ k) :
    (List.range m).foldl (fun a idx => if f idx then a ||| (1 <<< L.getD idx 0) else a) acc < 2 ^ k := by
  induction m generalizing acc with
  | zero => simpa using hacc
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih acc (fun j hj => hL j (by omega)) hacc
    cases f m
    · simpa using hprev
    · simp only [↓reduceIte]
      have hbit : 1 <<< L.getD m 0 < 2 ^ k := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by omega) (hL m (by omega))
      exact Nat.or_lt_two_pow hprev hbit

lemma foldl_or_pos_testBit (L : List Nat) (f : Nat → Bool) (m acc pos : Nat) :
    ((List.range m).foldl (fun a idx => if f idx then a ||| (1 <<< L.getD idx 0) else a) acc).testBit pos =
      (acc.testBit pos || (List.range m).any (fun idx => f idx && decide (pos = L.getD idx 0))) := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    cases hfm : f m
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.or_false]
      exact ih acc
    · simp only [↓reduceIte, Bool.true_and]
      rw [Nat.testBit_or, ih acc, testBit_one_shiftLeft, Bool.or_assoc]

lemma excInitStart_lt (k r e q i v extra : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) :
    excInitStart k r e q i v extra < 2 ^ k := by
  unfold excInitStart
  dsimp only
  apply foldl_or_pos_lt k _ _ _ 0
  · intro idx _
    by_cases hlt : idx < (excNonPivList k r e q i v (stopPos ((r - e) - (e + q + 3))
        (((r - e) - (e + q + 3)) - (e + q - 1)) v)).length
    · rw [List.getD_eq_getElem _ _ hlt]
      have hmem := List.getElem_mem hlt
      unfold excNonPivList at hmem
      rw [List.mem_filter, List.mem_range] at hmem
      exact hmem.1
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  · exact Nat.two_pow_pos k

lemma excState_lt (k r e q u i v extra : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) :
    ∀ s, excState k r e q u i v extra s < 2 ^ k := by
  intro s
  induction s with
  | zero => exact excInitStart_lt k r e q i v extra hq hr hkr
  | succ s ih =>
    unfold excState excStep
    dsimp only
    exact writeBit_lt k _ _ _ ih (Nat.mod_lt _ (by omega))

def maxF (d : Nat → Nat) (cut : Nat) : Nat → Nat
  | 0 => cut + d cut
  | s + 1 => max (maxF d cut s) (cut + (s + 1) + d (cut + (s + 1)))

lemma maxF_ge (d : Nat → Nat) (cut : Nat) :
    ∀ s t, t ≤ s → cut + t + d (cut + t) ≤ maxF d cut s := by
  intro s
  induction s with
  | zero =>
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0; exact Nat.le_refl _
  | succ s ih =>
    intro t ht
    unfold maxF
    by_cases hts : t ≤ s
    · exact Nat.le_trans (ih t hts) (Nat.le_max_left _ _)
    · have hteq : t = s + 1 := by omega
      subst hteq
      exact Nat.le_max_right _ _

lemma maxF_step_le (d : Nat → Nat) (cut s : Nat) (hdec : d (cut + (s + 1)) ≤ d (cut + s)) :
    maxF d cut (s + 1) ≤ maxF d cut s + 1 := by
  change max (maxF d cut s) (cut + (s + 1) + d (cut + (s + 1))) ≤ maxF d cut s + 1
  have h1 := maxF_ge d cut s s (Nat.le_refl s)
  exact max_le (by omega) (by omega)

lemma maxF_record_of_eq (d : Nat → Nat) (cut s : Nat)
    (heq : maxF d cut (s + 1) = maxF d cut s + 1) :
    cut + (s + 1) + d (cut + (s + 1)) = maxF d cut (s + 1) ∧
    ∀ t, cut ≤ t → t < cut + (s + 1) → t + d t < (cut + (s + 1)) + d (cut + (s + 1)) := by
  have h1 : cut + (s + 1) + d (cut + (s + 1)) = maxF d cut (s + 1) := by
    rw [heq]
    change max (maxF d cut s) (cut + (s + 1) + d (cut + (s + 1))) = maxF d cut s + 1 at heq
    rw [Nat.max_def] at heq
    split at heq <;> omega
  refine ⟨h1, ?_⟩
  intro t ht1 ht2
  have hle := maxF_ge d cut s (t - cut) (by omega)
  have hadd : cut + (t - cut) = t := by omega
  rw [hadd] at hle
  omega

def greedyPrefixRec (k r e q u i w : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, s, ones, acc =>
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let m := N - D
    if m ≤ s - ones then acc
    else
      let b := guardAt k r u i w (e + q + 4 + s) (D - ones)
      if b then greedyPrefixRec k r e q u i w fuel (s + 1) (ones + 1) (acc ||| (1 <<< s))
      else greedyPrefixRec k r e q u i w fuel (s + 1) ones acc

lemma greedyPrefixRec_testBit_lt (k r e q u i w : Nat) :
    ∀ fuel s ones acc j, j < s →
      (greedyPrefixRec k r e q u i w fuel s ones acc).testBit j = acc.testBit j := by
  intro fuel
  induction fuel with
  | zero => intro s ones acc j _; rfl
  | succ fuel ih =>
    intro s ones acc j hj
    unfold greedyPrefixRec
    dsimp only
    split
    · rfl
    · split
      · rw [ih (s + 1) (ones + 1) (acc ||| (1 <<< s)) j (by omega),
            Nat.testBit_or, testBit_one_shiftLeft, decide_eq_false (by omega), Bool.or_false]
      · exact ih (s + 1) ones acc j (by omega)

lemma greedyPrefixRec_lt (k r e q u i w : Nat) :
    ∀ fuel s ones acc, acc < 2 ^ s →
      greedyPrefixRec k r e q u i w fuel s ones acc < 2 ^ (s + fuel) := by
  intro fuel
  induction fuel with
  | zero => intro s ones acc hacc; simpa [greedyPrefixRec] using hacc
  | succ fuel ih =>
    intro s ones acc hacc
    unfold greedyPrefixRec
    dsimp only
    split
    · exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by omega) (by omega))
    · have hacc1 : acc < 2 ^ (s + 1) :=
        Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by omega) (by omega))
      split
      · have hor : acc ||| (1 <<< s) < 2 ^ (s + 1) := by
          apply Nat.or_lt_two_pow hacc1
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.pow_lt_pow_right (by omega) (by omega)
        have h := ih (s + 1) (ones + 1) (acc ||| (1 <<< s)) hor
        simpa [Nat.add_assoc, Nat.add_comm 1 fuel] using h
      · have h := ih (s + 1) ones acc hacc1
        simpa [Nat.add_assoc, Nat.add_comm 1 fuel] using h

lemma greedyPrefixRec_testBit_ge_stop (k r e q u i w : Nat) :
    ∀ fuel s ones acc,
      (∀ j ≥ s, acc.testBit j = false) →
      ones = onesBefore acc s →
      let res := greedyPrefixRec k r e q u i w fuel s ones acc
      (∀ j, s ≤ j → j < s + fuel →
        zerosBefore res j < ((r - e) - (e + q + 3)) - (e + q - 1) →
        res.testBit j = guardAt k r u i w (e + q + 4 + j) ((e + q - 1) - onesBefore res j)) ∧
      (∀ j, s + fuel ≤ j → res.testBit j = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s ones acc hge _
    exact ⟨fun j hj1 hj2 _ => by omega, fun j hj => hge j (by omega)⟩
  | succ fuel ih =>
    intro s ones acc hge hones
    unfold greedyPrefixRec
    dsimp only
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let m := N - D
    have hzs : zerosBefore acc s = s - ones := by
      have := ones_add_zeros acc s; omega
    by_cases hstop : ((r - e) - (e + q + 3)) - (e + q - 1) ≤ s - ones
    · simp only [hstop, ↓reduceIte]
      refine ⟨?_, fun j hj => hge j (by omega)⟩
      intro j hj1 _ hzlt
      have hmono := zerosBefore_mono acc s j hj1
      omega
    · simp only [hstop, ↓reduceIte]
      cases hb : guardAt k r u i w (e + q + 4 + s) (D - ones)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hge' : ∀ j ≥ s + 1, acc.testBit j = false := fun j hj => hge j (by omega)
        have hones' : ones = onesBefore acc (s + 1) := by
          rw [onesBefore_succ, hge s (Nat.le_refl s)]; simpa using hones
        have hrec := ih (s + 1) ones acc hge' hones'
        have hres_s : (greedyPrefixRec k r e q u i w fuel (s + 1) ones acc).testBit s = false := by
          rw [greedyPrefixRec_testBit_lt k r e q u i w fuel (s + 1) ones acc s (by omega)]
          exact hge s (Nat.le_refl s)
        have hones_res : onesBefore (greedyPrefixRec k r e q u i w fuel (s + 1) ones acc) s = ones := by
          rw [onesBefore_congr _ acc s (fun t ht =>
            greedyPrefixRec_testBit_lt k r e q u i w fuel (s + 1) ones acc t (by omega))]
          exact hones.symm
        refine ⟨?_, fun j hj => hrec.2 j (by omega)⟩
        intro j hj1 hj2 hzlt
        by_cases hjs : j = s
        · subst hjs
          rw [hres_s, hones_res]
          exact hb.symm
        · exact hrec.1 j (by omega) (by omega) hzlt
      · simp only [↓reduceIte]
        let acc' := acc ||| (1 <<< s)
        have hge' : ∀ j ≥ s + 1, acc'.testBit j = false := by
          intro j hj
          dsimp only [acc']
          rw [Nat.testBit_or, hge j (by omega), testBit_one_shiftLeft, decide_eq_false (by omega)]
          rfl
        have hones' : ones + 1 = onesBefore acc' (s + 1) := by
          rw [onesBefore_succ]
          have h1 : onesBefore acc' s = onesBefore acc s := by
            apply onesBefore_congr
            intro t ht
            dsimp only [acc']
            rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_false (by omega), Bool.or_false]
          have h2 : acc'.testBit s = true := by
            dsimp only [acc']
            rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_true rfl, Bool.or_true]
          rw [h1, h2, ← hones]; rfl
        have hrec := ih (s + 1) (ones + 1) acc' hge' hones'
        have hres_s : (greedyPrefixRec k r e q u i w fuel (s + 1) (ones + 1) acc').testBit s = true := by
          rw [greedyPrefixRec_testBit_lt k r e q u i w fuel (s + 1) (ones + 1) acc' s (by omega)]
          dsimp only [acc']
          rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_true rfl, Bool.or_true]
        have hones_res : onesBefore (greedyPrefixRec k r e q u i w fuel (s + 1) (ones + 1) acc') s = ones := by
          rw [onesBefore_congr _ acc s (fun t ht => by
            rw [greedyPrefixRec_testBit_lt k r e q u i w fuel (s + 1) (ones + 1) acc' t (by omega)]
            dsimp only [acc']
            rw [Nat.testBit_or, testBit_one_shiftLeft, decide_eq_false (by omega), Bool.or_false])]
          exact hones.symm
        refine ⟨?_, fun j hj => hrec.2 j (by omega)⟩
        intro j hj1 hj2 hzlt
        by_cases hjs : j = s
        · subst hjs
          rw [hres_s, hones_res]
          exact hb.symm
        · exact hrec.1 j (by omega) (by omega) hzlt

lemma greedy_reconstructs_exc (k r e q u i w : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) (hu : u < 2 ^ k) (hi : i < k) (hw : w < 2 ^ k)
    (d : Nat → Nat)
    (hd_lt : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q)
    (hd_dec : ∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1))
    (hd_guard : ∀ t, e + q + 3 < t → t ≤ r - e →
      (∀ s, e + q + 3 ≤ s → s < t → s + d s < t + d t) →
      guardAt k r u i w t (d t) = false) :
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    ∃ v : Fin (2 ^ N), v ∈ lowWeightSet N D ∧
      ∃ extra : Fin (2 ^ (k - N)), reconstructExc k r e q u i v.val extra.val = w := by
  intro N D
  let cut := e + q + 3
  let m := N - D
  have hm_pos : 0 < m := by dsimp only [m, N, D]; omega
  let v0 := greedyPrefixRec k r e q u i w N 0 0 0
  have hv0_spec := greedyPrefixRec_testBit_ge_stop k r e q u i w N 0 0 0
    (fun _ _ => by simp) (by simp [onesBefore])
  dsimp only at hv0_spec
  have hinv : ∀ s ≤ N,
      zerosBefore v0 s < m →
      onesBefore v0 s ≤ D ∧ maxF d cut s < (cut + 1 + s) + (D - onesBefore v0 s) := by
    intro s
    induction s with
    | zero =>
      intro _ _
      have h0 : onesBefore v0 0 = 0 := by simp [onesBefore]
      rw [h0]
      have hd0 : d cut < e + q := hd_lt cut (Nat.le_refl _) (by omega)
      unfold maxF
      dsimp only [D]
      omega
    | succ s ih =>
      intro hsN hzs1
      have hzs : zerosBefore v0 s < m :=
        Nat.lt_of_le_of_lt (zerosBefore_mono v0 s (s + 1) (by omega)) hzs1
      have hprev := ih (by omega) hzs
      have hbit := hv0_spec.1 s (Nat.zero_le s) (by omega) hzs
      have hdec_s : d (cut + (s + 1)) ≤ d (cut + s) := by
        have := hd_dec (cut + s + 1) (by omega) (by omega)
        simpa [Nat.add_assoc] using this
      have hm_le := maxF_step_le d cut s hdec_s
      by_cases heq_m : maxF d cut (s + 1) = (cut + 1 + s) + (D - onesBefore v0 s)
      · have hinc : maxF d cut (s + 1) = maxF d cut s + 1 := by omega
        have hrec := maxF_record_of_eq d cut s hinc
        have hd_eq : d (cut + (s + 1)) = D - onesBefore v0 s := by omega
        have hg_false : guardAt k r u i w (e + q + 4 + s) (D - onesBefore v0 s) = false := by
          have ht_eq : e + q + 4 + s = cut + (s + 1) := by dsimp only [cut]; omega
          rw [ht_eq, ← hd_eq]
          exact hd_guard (cut + (s + 1)) (by dsimp only [cut]; omega) (by dsimp only [cut, N] at *; omega)
            (fun t ht1 ht2 => hrec.2 t ht1 ht2)
        have hvs : v0.testBit s = false := by rw [hbit]; exact hg_false
        rw [onesBefore_succ, hvs]
        simp only [Bool.toNat_false, Nat.add_zero]
        exact ⟨hprev.1, by omega⟩
      · have hlt_m : maxF d cut (s + 1) < (cut + 1 + s) + (D - onesBefore v0 s) := by omega
        cases hvs : v0.testBit s
        · rw [onesBefore_succ, hvs]
          simp only [Bool.toNat_false, Nat.add_zero]
          exact ⟨hprev.1, by omega⟩
        · have hone_lt : onesBefore v0 s < D := by
            have hge := maxF_ge d cut (s + 1) (s + 1) (Nat.le_refl _)
            omega
          rw [onesBefore_succ, hvs]
          simp only [Bool.toNat_true]
          exact ⟨by omega, by omega⟩
  have hzN : m ≤ zerosBefore v0 N := by
    by_contra hlt
    have hlt' : zerosBefore v0 N < m := by omega
    have hN := hinv N (Nat.le_refl N) hlt'
    have hge := maxF_ge d cut N N (Nat.le_refl N)
    have hoz := ones_add_zeros v0 N
    dsimp only [cut, N, D, m] at hN hge hoz hlt'
    omega
  have hwt0 : weightN N v0 + m ≤ N := by
    have hoz := ones_add_zeros v0 N
    have h1 : onesBefore v0 N = weightN N v0 := rfl
    omega
  let a := stopPos N m v0
  have ha := stopPos_props N m v0 hm_pos hwt0
  dsimp only at ha
  have hones_a : onesBefore v0 a ≤ D := by
    change onesBefore v0 (stopPos N m v0) ≤ D
    dsimp only [m, N, D] at ha ⊢; omega
  let np := excNonPivList k r e q i v0 a
  have hnp_len : np.length = k - a :=
    length_excNonPivList k r e q i v0 a hq hr hkr hones_a ha.2.2.2.2
  have hnp_nd : np.Nodup := List.Nodup.filter _ List.nodup_range
  let stTrue := rot k 1 w ^^^ u
  have hstTrue_lt : stTrue < 2 ^ k := Nat.xor_lt_two_pow (rot_lt k 1 w) hu
  let suf := (List.range (N - a)).foldl (fun acc j =>
    if stTrue.testBit (np.getD j 0) then acc ||| (1 <<< (a + j)) else acc) 0
  let v1 := (v0 % 2 ^ a) ||| suf
  let extra1 := (List.range (k - N)).foldl (fun acc j =>
    if stTrue.testBit (np.getD (N - a + j) 0) then acc ||| (1 <<< j) else acc) 0
  have hsuf_bit : ∀ j, suf.testBit j =
      (decide (a ≤ j ∧ j < N) && stTrue.testBit (np.getD (j - a) 0)) := by
    intro j
    have hstep : ∀ len acc,
        ((List.range len).foldl (fun acc0 t =>
          if stTrue.testBit (np.getD t 0) then acc0 ||| (1 <<< (a + t)) else acc0) acc).testBit j =
        (acc.testBit j || (decide (a ≤ j ∧ j < a + len) && stTrue.testBit (np.getD (j - a) 0))) := by
      intro len
      induction len with
      | zero => intro acc; simp
      | succ len ih =>
        intro acc
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        cases hst : stTrue.testBit (np.getD len 0)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih acc]
          by_cases hjeq : j = a + len
          · subst hjeq
            rw [Nat.add_sub_cancel_left, hst, decide_eq_false (by omega), Bool.false_and,
                Bool.and_false, Bool.or_false]
          · have hiff : (a ≤ j ∧ j < a + (len + 1)) ↔ (a ≤ j ∧ j < a + len) := by omega
            simp [hiff]
        · simp only [↓reduceIte]
          rw [Nat.testBit_or, ih acc, testBit_one_shiftLeft]
          by_cases hjeq : j = a + len
          · subst hjeq
            have hdec : decide (a ≤ a + len ∧ a + len < a + (len + 1)) = true := decide_eq_true (by omega)
            rw [Nat.add_sub_cancel_left, hst, decide_eq_true rfl, Bool.or_true, hdec, Bool.and_true, Bool.or_true]
          · have hiff : (a ≤ j ∧ j < a + (len + 1)) ↔ (a ≤ j ∧ j < a + len) := by omega
            simp [hjeq, hiff]
    simpa [suf, show a + (N - a) = N by omega] using hstep (N - a) 0
  have hv1_lt : v1 < 2 ^ N := by
    have h1 : v0 % 2 ^ a < 2 ^ N :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos a)) (Nat.pow_le_pow_right (by omega) ha.2.1)
    have h2 : suf < 2 ^ N := by
      have hlt : ∀ len acc, a + len ≤ N → acc < 2 ^ N →
          (List.range len).foldl (fun acc0 t =>
            if stTrue.testBit (np.getD t 0) then acc0 ||| (1 <<< (a + t)) else acc0) acc < 2 ^ N := by
        intro len
        induction len with
        | zero => intro acc _ hacc; simpa using hacc
        | succ len ih =>
          intro acc hle hacc
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hprev := ih acc (by omega) hacc
          cases stTrue.testBit (np.getD len 0)
          · simpa using hprev
          · simp only [↓reduceIte]
            apply Nat.or_lt_two_pow hprev
            rw [Nat.shiftLeft_eq, Nat.one_mul]
            exact Nat.pow_lt_pow_right (by omega) (by omega)
      exact hlt (N - a) 0 (by omega) (Nat.two_pow_pos N)
    exact Nat.or_lt_two_pow h1 h2
  have hv1_agree_lt : ∀ j < a, v1.testBit j = v0.testBit j := by
    intro j hj
    dsimp only [v1]
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, hsuf_bit,
        decide_eq_false (by omega), Bool.false_and, Bool.or_false]
  have hv1_agree_ge : ∀ j < N - a, v1.testBit (a + j) = stTrue.testBit (np.getD j 0) := by
    intro j hj
    dsimp only [v1]
    have hltN : a + j < N := by omega
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, decide_eq_false (by omega), Bool.false_and,
        Bool.false_or, hsuf_bit]
    simp [hltN]
  have hextra_lt : extra1 < 2 ^ (k - N) := by
    have hlt : ∀ len acc, len ≤ k - N → acc < 2 ^ (k - N) →
        (List.range len).foldl (fun acc0 t =>
          if stTrue.testBit (np.getD (N - a + t) 0) then acc0 ||| (1 <<< t) else acc0) acc < 2 ^ (k - N) := by
      intro len
      induction len with
      | zero => intro acc _ hacc; simpa using hacc
      | succ len ih =>
        intro acc hle hacc
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hprev := ih acc (by omega) hacc
        cases stTrue.testBit (np.getD (N - a + len) 0)
        · simpa using hprev
        · simp only [↓reduceIte]
          apply Nat.or_lt_two_pow hprev
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact hlt (k - N) 0 (Nat.le_refl _) (Nat.two_pow_pos _)
  have hextra_bit : ∀ j < k - N, extra1.testBit j = stTrue.testBit (np.getD (N - a + j) 0) := by
    intro j hj
    have hstep : ∀ len acc,
        ((List.range len).foldl (fun acc0 t =>
          if stTrue.testBit (np.getD (N - a + t) 0) then acc0 ||| (1 <<< t) else acc0) acc).testBit j =
        (acc.testBit j || (decide (j < len) && stTrue.testBit (np.getD (N - a + j) 0))) := by
      intro len
      induction len with
      | zero => intro acc; simp
      | succ len ih =>
        intro acc
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        cases hst : stTrue.testBit (np.getD (N - a + len) 0)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih acc]
          by_cases hjeq : j = len
          · subst hjeq
            rw [hst, decide_eq_false (by omega), Bool.false_and, Bool.and_false, Bool.or_false]
          · have hiff : (j < len + 1) ↔ (j < len) := by omega
            simp [hiff]
        · simp only [↓reduceIte]
          rw [Nat.testBit_or, ih acc, testBit_one_shiftLeft]
          by_cases hjeq : j = len
          · subst hjeq
            have hdec : decide (j < j + 1) = true := decide_eq_true (by omega)
            rw [hst, decide_eq_true rfl, Bool.or_true, hdec, Bool.and_true, Bool.or_true]
          · have hiff : (j < len + 1) ↔ (j < len) := by omega
            simp [hjeq, hiff]
    simpa [extra1, hj] using hstep (k - N) 0
  have hwt1 : weightN N v1 ≤ D := by
    have hsplit : onesBefore v1 N ≤ onesBefore v1 a + (N - a) := by
      have hstep : ∀ d, onesBefore v1 (a + d) ≤ onesBefore v1 a + d := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [← Nat.add_assoc, onesBefore_succ]
          cases v1.testBit (a + d) <;> simp <;> omega
      simpa [show a + (N - a) = N by omega] using hstep (N - a)
    have h1 : onesBefore v1 a = onesBefore v0 a := onesBefore_congr v1 v0 a hv1_agree_lt
    have h2 : weightN N v1 = onesBefore v1 N := rfl
    change onesBefore v1 N ≤ onesBefore v1 (stopPos N m v0) + (N - stopPos N m v0) at hsplit
    change onesBefore v1 (stopPos N m v0) = onesBefore v0 (stopPos N m v0) at h1
    have ha_eq : onesBefore v0 (stopPos N m v0) + (N - D) = stopPos N m v0 := ha.2.2.2.1
    have ha_leN : stopPos N m v0 ≤ N := ha.2.1
    omega
  have ha1 : stopPos N m v1 = a := (stopPos_congr N m v0 v1 (fun j hj => (hv1_agree_lt j hj).symm)).symm
  have hpiv_eq : ∀ s ≤ a, excPivPos k r e q i v1 s = excPivPos k r e q i v0 s := by
    intro s hs
    unfold excPivPos excXPiv excDelta
    rw [onesBefore_congr v1 v0 s (fun j hj => hv1_agree_lt j (by omega))]
  have hpivList_eq : excPivList k r e q i v1 a = excPivList k r e q i v0 a := by
    unfold excPivList
    apply List.map_congr_left
    intro s hs
    rw [List.mem_range] at hs
    exact hpiv_eq s (by omega)
  have hnp_eq : excNonPivList k r e q i v1 a = np := by
    dsimp only [np]; unfold excNonPivList; rw [hpivList_eq]
  have hinit_bits : ∀ pos < k,
      (excInitStart k r e q i v1 extra1).testBit pos =
        if (excPivList k r e q i v0 a).contains pos then false else stTrue.testBit pos := by
    intro pos hpos
    unfold excInitStart
    dsimp only
    change ((List.range (k - stopPos N m v1)).foldl _ 0).testBit pos = _
    rw [ha1, hnp_eq, foldl_or_pos_testBit]
    simp only [Nat.zero_testBit, Bool.false_or]
    by_cases hpiv : (excPivList k r e q i v0 a).contains pos = true
    · simp only [hpiv, ↓reduceIte]
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      rcases hany with ⟨idx, hidx, hboth⟩
      rw [List.mem_range] at hidx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
      have hlt_np : idx < np.length := by omega
      rw [List.getD_eq_getElem _ _ hlt_np] at hboth
      have hmem := List.getElem_mem hlt_np
      rw [← hboth.2] at hmem
      dsimp only [np] at hmem
      unfold excNonPivList at hmem
      rw [List.mem_filter] at hmem
      have hmem_piv : pos ∈ excPivList k r e q i v0 a := List.contains_iff_mem.mp hpiv
      simp at hmem
      exact hmem.2 hmem_piv
    · have hpiv_f : (excPivList k r e q i v0 a).contains pos = false := Bool.eq_false_iff.mpr hpiv
      simp only [hpiv_f, Bool.false_eq_true, ↓reduceIte]
      have hnot_piv : pos ∉ excPivList k r e q i v0 a := by
        intro hm; exact hpiv (List.contains_iff_mem.mpr hm)
      have hmem_np : pos ∈ np := by
        dsimp only [np]; unfold excNonPivList
        rw [List.mem_filter, List.mem_range]
        exact ⟨hpos, by simp [hnot_piv]⟩
      rcases List.getElem_of_mem hmem_np with ⟨idx, hidx_lt, hidx_eq⟩
      have hdata : excDataBit N v1 extra1 a idx = stTrue.testBit pos := by
        unfold excDataBit
        by_cases h1 : idx < N - a
        · simp only [h1, ↓reduceIte]
          rw [hv1_agree_ge idx h1, List.getD_eq_getElem _ _ hidx_lt, hidx_eq]
        · simp only [h1, ↓reduceIte]
          rw [hextra_bit (idx - (N - a)) (by omega),
              show N - a + (idx - (N - a)) = idx by omega, List.getD_eq_getElem _ _ hidx_lt, hidx_eq]
      cases hst : stTrue.testBit pos
      · rw [Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        rcases hany with ⟨idx2, hidx2, hboth⟩
        rw [List.mem_range] at hidx2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
        have hidx2_lt : idx2 < np.length := by omega
        rw [List.getD_eq_getElem _ _ hidx2_lt] at hboth
        have heq_idx : idx2 = idx := by
          have hinj := List.nodup_iff_injective_getElem.mp hnp_nd
          have hfin : (⟨idx2, hidx2_lt⟩ : Fin np.length) = ⟨idx, hidx_lt⟩ :=
            hinj (by simpa [hidx_eq] using hboth.2.symm)
          exact congrArg Fin.val hfin
        subst heq_idx
        rw [hdata, hst] at hboth
        exact Bool.false_ne_true hboth.1
      · rw [List.any_eq_true]
        refine ⟨idx, List.mem_range.mpr (by omega), ?_⟩
        rw [hdata, hst, List.getD_eq_getElem _ _ hidx_lt, hidx_eq]
        simp
  let isLaterPiv : Nat → Nat → Bool := fun s pos =>
    (List.range (a - s)).any (fun d => decide (excPivPos k r e q i v0 (s + d) = pos))
  have hisLater_iff : ∀ s ≤ a, ∀ pos,
      isLaterPiv s pos = true ↔ ∃ t, s ≤ t ∧ t < a ∧ excPivPos k r e q i v0 t = pos := by
    intro s hsa pos
    dsimp only [isLaterPiv]
    rw [List.any_eq_true]
    constructor
    · rintro ⟨d, hd, heq⟩
      rw [List.mem_range] at hd
      rw [decide_eq_true_eq] at heq
      exact ⟨s + d, by omega, by omega, heq⟩
    · rintro ⟨t, ht1, ht2, heq⟩
      refine ⟨t - s, List.mem_range.mpr (by omega), decide_eq_true (by rw [show s + (t - s) = t by omega]; exact heq)⟩
  have hst_ind : ∀ s ≤ a,
      ∀ pos < k,
        (excState k r e q u i v1 extra1 s).testBit pos =
          if isLaterPiv s pos then false else stTrue.testBit pos := by
    intro s
    induction s with
    | zero =>
      intro _ pos hpos
      change (excInitStart k r e q i v1 extra1).testBit pos = _
      rw [hinit_bits pos hpos]
      have hbool_eq : (excPivList k r e q i v0 a).contains pos = isLaterPiv 0 pos := by
        rw [Bool.eq_iff_iff, hisLater_iff 0 (Nat.zero_le a) pos]
        simp [excPivList]
      rw [hbool_eq]
    | succ s ih =>
      intro hsa pos hpos
      have hprev := ih (by omega)
      unfold excState excStep
      dsimp only
      have hp_eq : excPivPos k r e q i v1 s = excPivPos k r e q i v0 s := hpiv_eq s (by omega)
      rw [hp_eq]
      have hp_lt : excPivPos k r e q i v0 s < k := Nat.mod_lt _ (by omega)
      have hp_is_later : isLaterPiv s (excPivPos k r e q i v0 s) = true :=
        (hisLater_iff s (by omega) _).mpr ⟨s, Nat.le_refl s, by omega, rfl⟩
      have hp_zero : (excState k r e q u i v1 extra1 s).testBit (excPivPos k r e q i v0 s) = false := by
        rw [hprev _ hp_lt, hp_is_later]; rfl
      rw [testBit_writeBit _ _ _ hp_zero pos]
      by_cases hpos_p : pos = excPivPos k r e q i v0 s
      · subst hpos_p
        have hnot_later : isLaterPiv (s + 1) (excPivPos k r e q i v0 s) = false := by
          rw [Bool.eq_false_iff]
          intro hm
          rcases (hisLater_iff (s + 1) hsa _).mp hm with ⟨t, ht1, ht2, hteq⟩
          have := excPivPos_inj k r e q i v0 a hq hr hkr hones_a ha.2.2.2.2 t ht2 s (by omega) hteq
          omega
        simp only [↓reduceIte, hnot_later, Bool.false_eq_true]
        have hd_eq : excDelta e q v1 s = excDelta e q v0 s := by
          unfold excDelta; rw [onesBefore_congr v1 v0 s (fun j hj => hv1_agree_lt j (by omega))]
        rw [hd_eq]
        have hxb := excXPiv_bounds k r e q v0 s hq hr hkr
          (Nat.le_trans (onesBefore_mono v0 s a (by omega)) hones_a) (ha.2.2.2.2 s (by omega))
        have hlin := guardAt_linear_pivot k r u i (excState k r e q u i v1 extra1 s) stTrue
          (e + q + 4 + s) (excDelta e q v0 s) (by omega) (by dsimp only [N] at ha; omega) (by omega)
          hu (excState_lt k r e q u i v1 extra1 hq hr hkr s) hstTrue_lt ?_
        · have hv1s : v1.testBit s = guardAt k r u i w (e + q + 4 + s) (excDelta e q v0 s) := by
            rw [hv1_agree_lt s (by omega)]
            exact hv0_spec.1 s (Nat.zero_le s) (by omega) (ha.2.2.2.2 s (by omega))
          have hkey_st : keyOfStart k u stTrue = w :=
            keyOfStart_start k u w (by omega) hu hw
          rw [hkey_st] at hlin
          have hp_def : (i + 3 * r + (k + 5 - (5 * (e + q + 4 + s) + excDelta e q v0 s))) % k =
              excPivPos k r e q i v0 s := rfl
          rw [hp_def, hp_zero, Bool.false_xor] at hlin
          rw [hv1s, hlin]
        · intro x hx1 hx2
          rw [hprev _ (Nat.mod_lt _ (by omega))]
          have hnot_in : isLaterPiv s ((i + 3 * r + x) % k) = false := by
            rw [Bool.eq_false_iff]
            intro hm
            rcases (hisLater_iff s (by omega) _).mp hm with ⟨t, ht1, ht2, hteq⟩
            have htb := excXPiv_bounds k r e q v0 t hq hr hkr
              (Nat.le_trans (onesBefore_mono v0 t a (by omega)) hones_a) (ha.2.2.2.2 t ht2)
            have hle_x : excXPiv k e q v0 t ≤ excXPiv k e q v0 s := by
              by_cases hts : s = t
              · subst hts; exact Nat.le_refl _
              · have := excXPiv_strict_dec k r e q v0 s t hq hr hkr (by omega)
                  (Nat.le_trans (onesBefore_mono v0 t a (by omega)) hones_a) (ha.2.2.2.2 t ht2)
                omega
            have hne_x : excXPiv k e q v0 t ≠ x := by unfold excXPiv at hle_x ⊢; omega
            exact mod_ne_of_lt_k k (i + 3 * r) _ _ htb.2.2 (by omega) hne_x hteq
          rw [hnot_in]; rfl
      · simp only [hpos_p, ↓reduceIte, hprev pos hpos]
        have hbool_eq : isLaterPiv s pos = isLaterPiv (s + 1) pos := by
          rw [Bool.eq_iff_iff, hisLater_iff s (by omega) pos, hisLater_iff (s + 1) hsa pos]
          constructor
          · rintro ⟨t, ht1, ht2, hteq⟩
            by_cases hts : t = s
            · subst hts; exact absurd hteq.symm hpos_p
            · exact ⟨t, by omega, ht2, hteq⟩
          · rintro ⟨t, ht1, ht2, hteq⟩; exact ⟨t, by omega, ht2, hteq⟩
        rw [hbool_eq]
  refine ⟨⟨v1, hv1_lt⟩, ?_, ⟨extra1, hextra_lt⟩, ?_⟩
  · simp [lowWeightSet, hwt1]
  · unfold reconstructExc
    dsimp only
    change keyOfStart k u (excState k r e q u i v1 extra1 (stopPos N m v1)) = w
    rw [ha1]
    have hst_eq : excState k r e q u i v1 extra1 a = stTrue := by
      apply nat_eq_of_testBit_lt k _ _ (excState_lt k r e q u i v1 extra1 hq hr hkr a) hstTrue_lt
      intro pos hpos
      have h := hst_ind a (Nat.le_refl a) pos hpos
      have hnot : isLaterPiv a pos = false := by simp [isLaterPiv]
      rw [hnot] at h
      exact h
    rw [hst_eq]
    exact keyOfStart_start k u w (by omega) hu hw

lemma testBit_writeBit_any (w p : Nat) (b : Bool) (j : Nat) :
    (writeBit w p b).testBit j = if j = p then (w.testBit p || b) else w.testBit j := by
  unfold writeBit
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h : j = p
    · subst h; simp
    · simp [h]
  · simp only [↓reduceIte]
    rw [Nat.testBit_or, testBit_one_shiftLeft]
    by_cases h : j = p
    · subst h; simp
    · simp [h]

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates, 0⟩
  back : ReadsBack n ⟨gates, 0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def HasWord (B : Bank n) (k : Nat) (w : (Fin n → Bool) → Nat) : Prop :=
  ∀ j < k, B.Has (fun x => (w x).testBit j)

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

lemma Ext.word {B D : Bank n} (e : B.Ext D) {k : Nat} {w : (Fin n → Bool) → Nat}
    (hw : B.HasWord k w) : D.HasWord k w :=
  fun j hj => e (hw j hj)

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[], by simp [FanInTwo], by simp [ReadsBack]⟩

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i.val, i.isLt, ?_⟩
  intro x
  simp [val, empty, Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B, fun h => h, by omega, h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D, e, c, t⟩ := h
  exact ⟨D, e, by omega, hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a + b) q := by
  obtain ⟨D, e, c, t⟩ := h
  obtain ⟨E, e', c', t'⟩ := f D e t
  exact ⟨E, fun h => e' (e h), by omega, t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n + B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h | h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates, 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D, val, Circuit.wires, List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).length = n + B.gates.length := by
    simp [wireLen]
  refine ⟨D, ?_, by simp [D], n + B.gates.length, by simp [D], ?_⟩
  · intro f hf
    obtain ⟨i, hi, he⟩ := hf
    refine ⟨i, by simp [D]; omega, ?_⟩
    intro x
    unfold val
    rw [hv, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv, ← hl x]
    simp [val, List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or, []⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and, []⟩ (by simp) (by simp)

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i, hi, he⟩ := a
  simpa [GateOp.eval, he] using B.gate ⟨.not, [i]⟩ (by simp) (by simpa using hi)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.and, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.or, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  obtain ⟨D1, e1, hl1, h1⟩ := B.join a b
  obtain ⟨D2, e2, hl2, h2⟩ := D1.meet (e1 a) (e1 b)
  obtain ⟨D3, e3, hl3, h3⟩ := D2.inv h2
  obtain ⟨D4, e4, hl4, h4⟩ := D3.meet (e3 (e2 h1)) h3
  refine ⟨D4, fun h => e4 (e3 (e2 (e1 h))), by omega, ?_⟩
  have heq : (fun x => (f x || g x) && !(f x && g x)) = (fun x => xor (f x) (g x)) := by
    funext x; cases f x <;> cases g x <;> rfl
  rwa [heq] at h4

lemma finish {n budget : Nat} {f : BitFn n} (h : (empty n).Grow budget (fun D => D.Has f)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ budget ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨D, _, hlen, out, hout, heval⟩ := h
  refine ⟨⟨D.gates, out⟩, D.fan, D.back, by simpa [Circuit.size, empty] using hlen, ?_⟩
  intro x
  simpa [Circuit.eval, Circuit.wires, val] using heval x

end Bank

lemma grow_bits_clean {n : Nat} (B : Bank n) (m c : Nat) (F : Nat → BitFn n)
    (hF : ∀ (D : Bank n), B.Ext D → ∀ j < m, D.Grow c (fun E => E.Has (F j))) :
    B.Grow (m * c) (fun D => ∀ j < m, D.Has (F j)) := by
  induction m with
  | zero => exact (Bank.Grow.pure B (fun _ hj => by omega)).weaken (by omega) (fun _ h => h)
  | succ m ih =>
    have hprev := ih (fun D e j hj => hF D e j (by omega))
    obtain ⟨D, eBD, hlenD, hD⟩ := hprev
    obtain ⟨E, eDE, hlenE, hEm⟩ := hF D eBD m (by omega)
    refine ⟨E, fun h => eDE (eBD h), by rw [Nat.succ_mul]; omega, ?_⟩
    intro j hj
    by_cases hjm : j < m
    · exact eDE (hD j hjm)
    · have : j = m := by omega
      subst this; exact hEm

lemma grow_anyList {n : Nat} {α : Type*} (B : Bank n) (L : List α) (c : Nat)
    (F : α → BitFn n)
    (hF : ∀ a ∈ L, ∀ (D : Bank n), B.Ext D → D.Grow c (fun E => E.Has (F a))) :
    B.Grow (1 + L.length * (c + 1)) (fun D => D.Has (fun x => L.any (fun a => F a x))) := by
  induction L with
  | nil =>
    exact (B.const false).weaken (by simp) (fun D hD => by simpa using hD)
  | cons a L ih =>
    obtain ⟨D1, e1, hl1, h1⟩ := ih (fun b hb => hF b (List.mem_cons_of_mem a hb))
    obtain ⟨D2, e2, hl2, h2⟩ := hF a List.mem_cons_self D1 e1
    obtain ⟨D3, e3, hl3, h3⟩ := D2.join h2 (e2 h1)
    refine ⟨D3, fun h => e3 (e2 (e1 h)), ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul] at hl1 hl2 hl3 ⊢; omega
    · simpa [List.any_cons] using h3

lemma grow_constWord {n : Nat} (B : Bank n) (k c : Nat) :
    B.Grow k (fun D => D.HasWord k (fun _ => c)) := by
  simpa [Bank.HasWord, Nat.mul_one] using
    grow_bits_clean B k 1 (fun j _ => c.testBit j) (fun D _ j _ => D.const (c.testBit j))

lemma hasWord_rot {n : Nat} {B : Bank n} {k : Nat} (hk : 0 < k) (s : Nat)
    {w : (Fin n → Bool) → Nat} (hw : B.HasWord k w) (hlt : ∀ x, w x < 2 ^ k) :
    B.HasWord k (fun x => rot k s (w x)) := by
  intro j hj
  have h1 := hw ((j + k - s % k) % k) (Nat.mod_lt _ hk)
  have heq : (fun x => (rot k s (w x)).testBit j) =
      (fun x => (w x).testBit ((j + k - s % k) % k)) := by
    funext x; exact testBit_rot k s (w x) j (hlt x) hj
  rwa [heq]

lemma grow_xorWord {n : Nat} (B : Bank n) (k : Nat) {w1 w2 : (Fin n → Bool) → Nat}
    (h1 : B.HasWord k w1) (h2 : B.HasWord k w2) :
    B.Grow (4 * k) (fun D => D.HasWord k (fun x => w1 x ^^^ w2 x)) := by
  have h := grow_bits_clean B k 4 (fun j x => xor ((w1 x).testBit j) ((w2 x).testBit j))
    (fun D e j hj => D.xor2 (e (h1 j hj)) (e (h2 j hj)))
  refine h.weaken (by rw [Nat.mul_comm]) fun D hD j hj => ?_
  have heq : (fun x => (w1 x ^^^ w2 x).testBit j) =
      (fun x => xor ((w1 x).testBit j) ((w2 x).testBit j)) := by
    funext x; exact Nat.testBit_xor _ _ j
  rw [heq]; exact hD j hj

lemma grow_stepWord {n : Nat} (B : Bank n) (k : Nat) (hk : 0 < k) {w : (Fin n → Bool) → Nat}
    (hw : B.HasWord k w) :
    B.Grow (6 * k) (fun D => D.HasWord k (fun x => step k (w x))) := by
  have h := grow_bits_clean B k 6
    (fun j x => xor ((w x).testBit j)
      (!((w x).testBit ((j + 1) % k)) && (w x).testBit ((j + 2) % k)))
    (fun D e j hj => by
      have ha := e (hw j hj)
      have hb := e (hw ((j + 1) % k) (Nat.mod_lt _ hk))
      have hc := e (hw ((j + 2) % k) (Nat.mod_lt _ hk))
      obtain ⟨D1, e1, hl1, h1⟩ := D.inv hb
      obtain ⟨D2, e2, hl2, h2⟩ := D1.meet h1 (e1 hc)
      obtain ⟨D3, e3, hl3, h3⟩ := D2.xor2 (e2 (e1 ha)) h2
      exact ⟨D3, fun h => e3 (e2 (e1 h)), by omega, h3⟩)
  refine h.weaken (by rw [Nat.mul_comm]) fun D hD j hj => ?_
  have heq : (fun x => (step k (w x)).testBit j) =
      (fun x => xor ((w x).testBit j)
        (!((w x).testBit ((j + 1) % k)) && (w x).testBit ((j + 2) % k))) := by
    funext x; exact testBit_step k (w x) j hj
  rw [heq]; exact hD j hj

lemma grow_writeBit {n : Nat} (B : Bank n) (k p : Nat) {w : (Fin n → Bool) → Nat}
    {b : BitFn n} (hw : B.HasWord k w) (hb : B.Has b) (hp : p < k) :
    B.Grow 1 (fun D => D.HasWord k (fun x => writeBit (w x) p (b x))) := by
  obtain ⟨D, e, hl, hj⟩ := B.join (hw p hp) hb
  refine ⟨D, e, hl, ?_⟩
  intro j hj_lt
  have heq : (fun x => (writeBit (w x) p (b x)).testBit j) =
      if j = p then (fun x => (w x).testBit p || b x) else (fun x => (w x).testBit j) := by
    funext x
    rw [testBit_writeBit_any]
    by_cases hjp : j = p <;> simp [hjp]
  rw [heq]
  by_cases hjp : j = p
  · simp only [hjp, ↓reduceIte]; exact hj
  · simp only [hjp, ↓reduceIte]; exact e (hw j hj_lt)

lemma grow_state1 {n : Nat} (B : Bank n) (k : Nat) (hk : 2 ≤ k)
    {u key : (Fin n → Bool) → Nat}
    (hu : B.HasWord k u) (hkey : B.HasWord k key)
    (hu_lt : ∀ x, u x < 2 ^ k) (hkey_lt : ∀ x, key x < 2 ^ k) :
    ∀ t, B.Grow (4 * k + 23 * k * t) (fun D => D.HasWord k (fun x => state1 k (u x) (key x) t)) := by
  intro t
  induction t with
  | zero =>
    have hr1 := hasWord_rot (by omega) 1 hkey hkey_lt
    exact (grow_xorWord B k hr1 hu).weaken (by omega) (fun _ h => h)
  | succ t ih =>
    obtain ⟨D1, e1, hl1, hprev⟩ := ih
    have hprev_lt : ∀ x, state1 k (u x) (key x) t < 2 ^ k := fun x => state1_lt k _ _ t (hu_lt x)
    have hr1 := hasWord_rot (by omega) 1 hprev hprev_lt
    have hrk1 := hasWord_rot (by omega) (k - 1) hprev hprev_lt
    obtain ⟨D2, e2, hl2, hm1⟩ := grow_xorWord D1 k hprev hr1
    obtain ⟨D3, e3, hl3, hm2⟩ := grow_xorWord D2 k hm1 (e2.word hrk1)
    obtain ⟨D4, e4, hl4, hst⟩ := grow_stepWord D3 k (by omega) hm2
    have hrk := hasWord_rot (by omega) (2 * t) (e4.word (e3.word (e2.word (e1.word hkey)))) hkey_lt
    obtain ⟨D5, e5, hl5, hx1⟩ := grow_xorWord D4 k hst hrk
    obtain ⟨D6, e6, hl6, hc⟩ := grow_constWord D5 k (constW k (t + 1))
    obtain ⟨D7, e7, hl7, hx2⟩ := grow_xorWord D6 k (e6.word hx1) hc
    refine ⟨D7, fun h => e7 (e6 (e5 (e4 (e3 (e2 (e1 h)))))), ?_, hx2⟩
    rw [Nat.mul_succ]; omega

lemma grow_state2 {n : Nat} (B : Bank n) (k r : Nat) (hk : 2 ≤ k)
    {v key : (Fin n → Bool) → Nat}
    (hv : B.HasWord k v) (hkey : B.HasWord k key)
    (hv_lt : ∀ x, v x < 2 ^ k) (hkey_lt : ∀ x, key x < 2 ^ k) :
    ∀ t, B.Grow (4 * k + 23 * k * t) (fun D => D.HasWord k (fun x => state2 k r (v x) (key x) t)) := by
  intro t
  induction t with
  | zero =>
    have hr3 := hasWord_rot (by omega) 3 hkey hkey_lt
    exact (grow_xorWord B k hr3 hv).weaken (by omega) (fun _ h => h)
  | succ t ih =>
    obtain ⟨D1, e1, hl1, hprev⟩ := ih
    have hprev_lt : ∀ x, state2 k r (v x) (key x) t < 2 ^ k := fun x => state2_lt k r _ _ t (hv_lt x)
    have hr2 := hasWord_rot (by omega) 2 hprev hprev_lt
    have hrk2 := hasWord_rot (by omega) (k - 2) hprev hprev_lt
    obtain ⟨D2, e2, hl2, hm1⟩ := grow_xorWord D1 k hprev hr2
    obtain ⟨D3, e3, hl3, hm2⟩ := grow_xorWord D2 k hm1 (e2.word hrk2)
    obtain ⟨D4, e4, hl4, hst⟩ := grow_stepWord D3 k (by omega) hm2
    have hrk := hasWord_rot (by omega) (3 * (t + 1) + 1) (e4.word (e3.word (e2.word (e1.word hkey)))) hkey_lt
    obtain ⟨D5, e5, hl5, hx1⟩ := grow_xorWord D4 k hst hrk
    obtain ⟨D6, e6, hl6, hc⟩ := grow_constWord D5 k (constW k (r + (t + 1)))
    obtain ⟨D7, e7, hl7, hx2⟩ := grow_xorWord D6 k (e6.word hx1) hc
    refine ⟨D7, fun h => e7 (e6 (e5 (e4 (e3 (e2 (e1 h)))))), ?_, hx2⟩
    rw [Nat.mul_succ]; omega

lemma grow_before1 {n : Nat} (B : Bank n) (k r i : Nat) (hk : 2 ≤ k) (hi : i < k)
    {u key : (Fin n → Bool) → Nat}
    (hu : B.HasWord k u) (hkey : B.HasWord k key)
    (hu_lt : ∀ x, u x < 2 ^ k) (hkey_lt : ∀ x, key x < 2 ^ k) :
    B.Grow (23 * k * (r + 1)) (fun D => D.Has (fun x => before1 k r (u x) i (key x))) := by
  obtain ⟨D1, e1, hl1, hprev⟩ := grow_state1 B k hk hu hkey hu_lt hkey_lt (r - 1)
  have hprev_lt : ∀ x, state1 k (u x) (key x) (r - 1) < 2 ^ k := fun x => state1_lt k _ _ _ (hu_lt x)
  have hr1 := hasWord_rot (by omega) 1 hprev hprev_lt
  have hrk1 := hasWord_rot (by omega) (k - 1) hprev hprev_lt
  obtain ⟨D2, e2, hl2, hm1⟩ := grow_xorWord D1 k hprev hr1
  obtain ⟨D3, e3, hl3, hm2⟩ := grow_xorWord D2 k hm1 (e2.word hrk1)
  obtain ⟨D4, e4, hl4, hst⟩ := grow_stepWord D3 k (by omega) hm2
  refine ⟨D4, fun h => e4 (e3 (e2 (e1 h))), ?_, hst i hi⟩
  have hle : 23 * k * (r - 1) ≤ 23 * k * r := Nat.mul_le_mul_left _ (Nat.sub_le r 1)
  rw [Nat.mul_succ]; omega

lemma grow_guardAt {n : Nat} (B : Bank n) (k r i t δ : Nat) (hk : 2 ≤ k) (htr : t ≤ r)
    {u key : (Fin n → Bool) → Nat}
    (hu : B.HasWord k u) (hkey : B.HasWord k key)
    (hu_lt : ∀ x, u x < 2 ^ k) (hkey_lt : ∀ x, key x < 2 ^ k) :
    B.Grow (23 * k * (r + 1) + 8) (fun D => D.Has (fun x => guardAt k r (u x) i (key x) t δ)) := by
  obtain ⟨D1, e1, hl1, hz⟩ := grow_state1 B k hk hu hkey hu_lt hkey_lt (t - 1)
  let b := i + 3 * (r - t) + k - δ
  have h0 := hz (b % k) (Nat.mod_lt _ (by omega))
  have h1 := hz ((b + 1) % k) (Nat.mod_lt _ (by omega))
  have h2 := hz ((b + 2) % k) (Nat.mod_lt _ (by omega))
  obtain ⟨D2, e2, hl2, hx1⟩ := D1.xor2 h0 h1
  obtain ⟨D3, e3, hl3, hx2⟩ := D2.xor2 hx1 (e2 h2)
  refine ⟨D3, fun h => e3 (e2 (e1 h)), ?_, hx2⟩
  have hle : 23 * k * (t - 1) ≤ 23 * k * r := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_succ]; omega

lemma grow_lt_pow {n : Nat} (B : Bank n) (k h : Nat) (hh : h ≤ k)
    {w : (Fin n → Bool) → Nat} (hw : B.HasWord k w) (hw_lt : ∀ x, w x < 2 ^ k) :
    B.Grow (2 * k + 1) (fun D => D.Has (fun x => decide (w x < 2 ^ (k - h)))) := by
  have hall : ∀ m ≤ h, B.Grow (1 + 2 * m) (fun D =>
      D.Has (fun x => (List.range m).all (fun j => !((w x).testBit (k - h + j))))) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact (B.const true).weaken (by omega) (fun D hD => by simpa using hD)
    | succ m ih =>
      intro hm
      obtain ⟨D1, e1, hl1, h1⟩ := ih (by omega)
      obtain ⟨D2, e2, hl2, hn⟩ := D1.inv (e1 (hw (k - h + m) (by omega)))
      obtain ⟨D3, e3, hl3, ha⟩ := D2.meet (e2 h1) hn
      refine ⟨D3, fun h => e3 (e2 (e1 h)), by omega, ?_⟩
      have heq : (fun x => (List.range (m + 1)).all (fun j => !((w x).testBit (k - h + j)))) =
          (fun x => (List.range m).all (fun j => !((w x).testBit (k - h + j))) &&
            !((w x).testBit (k - h + m))) := by
        funext x; simp [List.range_succ]
      rwa [heq]
  obtain ⟨D, e, hl, hD⟩ := hall h (Nat.le_refl h)
  refine ⟨D, e, by omega, ?_⟩
  have heq : (fun x => (List.range h).all (fun j => !((w x).testBit (k - h + j)))) =
      (fun x => decide (w x < 2 ^ (k - h))) := by
    funext x
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, lt_two_pow_sub_iff k h (w x) hh (hw_lt x)]
    constructor
    · intro h1 j hj1 hj2
      have := h1 (j - (k - h)) (List.mem_range.mpr (by omega))
      simp only [show k - h + (j - (k - h)) = j by omega, Bool.not_eq_true'] at this
      exact this
    · intro h1 j hj
      rw [List.mem_range] at hj
      simp only [Bool.not_eq_true']
      exact h1 (k - h + j) (by omega) (by omega)
  rwa [heq] at hD

lemma grow_testWord {n : Nat} (B : Bank n) (k r : Nat) (hk : 2 ≤ k)
    {u v key : (Fin n → Bool) → Nat}
    (hu : B.HasWord k u) (hv : B.HasWord k v) (hkey : B.HasWord k key)
    (hu_lt : ∀ x, u x < 2 ^ k) (hv_lt : ∀ x, v x < 2 ^ k) (hkey_lt : ∀ x, key x < 2 ^ k) :
    B.Grow (50 * k * (r + 1) + 3) (fun D => D.Has (fun x => testWord k r (u x) (v x) (key x))) := by
  obtain ⟨D1, e1, hl1, hs1⟩ := grow_state1 B k hk hu hkey hu_lt hkey_lt r
  obtain ⟨D2, e2, hl2, ht1⟩ := grow_lt_pow D1 k ((k + 1) / 2) (by omega) hs1
    (fun x => state1_lt k _ _ r (hu_lt x))
  obtain ⟨D3, e3, hl3, hs2⟩ := grow_state2 D2 k r hk (e2.word (e1.word hv)) (e2.word (e1.word hkey))
    hv_lt hkey_lt r
  obtain ⟨D4, e4, hl4, ht2⟩ := grow_lt_pow D3 k ((k + 1) / 2) (by omega) hs2
    (fun x => state2_lt k r _ _ r (hv_lt x))
  obtain ⟨D5, e5, hl5, hand⟩ := D4.meet (e4 (e3 ht1)) ht2
  refine ⟨D5, fun h => e5 (e4 (e3 (e2 (e1 h)))), ?_, hand⟩
  have h50 : 50 * k * (r + 1) = 50 * (k * r) + 50 * k := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have h23 : 23 * k * r = 23 * (k * r) := Nat.mul_assoc 23 k r
  rw [h50]; rw [h23] at hl1 hl3; omega

lemma grow_ordSlot {n : Nat} (B : Bank n) (k r e q raw : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hkr : k + e + 3 = 5 * r)
    {u v : (Fin n → Bool) → Nat} (hu : B.HasWord k u) (hv : B.HasWord k v)
    (hu_lt : ∀ x, u x < 2 ^ k) (hv_lt : ∀ x, v x < 2 ^ k) :
    B.Grow (100 * (k + 1) * (r + 1) ^ 2)
      (fun D => D.Has (fun x => testWord k r (u x) (v x) (reconstructOrd k r e q (u x) raw))) := by
  have hk2 : 2 ≤ k := by omega
  have hsteps : ∀ j ≤ q, B.Grow (k + j * (23 * k * (r + 1) + 6))
      (fun D => D.HasWord k (fun x => ordKey k r e q (u x) raw j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact (grow_constWord B k (ordInit k r e q raw)).weaken (by omega) (fun _ h => h)
    | succ j ih =>
      intro hjq
      obtain ⟨D1, e1, hl1, hwj⟩ := ih (by omega)
      have hwj_lt : ∀ x, ordKey k r e q (u x) raw j < 2 ^ k :=
        fun x => ordKey_lt k r e q (u x) raw hq hr hkr j (by omega)
      let i := k - 1 - j
      let p := ordBase r e q + (q - 1 - j)
      obtain ⟨D2, e2, hl2, hbef⟩ := grow_before1 D1 k r i hk2 (by dsimp only [i]; omega)
        (e1.word hu) hwj hu_lt hwj_lt
      obtain ⟨D3, e3, hl3, hc⟩ := D2.const ((constW k r).testBit i)
      obtain ⟨D4, e4, hl4, hbit⟩ := D3.xor2 (e3 hbef) hc
      obtain ⟨D5, e5, hl5, hnext⟩ := grow_writeBit D4 k p (e4.word (e3.word (e2.word hwj))) hbit
        (by dsimp only [p]; unfold ordBase; omega)
      refine ⟨D5, fun h => e5 (e4 (e3 (e2 (e1 h)))), ?_, hnext⟩
      rw [Nat.succ_mul]; omega
  obtain ⟨D1, e1, hl1, hkey⟩ := hsteps q (Nat.le_refl q)
  have hkey_lt : ∀ x, reconstructOrd k r e q (u x) raw < 2 ^ k :=
    fun x => ordKey_lt k r e q (u x) raw hq hr hkr q (Nat.le_refl q)
  obtain ⟨D2, e2, hl2, ht⟩ := grow_testWord D1 k r hk2 (e1.word hu) (e1.word hv) hkey hu_lt hv_lt hkey_lt
  refine ⟨D2, fun h => e2 (e1 h), ?_, ht⟩
  have hqr : q ≤ r := by omega
  have h1 : q * (23 * k * (r + 1) + 6) ≤ (r + 1) * (29 * (k + 1) * (r + 1)) := by
    apply Nat.mul_le_mul (by omega)
    have : 23 * k * (r + 1) + 6 ≤ 29 * (k + 1) * (r + 1) := by
      have h29 : 29 * (k + 1) * (r + 1) = 29 * (k * (r + 1)) + 29 * (r + 1) := by
        rw [Nat.mul_add 29 k 1, Nat.mul_one, Nat.add_mul, Nat.mul_assoc]
      have h23 : 23 * k * (r + 1) = 23 * (k * (r + 1)) := Nat.mul_assoc 23 k (r + 1)
      rw [h29, h23]; omega
    exact this
  have h2 : (r + 1) * (29 * (k + 1) * (r + 1)) = 29 * (k + 1) * (r + 1) ^ 2 := by
    rw [Nat.pow_two]; ac_rfl
  have h3 : 50 * k * (r + 1) + 3 + k ≤ 70 * (k + 1) * (r + 1) ^ 2 := by
    have hr1 : 1 ≤ r + 1 := by omega
    have hsq : r + 1 ≤ (r + 1) ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_right _ hr1
    have hm1 : 50 * k * (r + 1) ≤ 50 * (k + 1) * (r + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 50 (by omega)) hsq
    have hm2 : k + 3 ≤ 20 * (k + 1) * (r + 1) ^ 2 := by
      have : 1 ≤ (r + 1) ^ 2 := by rw [Nat.pow_two]; exact Nat.mul_pos hr1 hr1
      have : 20 * (k + 1) ≤ 20 * (k + 1) * (r + 1) ^ 2 := Nat.le_mul_of_pos_right _ this
      omega
    have hadd : 50 * (k + 1) * (r + 1) ^ 2 + 20 * (k + 1) * (r + 1) ^ 2 =
        70 * (k + 1) * (r + 1) ^ 2 := by rw [← Nat.add_mul, ← Nat.add_mul]
    omega
  have htot : 29 * (k + 1) * (r + 1) ^ 2 + 70 * (k + 1) * (r + 1) ^ 2 ≤
      100 * (k + 1) * (r + 1) ^ 2 := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

lemma grow_excSlot {n : Nat} (B : Bank n) (k r e q i v extra : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hkr : k + e + 3 = 5 * r)
    {u vcol : (Fin n → Bool) → Nat} (hu : B.HasWord k u) (hv : B.HasWord k vcol)
    (hu_lt : ∀ x, u x < 2 ^ k) (hv_lt : ∀ x, vcol x < 2 ^ k) :
    B.Grow (100 * (k + 1) * (r + 1) ^ 2)
      (fun D => D.Has (fun x => testWord k r (u x) (vcol x) (reconstructExc k r e q (u x) i v extra))) := by
  have hk2 : 2 ≤ k := by omega
  let N := (r - e) - (e + q + 3)
  let m := N - (e + q - 1)
  let a := stopPos N m v
  have ha_le : a ≤ N := by
    have hp := stopPosRec_props m v N 0
    have hz0 : zerosBefore v 0 = 0 := by simp [zerosBefore]
    rw [hz0] at hp
    simpa [a, stopPos] using hp.1
  have hsteps : ∀ s ≤ a, B.Grow (k + s * (27 * k * (r + 1) + 14))
      (fun D => D.HasWord k (fun x => excState k r e q (u x) i v extra s)) := by
    intro s
    induction s with
    | zero =>
      intro _
      exact (grow_constWord B k (excInitStart k r e q i v extra)).weaken (by omega) (fun _ h => h)
    | succ s ih =>
      intro hsa
      obtain ⟨D1, e1, hl1, hst⟩ := ih (by omega)
      have hst_lt : ∀ x, excState k r e q (u x) i v extra s < 2 ^ k :=
        fun x => excState_lt k r e q (u x) i v extra hq hr hkr s
      obtain ⟨D2, e2, hl2, hxu⟩ := grow_xorWord D1 k hst (e1.word hu)
      have hkey : D2.HasWord k (fun x => keyOfStart k (u x) (excState k r e q (u x) i v extra s)) :=
        hasWord_rot (by omega) (k - 1) hxu (fun x => Nat.xor_lt_two_pow (hst_lt x) (hu_lt x))
      have hkey_lt : ∀ x, keyOfStart k (u x) (excState k r e q (u x) i v extra s) < 2 ^ k :=
        fun x => keyOfStart_lt k _ _
      obtain ⟨D3, e3, hl3, hg⟩ := grow_guardAt D2 k r i (e + q + 4 + s) (excDelta e q v s) hk2
        (by dsimp only [N] at ha_le; omega) (e2.word (e1.word hu)) hkey hu_lt hkey_lt
      obtain ⟨D4, e4, hl4, hc⟩ := D3.const (v.testBit s)
      obtain ⟨D5, e5, hl5, hbit⟩ := D4.xor2 (e4 hg) hc
      obtain ⟨D6, e6, hl6, hnext⟩ := grow_writeBit D5 k (excPivPos k r e q i v s)
        (e5.word (e4.word (e3.word (e2.word hst)))) hbit (Nat.mod_lt _ (by omega))
      refine ⟨D6, fun h => e6 (e5 (e4 (e3 (e2 (e1 h))))), ?_, hnext⟩
      have h4k : 4 * k ≤ 4 * k * (r + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h27 : 23 * k * (r + 1) + 4 * k * (r + 1) = 27 * k * (r + 1) := by
        rw [← Nat.add_mul, ← Nat.add_mul]
      rw [Nat.succ_mul]; omega
  obtain ⟨D1, e1, hl1, hsta⟩ := hsteps a (Nat.le_refl a)
  have hsta_lt : ∀ x, excState k r e q (u x) i v extra a < 2 ^ k :=
    fun x => excState_lt k r e q (u x) i v extra hq hr hkr a
  obtain ⟨D2, e2, hl2, hxu⟩ := grow_xorWord D1 k hsta (e1.word hu)
  have hkey : D2.HasWord k (fun x => reconstructExc k r e q (u x) i v extra) :=
    hasWord_rot (by omega) (k - 1) hxu (fun x => Nat.xor_lt_two_pow (hsta_lt x) (hu_lt x))
  have hkey_lt : ∀ x, reconstructExc k r e q (u x) i v extra < 2 ^ k :=
    fun x => keyOfStart_lt k _ _
  obtain ⟨D3, e3, hl3, ht⟩ := grow_testWord D2 k r hk2 (e2.word (e1.word hu)) (e2.word (e1.word hv))
    hkey hu_lt hv_lt hkey_lt
  refine ⟨D3, fun h => e3 (e2 (e1 h)), ?_, ht⟩
  have h1 : a * (27 * k * (r + 1) + 14) ≤ (r + 1) * (41 * (k + 1) * (r + 1)) := by
    apply Nat.mul_le_mul (by dsimp only [N] at ha_le; omega)
    have h41 : 41 * (k + 1) * (r + 1) = 41 * (k * (r + 1)) + 41 * (r + 1) := by
      rw [Nat.mul_add 41 k 1, Nat.mul_one, Nat.add_mul, Nat.mul_assoc]
    have h27 : 27 * k * (r + 1) = 27 * (k * (r + 1)) := Nat.mul_assoc 27 k (r + 1)
    rw [h41, h27]; omega
  have h2 : (r + 1) * (41 * (k + 1) * (r + 1)) = 41 * (k + 1) * (r + 1) ^ 2 := by
    rw [Nat.pow_two]; ac_rfl
  have h3 : 50 * k * (r + 1) + 3 + 4 * k + k ≤ 58 * (k + 1) * (r + 1) ^ 2 := by
    have hr1 : 1 ≤ r + 1 := by omega
    have hsq : r + 1 ≤ (r + 1) ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_right _ hr1
    have hm1 : 50 * k * (r + 1) ≤ 50 * (k + 1) * (r + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 50 (by omega)) hsq
    have hm2 : 5 * k + 3 ≤ 8 * (k + 1) * (r + 1) ^ 2 := by
      have : 1 ≤ (r + 1) ^ 2 := by rw [Nat.pow_two]; exact Nat.mul_pos hr1 hr1
      have : 8 * (k + 1) ≤ 8 * (k + 1) * (r + 1) ^ 2 := Nat.le_mul_of_pos_right _ this
      omega
    have hadd : 50 * (k + 1) * (r + 1) ^ 2 + 8 * (k + 1) * (r + 1) ^ 2 =
        58 * (k + 1) * (r + 1) ^ 2 := by rw [← Nat.add_mul, ← Nat.add_mul]
    omega
  have htot : 41 * (k + 1) * (r + 1) ^ 2 + 58 * (k + 1) * (r + 1) ^ 2 ≤
      100 * (k + 1) * (r + 1) ^ 2 := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

lemma graph_iff_slots (k r e q u v : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hkr : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (_hv : v < 2 ^ k) :
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let ordList := (Finset.univ : Finset (Fin (2 ^ (k - q)))).toList
    let excList := ((Finset.univ : Finset (Fin q)) ×ˢ
      ((lowWeightSet N D) ×ˢ (Finset.univ : Finset (Fin (2 ^ (k - N)))))).toList
    (List.range (2 ^ k)).any (fun w => testWord k r u v w) =
      (ordList.any (fun raw => testWord k r u v (reconstructOrd k r e q u raw.val)) ||
       excList.any (fun slot => testWord k r u v
         (reconstructExc k r e q u (k - 1 - slot.1.val) slot.2.1.val slot.2.2.val))) := by
  intro N D ordList excList
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨w, hw_mem, htw⟩
    rw [List.mem_range] at hw_mem
    have hpass1 : state1 k u w r < 2 ^ (k - (k + 1) / 2) := by
      unfold testWord at htw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htw
      exact htw.1
    rcases ord_or_exceptional k r e q u w hq hr hkr hu hw_mem hpass1 with
      ⟨raw, hord⟩ | ⟨idx, hidx, mask, hdiff⟩
    · left
      refine ⟨raw, ?_, by rw [hord]; exact htw⟩
      simp [ordList]
    · right
      dsimp only at hdiff
      let i := k - 1 - idx
      have hi_lt : i < k := by dsimp only [i]; omega
      let consts : Nat → Fin (2 ^ k) := fun j => ⟨constW k j, constW_lt k j⟩
      have h25514 := PEqualNP.Outside.L_meta_25514 k r e q consts u i hq hr hkr hu hi_lt
        ⟨w, hw_mem⟩ mask
      have hstate_eq : ∀ key rounds,
          (List.range rounds).foldl (fun prev t =>
            step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
              rot k (2 * t) key ^^^ (consts (t + 1)).val) (rot k 1 key ^^^ u) =
          state1 k u key rounds := fun key rounds => (state1_eq_fold k u key rounds).symm
      have hbefore_eq : ∀ key,
          (let prev := (List.range (r - 1)).foldl (fun prev t =>
            step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
              rot k (2 * t) key ^^^ (consts (t + 1)).val) (rot k 1 key ^^^ u)
           (step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev)).testBit i) =
          before1 k r u i key := by
        intro key; dsimp only; rw [hstate_eq]; rfl
      have hdiff' :
          (let rot' := fun (s word : ℕ) => ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
           let step' := fun (word : ℕ) => (List.range k).foldl (fun acc b =>
             acc ||| ((xor (word.testBit b)
               (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
           let state' := fun (key rounds : ℕ) => (List.range rounds).foldl (fun prev t =>
             step' (prev ^^^ rot' 1 prev ^^^ rot' (k - 1) prev) ^^^ rot' (2 * t) key ^^^
               (consts (t + 1)).val) (rot' 1 key ^^^ u)
           let before' := fun subject : ℕ =>
             let prev := state' subject (r - 1)
             (step' (prev ^^^ rot' 1 prev ^^^ rot' (k - 1) prev)).testBit i
           before' w ≠ before' (w ^^^ rot' (i + 3 * r + k - e - q) mask.val)) := by
        dsimp only
        let w2 := w ^^^ rot k (i + 3 * r + k - e - q) mask.val
        change (let prev := (List.range (r - 1)).foldl (fun prev t =>
          step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
            rot k (2 * t) w ^^^ (consts (t + 1)).val) (rot k 1 w ^^^ u)
          (step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev)).testBit i) ≠
          (let prev := (List.range (r - 1)).foldl (fun prev t =>
          step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^
            rot k (2 * t) w2 ^^^ (consts (t + 1)).val) (rot k 1 w2 ^^^ u)
          (step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev)).testBit i)
        rw [hbefore_eq w, hbefore_eq w2]
        exact hdiff
      rcases h25514 hdiff' with ⟨d, hd1, hd2, hd3⟩
      have hd_guard : ∀ t, e + q + 3 < t → t ≤ r - e →
          (∀ s, e + q + 3 ≤ s → s < t → s + d s < t + d t) →
          guardAt k r u i w t (d t) = false := by
        intro t ht1 ht2 hrec
        have hg := hd3 t ht1 ht2 hrec
        dsimp only at hg
        unfold guardAt
        dsimp only
        rw [← hstate_eq w (t - 1)]
        exact hg
      have hexc := greedy_reconstructs_exc k r e q u i w hq hr hkr hu hi_lt hw_mem d
        (fun t ht1 ht2 => (hd1 t ht1 ht2).1) hd2 hd_guard
      rcases hexc with ⟨v1, hv1_mem, extra1, hrec_eq⟩
      refine ⟨(⟨idx, hidx⟩, (v1, extra1)), ?_, by dsimp only; rw [hrec_eq]; exact htw⟩
      simp only [excList, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and, and_true]
      exact hv1_mem
  · rintro (⟨raw, _, htw⟩ | ⟨slot, _, htw⟩)
    · refine ⟨reconstructOrd k r e q u raw.val, List.mem_range.mpr ?_, htw⟩
      exact ordKey_lt k r e q u raw.val hq hr hkr q (Nat.le_refl q)
    · refine ⟨reconstructExc k r e q u (k - 1 - slot.1.val) slot.2.1.val slot.2.2.val,
        List.mem_range.mpr (keyOfStart_lt k _ _), htw⟩

lemma solve_25533 (k r e q : Nat) (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hkr : k + e + 3 = 5 * r) :
    let h := (k + 1) / 2
    let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
      (List.range (2 ^ k)).any (fun w =>
        decide (state1 k row.val w r < 2 ^ (k - h)) &&
        decide (state2 k r col.val w r < 2 ^ (k - h)))
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let E := (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)
    ∃ C : Circuit,
      FanInTwo C ∧
      ReadsBack (k + k) C ∧
      C.size ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 * (2 ^ (k - q) + q * E) ∧
      ∀ bits : Fin (k + k) → Bool,
        C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro h graph N D E
  let uFn : (Fin (k + k) → Bool) → Nat := fun bits =>
    (Fin.ofNat (2 ^ k) (tableIndex fun i : Fin k => bits (Fin.castAdd k i))).val
  let vFn : (Fin (k + k) → Bool) → Nat := fun bits =>
    (Fin.ofNat (2 ^ k) (tableIndex fun j : Fin k => bits (Fin.natAdd k j))).val
  have hu_lt : ∀ x, uFn x < 2 ^ k := fun x => (Fin.ofNat (2 ^ k) _).isLt
  have hv_lt : ∀ x, vFn x < 2 ^ k := fun x => (Fin.ofNat (2 ^ k) _).isLt
  have hu_word : (Bank.empty (k + k)).HasWord k uFn := by
    intro j hj
    have heq : (fun x => (uFn x).testBit j) = (fun x => x ⟨j, by omega⟩) := by
      funext x
      dsimp only [uFn]
      have hlt := tableIndex_lt (fun i : Fin k => x (Fin.castAdd k i))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hlt, testBit_tableIndex _ j hj]
      rfl
    rw [heq]
    exact Bank.input ⟨j, by omega⟩
  have hv_word : (Bank.empty (k + k)).HasWord k vFn := by
    intro j hj
    have heq : (fun x => (vFn x).testBit j) = (fun x => x ⟨k + j, by omega⟩) := by
      funext x
      dsimp only [vFn]
      have hlt := tableIndex_lt (fun i : Fin k => x (Fin.natAdd k i))
      simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hlt, testBit_tableIndex _ j hj]
      rfl
    rw [heq]
    exact Bank.input ⟨k + j, by omega⟩
  let ordList := (Finset.univ : Finset (Fin (2 ^ (k - q)))).toList
  let excList := ((Finset.univ : Finset (Fin q)) ×ˢ
    ((lowWeightSet N D) ×ˢ (Finset.univ : Finset (Fin (2 ^ (k - N)))))).toList
  let slotCost := 100 * (k + 1) * (r + 1) ^ 2
  have hord_len : ordList.length = 2 ^ (k - q) := by
    simp [ordList, Fintype.card_fin]
  have hexc_len : excList.length = q * E := by
    simp only [excList, Finset.length_toList, Finset.card_product, Finset.card_univ,
               Fintype.card_fin, card_lowWeightSet, E]
  have hord_grow := grow_anyList (Bank.empty (k + k)) ordList slotCost
    (fun raw x => testWord k r (uFn x) (vFn x) (reconstructOrd k r e q (uFn x) raw.val))
    (fun raw _ D1 e1 => grow_ordSlot D1 k r e q raw.val hq hr hkr (e1.word hu_word) (e1.word hv_word) hu_lt hv_lt)
  have hbuild : (Bank.empty (k + k)).Grow
      (1000 * (k + 1) ^ 3 * (r + 1) ^ 2 * (2 ^ (k - q) + q * E))
      (fun D => D.Has (fun x => PEqualNP.Represents.adjFun (k := k) (l := k) graph x)) := by
    obtain ⟨D1, e1, hl1, h1⟩ := hord_grow
    obtain ⟨D2, e2, hl2, h2⟩ := grow_anyList D1 excList slotCost
      (fun slot x => testWord k r (uFn x) (vFn x)
        (reconstructExc k r e q (uFn x) (k - 1 - slot.1.val) slot.2.1.val slot.2.2.val))
      (fun slot _ D' e' => grow_excSlot D' k r e q (k - 1 - slot.1.val) slot.2.1.val slot.2.2.val
        hq hr hkr (e'.word (e1.word hu_word)) (e'.word (e1.word hv_word)) hu_lt hv_lt)
    obtain ⟨D3, e3, hl3, h3⟩ := D2.join (e2 h1) h2
    refine ⟨D3, fun h => e3 (e2 (e1 h)), ?_, ?_⟩
    · simp only [Bank.empty, List.length_nil, Nat.zero_add] at hl1 hl2 hl3 ⊢
      rw [hord_len] at hl1
      rw [hexc_len] at hl2
      let S := 2 ^ (k - q) + q * E
      have hS_pos : 1 ≤ S := by
        dsimp only [S]; have := Nat.two_pow_pos (k - q); omega
      have hsum : 1 + 2 ^ (k - q) * (slotCost + 1) + (1 + q * E * (slotCost + 1)) + 1 =
          3 + S * (slotCost + 1) := by
        dsimp only [S]; rw [Nat.add_mul]; omega
      have h3S : 3 + S * (slotCost + 1) ≤ S * (slotCost + 4) := by
        rw [Nat.mul_add, Nat.mul_add]; omega
      have hsc : slotCost + 4 ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 := by
        dsimp only [slotCost]
        have hk1 : 1 ≤ k + 1 := by omega
        have hr1 : 1 ≤ r + 1 := by omega
        have hsq : k + 1 ≤ (k + 1) ^ 3 := by
          calc k + 1 = (k + 1) * 1 := (Nat.mul_one _).symm
            _ ≤ (k + 1) * ((k + 1) * (k + 1)) := Nat.mul_le_mul_left _ (Nat.mul_pos hk1 hk1)
            _ = (k + 1) ^ 3 := by rw [Nat.pow_succ, Nat.pow_two]; ac_rfl
        have h100 : 100 * (k + 1) * (r + 1) ^ 2 ≤ 100 * (k + 1) ^ 3 * (r + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 100 hsq)
        have h4 : 4 ≤ 900 * (k + 1) ^ 3 * (r + 1) ^ 2 := by
          have : 1 ≤ (k + 1) ^ 3 * (r + 1) ^ 2 :=
            Nat.mul_pos (Nat.pow_pos hk1) (Nat.pow_pos hr1)
          rw [Nat.mul_assoc]; omega
        have h1000 : 100 * (k + 1) ^ 3 * (r + 1) ^ 2 + 900 * (k + 1) ^ 3 * (r + 1) ^ 2 =
            1000 * (k + 1) ^ 3 * (r + 1) ^ 2 := by rw [← Nat.add_mul, ← Nat.add_mul]
        omega
      have hfin : S * (slotCost + 4) ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 * S := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right S hsc
      have hfin' : S * (slotCost + 4) ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 * (2 ^ (k - q) + q * E) := hfin
      omega
    · have heq : (fun x =>
          (ordList.any (fun raw => testWord k r (uFn x) (vFn x) (reconstructOrd k r e q (uFn x) raw.val)) ||
           excList.any (fun slot => testWord k r (uFn x) (vFn x)
             (reconstructExc k r e q (uFn x) (k - 1 - slot.1.val) slot.2.1.val slot.2.2.val)))) =
          (fun x => PEqualNP.Represents.adjFun (k := k) (l := k) graph x) := by
        funext x
        rw [← graph_iff_slots k r e q (uFn x) (vFn x) hq hr hkr (hu_lt x) (hv_lt x)]
        rfl
      rwa [heq] at h3
  exact Bank.finish hbuild

end PEqualNP.Outside.L_meta_25533_aux

theorem PEqualNP.Outside.L_meta_25533 : ∀ (k r e q : Nat), 0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  let N := (r - e) - (e + q + 3)
  let D := e + q - 1
  let E := (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 *
      (2 ^ (k - q) + q * E) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r e q hq hr hkr
  dsimp only
  obtain ⟨C, hFan, hRead, hSize, hEval⟩ :=
    PEqualNP.Outside.L_meta_25533_aux.solve_25533 k r e q hq hr hkr
  refine ⟨C, hFan, hRead, hSize, fun bits => ?_⟩
  rw [hEval bits]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  congr 1
  funext w
  rw [PEqualNP.Outside.L_meta_25533_aux.state1_eq_fold,
      PEqualNP.Outside.L_meta_25533_aux.state2_eq_fold]
  rfl
