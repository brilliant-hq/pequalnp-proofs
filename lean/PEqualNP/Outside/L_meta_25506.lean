import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25506_aux

def rotK (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepK (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def constK (k j : ℕ) : ℕ :=
  3 ^ (k + j) % 2 ^ k

def rowStep (k w : ℕ) (st idx : ℕ) : ℕ :=
  stepK k (st ^^^ rotK k 1 st ^^^ rotK k (k - 1) st) ^^^ rotK k (2 * idx) w ^^^ constK k (idx + 1)

def colStep (k r w : ℕ) (st idx : ℕ) : ℕ :=
  stepK k (st ^^^ rotK k 2 st ^^^ rotK k (k - 2) st) ^^^
    rotK k (3 * (idx + 1) + 1) w ^^^ constK k (r + (idx + 1))

def firstIter (k w u : ℕ) (t : ℕ) : ℕ :=
  (List.range t).foldl (rowStep k w) (rotK k 1 w ^^^ u)

def secondIter (k r w v : ℕ) (t : ℕ) : ℕ :=
  (List.range t).foldl (colStep k r w) (rotK k 3 w ^^^ v)

def firstK (k r w u : ℕ) : ℕ := firstIter k w u r

def secondK (k r w v : ℕ) : ℕ := secondIter k r w v r

lemma testBit_lt_of_lt {a m i : ℕ} (ha : a < 2 ^ m) (hi : m ≤ i) : a.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)

lemma lt_two_pow_iff_high_bits_false {a m k : ℕ} (ha : a < 2 ^ k) :
    a < 2 ^ m ↔ ∀ i, m ≤ i → i < k → a.testBit i = false := by
  constructor
  · intro h i him _
    exact testBit_lt_of_lt h him
  · intro h
    have heq : a = a % 2 ^ m := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases him : i < m
      · simp [him]
      · simp only [him, decide_false, Bool.false_and]
        by_cases hik : i < k
        · exact h i (by omega) hik
        · exact testBit_lt_of_lt ha (by omega)
    rw [heq]
    exact Nat.mod_lt a (Nat.two_pow_pos m)

lemma xor_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : (a ^^^ b) < 2 ^ k := by
  have heq : a ^^^ b = (a ^^^ b) % 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hi : i < k
    · simp [hi]
    · have h1 : a.testBit i = false := testBit_lt_of_lt ha (by omega)
      have h2 : b.testBit i = false := testBit_lt_of_lt hb (by omega)
      simp [hi, h1, h2]
  rw [heq]
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotK_lt {k : ℕ} (s word : ℕ) : rotK k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotK_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotK k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotK
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsr : s % k < k := Nat.mod_lt s hk
  by_cases h0 : s % k = 0
  · rw [h0]
    have hge : word.testBit (k + i) = false := testBit_lt_of_lt hw (by omega)
    simp [hge, Nat.mod_eq_of_lt hi]
  · by_cases hir : i < s % k
    · have hge : ¬(s % k ≤ i) := by omega
      have hmod : (i + k - s % k) % k = k - s % k + i := by
        have hlt : k - s % k + i < k := by omega
        have heq : i + k - s % k = k - s % k + i := by omega
        rw [heq, Nat.mod_eq_of_lt hlt]
      simp [hge, hmod]
    · have hle : s % k ≤ i := by omega
      have hge : word.testBit (k - s % k + i) = false := testBit_lt_of_lt hw (by omega)
      have hmod : (i + k - s % k) % k = i - s % k := by
        have heq : i + k - s % k = (i - s % k) + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp [hle, hge, hmod]

def stepFold (f : ℕ → Bool) (m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0

lemma stepFold_lt (f : ℕ → Bool) (m : ℕ) : stepFold f m < 2 ^ m := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change stepFold f m ||| ((f m).toNat <<< m) < 2 ^ (m + 1)
    have hbit : ((f m).toNat <<< m) < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq]
      cases f m <;> simp [Nat.pow_succ]
    have hlt1 : stepFold f m < 2 ^ (m + 1) := lt_trans ih (by rw [Nat.pow_succ]; omega)
    have heq : (stepFold f m ||| ((f m).toNat <<< m)) =
        (stepFold f m ||| ((f m).toNat <<< m)) % 2 ^ (m + 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
      by_cases hi : i < m + 1
      · simp [hi]
      · have h1 : (stepFold f m).testBit i = false := testBit_lt_of_lt hlt1 (by omega)
        have h2 : ((f m).toNat <<< m).testBit i = false := testBit_lt_of_lt hbit (by omega)
        simp [hi, h1, h2]
    rw [heq]
    exact Nat.mod_lt _ (Nat.two_pow_pos (m + 1))

lemma stepFold_testBit (f : ℕ → Bool) (m i : ℕ) :
    (stepFold f m).testBit i = if i < m then f i else false := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (stepFold f m ||| ((f m).toNat <<< m)).testBit i = if i < m + 1 then f i else false
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have hnot : ¬(m ≤ i) := by omega
      have hlt : i < m + 1 := by omega
      simp [him, hnot, hlt]
    · by_cases heq : i = m
      · subst heq
        cases hfm : f i <;> simp
      · have hgt : ¬(i < m + 1) := by omega
        have htb : (f m).toNat.testBit (i - m) = false := by
          apply testBit_lt_of_lt (m := 1)
          · cases f m <;> simp
          · omega
        simp [him, hgt, htb]

lemma stepK_lt (k word : ℕ) : stepK k word < 2 ^ k :=
  stepFold_lt _ k

lemma stepK_testBit {k word i : ℕ} (hi : i < k) :
    (stepK k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  have h := stepFold_testBit
    (fun j => xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)))
    k i
  unfold stepK
  simpa [stepFold, hi] using h

lemma constK_lt (k j : ℕ) : constK k j < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma firstIter_lt {k w u : ℕ} (hu : u < 2 ^ k) (t : ℕ) : firstIter k w u t < 2 ^ k := by
  induction t with
  | zero =>
    unfold firstIter
    simp only [List.range_zero, List.foldl_nil]
    exact xor_lt_two_pow (rotK_lt 1 w) hu
  | succ t _ =>
    unfold firstIter
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold rowStep
    exact xor_lt_two_pow (xor_lt_two_pow (stepK_lt k _) (rotK_lt _ w)) (constK_lt k _)

lemma secondIter_lt {k r w v : ℕ} (hv : v < 2 ^ k) (t : ℕ) : secondIter k r w v t < 2 ^ k := by
  induction t with
  | zero =>
    unfold secondIter
    simp only [List.range_zero, List.foldl_nil]
    exact xor_lt_two_pow (rotK_lt 3 w) hv
  | succ t _ =>
    unfold secondIter
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold colStep
    exact xor_lt_two_pow (xor_lt_two_pow (stepK_lt k _) (rotK_lt _ w)) (constK_lt k _)

lemma firstK_lt {k r w u : ℕ} (hu : u < 2 ^ k) : firstK k r w u < 2 ^ k :=
  firstIter_lt hu r

lemma secondK_lt {k r w v : ℕ} (hv : v < 2 ^ k) : secondK k r w v < 2 ^ k :=
  secondIter_lt hv r

lemma rowMix_eq {k st1 st2 p : ℕ} (hk : 8 ≤ k) (h1 : st1 < 2 ^ k) (h2 : st2 < 2 ^ k) (hp : p < k)
    (hagree : ∀ e ≤ 4, st1.testBit ((p + k - 1 + e) % k) = st2.testBit ((p + k - 1 + e) % k)) :
    (stepK k (st1 ^^^ rotK k 1 st1 ^^^ rotK k (k - 1) st1)).testBit p =
    (stepK k (st2 ^^^ rotK k 1 st2 ^^^ rotK k (k - 1) st2)).testBit p := by
  have hk0 : 0 < k := by omega
  have hm : ∀ d ≤ 2,
      (st1 ^^^ rotK k 1 st1 ^^^ rotK k (k - 1) st1).testBit ((p + d) % k) =
      (st2 ^^^ rotK k 1 st2 ^^^ rotK k (k - 1) st2).testBit ((p + d) % k) := by
    intro d hd
    have hpd : (p + d) % k < k := Nat.mod_lt _ hk0
    simp only [Nat.testBit_xor]
    rw [rotK_testBit hk0 h1 hpd, rotK_testBit hk0 h1 hpd,
      rotK_testBit hk0 h2 hpd, rotK_testBit hk0 h2 hpd]
    have hm1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hmk1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm1, hmk1]
    have e0 : (p + d) % k = (p + k - 1 + (d + 1)) % k := by
      have hsum : p + k - 1 + (d + 1) = (p + d) + k := by omega
      rw [hsum, Nat.add_mod_right]
    have e1 : ((p + d) % k + k - 1) % k = (p + k - 1 + d) % k := by
      have hsub : (p + d) % k + k - 1 = (p + d) % k + (k - 1) := by omega
      rw [hsub, Nat.mod_add_mod]
      congr 1; omega
    have e2 : ((p + d) % k + k - (k - 1)) % k = (p + k - 1 + (d + 2)) % k := by
      have hsub : (p + d) % k + k - (k - 1) = (p + d) % k + 1 := by omega
      rw [hsub, Nat.mod_add_mod]
      have hsum : p + k - 1 + (d + 2) = (p + d + 1) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [e1, e2, e0, hagree (d + 1) (by omega), hagree d (by omega), hagree (d + 2) (by omega)]
  rw [stepK_testBit hp, stepK_testBit hp]
  have h0 := hm 0 (by omega)
  have h1' := hm 1 (by omega)
  have h2' := hm 2 (by omega)
  rw [Nat.add_zero, Nat.mod_eq_of_lt hp] at h0
  rw [h0, h1', h2']

lemma colMix_eq {k st1 st2 p : ℕ} (hk : 8 ≤ k) (h1 : st1 < 2 ^ k) (h2 : st2 < 2 ^ k) (hp : p < k)
    (hagree : ∀ e ≤ 6, st1.testBit ((p + k - 2 + e) % k) = st2.testBit ((p + k - 2 + e) % k)) :
    (stepK k (st1 ^^^ rotK k 2 st1 ^^^ rotK k (k - 2) st1)).testBit p =
    (stepK k (st2 ^^^ rotK k 2 st2 ^^^ rotK k (k - 2) st2)).testBit p := by
  have hk0 : 0 < k := by omega
  have hm : ∀ d ≤ 2,
      (st1 ^^^ rotK k 2 st1 ^^^ rotK k (k - 2) st1).testBit ((p + d) % k) =
      (st2 ^^^ rotK k 2 st2 ^^^ rotK k (k - 2) st2).testBit ((p + d) % k) := by
    intro d hd
    have hpd : (p + d) % k < k := Nat.mod_lt _ hk0
    simp only [Nat.testBit_xor]
    rw [rotK_testBit hk0 h1 hpd, rotK_testBit hk0 h1 hpd,
      rotK_testBit hk0 h2 hpd, rotK_testBit hk0 h2 hpd]
    have hm2 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have hmk2 : (k - 2) % k = k - 2 := Nat.mod_eq_of_lt (by omega)
    rw [hm2, hmk2]
    have e0 : (p + d) % k = (p + k - 2 + (d + 2)) % k := by
      have hsum : p + k - 2 + (d + 2) = (p + d) + k := by omega
      rw [hsum, Nat.add_mod_right]
    have e1 : ((p + d) % k + k - 2) % k = (p + k - 2 + d) % k := by
      have hsub : (p + d) % k + k - 2 = (p + d) % k + (k - 2) := by omega
      rw [hsub, Nat.mod_add_mod]
      congr 1; omega
    have e2 : ((p + d) % k + k - (k - 2)) % k = (p + k - 2 + (d + 4)) % k := by
      have hsub : (p + d) % k + k - (k - 2) = (p + d) % k + 2 := by omega
      rw [hsub, Nat.mod_add_mod]
      have hsum : p + k - 2 + (d + 4) = (p + d + 2) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [e1, e2, e0, hagree (d + 2) (by omega), hagree d (by omega), hagree (d + 4) (by omega)]
  rw [stepK_testBit hp, stepK_testBit hp]
  have h0 := hm 0 (by omega)
  have h1' := hm 1 (by omega)
  have h2' := hm 2 (by omega)
  rw [Nat.add_zero, Nat.mod_eq_of_lt hp] at h0
  rw [h0, h1', h2']

def rowL (t : ℕ) : ℕ := if t ≤ 2 then t + 1 else 2 * t - 2

def rowW (t : ℕ) : ℕ := if t = 0 then 0 else rowL t + 3 * t - 1

def colL (t : ℕ) : ℕ := if t = 0 then 3 else if t = 1 then 5 else 3 * t + 1

def colW (t : ℕ) : ℕ := if t = 0 then 0 else colL t + 4 * t - 3

lemma rowLW_props (t : ℕ) :
    rowL t + 1 ≤ rowL (t + 1) ∧
    2 * t ≤ rowL (t + 1) ∧
    rowL (t + 1) - (rowL t + 1) + 4 + rowW t ≤ rowW (t + 1) ∧
    rowL (t + 1) - 2 * t ≤ rowW (t + 1) ∧
    rowL (t + 1) ≤ 2 * (t + 1) + 1 := by
  rcases t with _ | _ | _ | t <;> simp [rowW, rowL] <;> omega

lemma colLW_props (t : ℕ) :
    colL t + 2 ≤ colL (t + 1) ∧
    3 * (t + 1) + 1 ≤ colL (t + 1) ∧
    colL (t + 1) - (colL t + 2) + 6 + colW t ≤ colW (t + 1) ∧
    colL (t + 1) - (3 * (t + 1) + 1) ≤ colW (t + 1) ∧
    colL (t + 1) ≤ 3 * (t + 1) + 2 := by
  rcases t with _ | _ | t <;> simp [colW, colL] <;> omega

lemma firstIter_eq_of_cone {k r w1 w2 u t p : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k)
    (ht : t ≤ r) (hp : p < k)
    (hagree : ∀ d ≤ rowW t,
      w1.testBit ((p + k - rowL t + d) % k) = w2.testBit ((p + k - rowL t + d) % k)) :
    (firstIter k w1 u t).testBit p = (firstIter k w2 u t).testBit p := by
  have hk0 : 0 < k := by omega
  induction t generalizing p with
  | zero =>
    unfold firstIter
    simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
    rw [rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h0 := hagree 0 (by simp [rowW])
    simp only [rowL, show (0 : ℕ) ≤ 2 by omega, ↓reduceIte, Nat.add_zero] at h0
    rw [h0]
  | succ t ih =>
    unfold firstIter
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (rowStep k w1 (firstIter k w1 u t) t).testBit p =
      (rowStep k w2 (firstIter k w2 u t) t).testBit p
    unfold rowStep
    simp only [Nat.testBit_xor]
    rcases rowLW_props t with ⟨hrl_step, hrl_key, hrw_step, hrw_key, hrl_ub⟩
    have hrl_le : rowL (t + 1) < k := by omega
    have hmix :
        (stepK k (firstIter k w1 u t ^^^ rotK k 1 (firstIter k w1 u t) ^^^
          rotK k (k - 1) (firstIter k w1 u t))).testBit p =
        (stepK k (firstIter k w2 u t ^^^ rotK k 1 (firstIter k w2 u t) ^^^
          rotK k (k - 1) (firstIter k w2 u t))).testBit p := by
      apply rowMix_eq (by omega) (firstIter_lt hu t) (firstIter_lt hu t) hp
      intro e he
      apply ih (by omega) (Nat.mod_lt _ hk0)
      intro d hd
      have hidx : ((p + k - 1 + e) % k + k - rowL t + d) % k =
          (p + k - rowL (t + 1) + (rowL (t + 1) - (rowL t + 1) + e + d)) % k := by
        have hlt1 : rowL t ≤ k := by omega
        have hsub : (p + k - 1 + e) % k + k - rowL t + d =
            (p + k - 1 + e) % k + (k - rowL t + d) := by omega
        rw [hsub, Nat.mod_add_mod]
        have hsum : p + k - 1 + e + (k - rowL t + d) =
            (p + k - rowL (t + 1) + (rowL (t + 1) - (rowL t + 1) + e + d)) + k := by omega
        rw [hsum, Nat.add_mod_right]
      rw [hidx]
      exact hagree _ (by omega)
    have hkey : (rotK k (2 * t) w1).testBit p = (rotK k (2 * t) w2).testBit p := by
      rw [rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
      have h2t : (2 * t) % k = 2 * t := Nat.mod_eq_of_lt (by omega)
      rw [h2t]
      have hidx : (p + k - 2 * t) % k = (p + k - rowL (t + 1) + (rowL (t + 1) - 2 * t)) % k := by
        congr 1; omega
      rw [hidx]
      exact hagree _ hrw_key
    rw [hmix, hkey]

lemma secondIter_eq_of_cone {k r w1 w2 v t p : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hv : v < 2 ^ k)
    (ht : t ≤ r) (hp : p < k)
    (hagree : ∀ d ≤ colW t,
      w1.testBit ((p + k - colL t + d) % k) = w2.testBit ((p + k - colL t + d) % k)) :
    (secondIter k r w1 v t).testBit p = (secondIter k r w2 v t).testBit p := by
  have hk0 : 0 < k := by omega
  induction t generalizing p with
  | zero =>
    unfold secondIter
    simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
    rw [rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
    have h3 : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
    rw [h3]
    have h0 := hagree 0 (by simp [colW])
    simp only [colL, ↓reduceIte, Nat.add_zero] at h0
    rw [h0]
  | succ t ih =>
    unfold secondIter
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (colStep k r w1 (secondIter k r w1 v t) t).testBit p =
      (colStep k r w2 (secondIter k r w2 v t) t).testBit p
    unfold colStep
    simp only [Nat.testBit_xor]
    rcases colLW_props t with ⟨hcl_step, hcl_key, hcw_step, hcw_key, hcl_ub⟩
    have hcl_le : colL (t + 1) < k := by omega
    have hmix :
        (stepK k (secondIter k r w1 v t ^^^ rotK k 2 (secondIter k r w1 v t) ^^^
          rotK k (k - 2) (secondIter k r w1 v t))).testBit p =
        (stepK k (secondIter k r w2 v t ^^^ rotK k 2 (secondIter k r w2 v t) ^^^
          rotK k (k - 2) (secondIter k r w2 v t))).testBit p := by
      apply colMix_eq (by omega) (secondIter_lt hv t) (secondIter_lt hv t) hp
      intro e he
      apply ih (by omega) (Nat.mod_lt _ hk0)
      intro d hd
      have hlt1 : colL t ≤ k := by omega
      have hidx : ((p + k - 2 + e) % k + k - colL t + d) % k =
          (p + k - colL (t + 1) + (colL (t + 1) - (colL t + 2) + e + d)) % k := by
        have hsub : (p + k - 2 + e) % k + k - colL t + d =
            (p + k - 2 + e) % k + (k - colL t + d) := by omega
        rw [hsub, Nat.mod_add_mod]
        have hsum : p + k - 2 + e + (k - colL t + d) =
            (p + k - colL (t + 1) + (colL (t + 1) - (colL t + 2) + e + d)) + k := by omega
        rw [hsum, Nat.add_mod_right]
      rw [hidx]
      exact hagree _ (by omega)
    have hkey : (rotK k (3 * (t + 1) + 1) w1).testBit p =
        (rotK k (3 * (t + 1) + 1) w2).testBit p := by
      rw [rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
      have h3t : (3 * (t + 1) + 1) % k = 3 * (t + 1) + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h3t]
      have hidx : (p + k - (3 * (t + 1) + 1)) % k =
          (p + k - colL (t + 1) + (colL (t + 1) - (3 * (t + 1) + 1))) % k := by
        congr 1; omega
      rw [hidx]
      exact hagree _ hcw_key
    rw [hmix, hkey]

lemma firstK_xor_pivot {k r w1 w2 u p : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k) (hp : p < k)
    (hagree : ∀ d, 1 ≤ d → d ≤ 5 * r - 3 →
      w1.testBit ((p + k - (2 * r - 2) + d) % k) = w2.testBit ((p + k - (2 * r - 2) + d) % k)) :
    xor ((firstK k r w1 u).testBit p) ((firstK k r w2 u).testBit p) =
      xor (w1.testBit ((p + k - (2 * r - 2)) % k)) (w2.testBit ((p + k - (2 * r - 2)) % k)) := by
  have hk0 : 0 < k := by omega
  have hstep : ∀ w, firstK k r w u = rowStep k w (firstIter k w u (r - 1)) (r - 1) := by
    intro w
    have hr1 : r = (r - 1) + 1 := by omega
    unfold firstK firstIter
    conv_lhs => rw [hr1]
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hstep w1, hstep w2]
  unfold rowStep
  simp only [Nat.testBit_xor]
  have hrl : rowL (r - 1) = 2 * r - 4 := by
    unfold rowL
    have hgt : ¬(r - 1 ≤ 2) := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hgt)]
    omega
  have hrw : rowW (r - 1) = 5 * r - 8 := by
    unfold rowW
    have hne : r - 1 ≠ 0 := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne), hrl]
    omega
  have hmix :
      (stepK k (firstIter k w1 u (r - 1) ^^^ rotK k 1 (firstIter k w1 u (r - 1)) ^^^
        rotK k (k - 1) (firstIter k w1 u (r - 1)))).testBit p =
      (stepK k (firstIter k w2 u (r - 1) ^^^ rotK k 1 (firstIter k w2 u (r - 1)) ^^^
        rotK k (k - 1) (firstIter k w2 u (r - 1)))).testBit p := by
    apply rowMix_eq (by omega) (firstIter_lt hu (r - 1)) (firstIter_lt hu (r - 1)) hp
    intro e he
    apply firstIter_eq_of_cone hr hk hw1 hw2 hu (by omega) (Nat.mod_lt _ hk0)
    intro d hd
    rw [hrl]
    have hidx : ((p + k - 1 + e) % k + k - (2 * r - 4) + d) % k =
        (p + k - (2 * r - 2) + (1 + e + d)) % k := by
      have hsub : (p + k - 1 + e) % k + k - (2 * r - 4) + d =
          (p + k - 1 + e) % k + (k - (2 * r - 4) + d) := by omega
      rw [hsub, Nat.mod_add_mod]
      have hsum : p + k - 1 + e + (k - (2 * r - 4) + d) =
          (p + k - (2 * r - 2) + (1 + e + d)) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [hidx]
    exact hagree (1 + e + d) (by omega) (by rw [hrw] at hd; omega)
  rw [hmix, rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
  have h2r : (2 * (r - 1)) % k = 2 * r - 2 := by
    have heq : 2 * (r - 1) = 2 * r - 2 := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]
  rw [h2r]
  generalize (stepK k (firstIter k w2 u (r - 1) ^^^ rotK k 1 (firstIter k w2 u (r - 1)) ^^^
    rotK k (k - 1) (firstIter k w2 u (r - 1)))).testBit p = m
  generalize (constK k (r - 1 + 1)).testBit p = c
  cases m <;> cases c <;>
    cases w1.testBit ((p + k - (2 * r - 2)) % k) <;>
    cases w2.testBit ((p + k - (2 * r - 2)) % k) <;> rfl

lemma secondK_xor_pivot {k r w1 w2 v p : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hv : v < 2 ^ k) (hp : p < k)
    (hagree : ∀ d, 1 ≤ d → d ≤ 7 * r - 2 →
      w1.testBit ((p + k - (3 * r + 1) + d) % k) = w2.testBit ((p + k - (3 * r + 1) + d) % k)) :
    xor ((secondK k r w1 v).testBit p) ((secondK k r w2 v).testBit p) =
      xor (w1.testBit ((p + k - (3 * r + 1)) % k)) (w2.testBit ((p + k - (3 * r + 1)) % k)) := by
  have hk0 : 0 < k := by omega
  have hstep : ∀ w, secondK k r w v = colStep k r w (secondIter k r w v (r - 1)) (r - 1) := by
    intro w
    unfold secondK secondIter
    rw [show List.range r = List.range (r - 1) ++ [r - 1] by
      rw [← List.range_succ]; congr 1; omega]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hstep w1, hstep w2]
  unfold colStep
  simp only [Nat.testBit_xor]
  have hcl : colL (r - 1) = 3 * r - 2 := by
    unfold colL
    have h0 : r - 1 ≠ 0 := by omega
    have h1 : r - 1 ≠ 1 := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h h0), ite_eq_right_iff.mpr (fun h => absurd h h1)]
    omega
  have hcw : colW (r - 1) = 7 * r - 9 := by
    unfold colW
    have h0 : r - 1 ≠ 0 := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h h0), hcl]
    omega
  have hmix :
      (stepK k (secondIter k r w1 v (r - 1) ^^^ rotK k 2 (secondIter k r w1 v (r - 1)) ^^^
        rotK k (k - 2) (secondIter k r w1 v (r - 1)))).testBit p =
      (stepK k (secondIter k r w2 v (r - 1) ^^^ rotK k 2 (secondIter k r w2 v (r - 1)) ^^^
        rotK k (k - 2) (secondIter k r w2 v (r - 1)))).testBit p := by
    apply colMix_eq (by omega) (secondIter_lt hv (r - 1)) (secondIter_lt hv (r - 1)) hp
    intro e he
    apply secondIter_eq_of_cone hr hk hw1 hw2 hv (by omega) (Nat.mod_lt _ hk0)
    intro d hd
    rw [hcl]
    have hidx : ((p + k - 2 + e) % k + k - (3 * r - 2) + d) % k =
        (p + k - (3 * r + 1) + (1 + e + d)) % k := by
      have hsub : (p + k - 2 + e) % k + k - (3 * r - 2) + d =
          (p + k - 2 + e) % k + (k - (3 * r - 2) + d) := by omega
      rw [hsub, Nat.mod_add_mod]
      have hsum : p + k - 2 + e + (k - (3 * r - 2) + d) =
          (p + k - (3 * r + 1) + (1 + e + d)) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [hidx]
    exact hagree (1 + e + d) (by omega) (by rw [hcw] at hd; omega)
  rw [hmix, rotK_testBit hk0 hw1 hp, rotK_testBit hk0 hw2 hp]
  have h3r : (3 * (r - 1 + 1) + 1) % k = 3 * r + 1 := by
    have heq : 3 * (r - 1 + 1) + 1 = 3 * r + 1 := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]
  rw [h3r]
  generalize (stepK k (secondIter k r w2 v (r - 1) ^^^ rotK k 2 (secondIter k r w2 v (r - 1)) ^^^
    rotK k (k - 2) (secondIter k r w2 v (r - 1)))).testBit p = m
  generalize (constK k (r + (r - 1 + 1))).testBit p = c
  cases m <;> cases c <;>
    cases w1.testBit ((p + k - (3 * r + 1)) % k) <;>
    cases w2.testBit ((p + k - (3 * r + 1)) % k) <;> rfl

lemma bool_eq_of_xor_eq {a b c d : Bool} (h : xor a b = xor c d) (hcd : c = d) : a = b := by
  subst hcd
  cases a <;> cases b <;> cases c <;> simp_all

lemma bool_xor_eq_of_eq {a b c d : Bool} (h : xor a b = xor c d) (hab : a = b) : c = d := by
  subst hab
  cases a <;> cases c <;> cases d <;> simp_all

def setBitNat (w idx : ℕ) (b : Bool) : ℕ :=
  if b then w ||| (1 <<< idx) else w

lemma setBitNat_lt {k w idx : ℕ} {b : Bool} (hw : w < 2 ^ k) (hi : idx < k) :
    setBitNat w idx b < 2 ^ k := by
  unfold setBitNat
  cases b
  · exact hw
  · simp only [↓reduceIte]
    have hbit : (1 <<< idx) < 2 ^ k := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by omega) hi
    have heq : (w ||| (1 <<< idx)) = (w ||| (1 <<< idx)) % 2 ^ k := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
      by_cases hik : i < k
      · simp [hik]
      · have h1 : w.testBit i = false := testBit_lt_of_lt hw (by omega)
        have h2 : (1 <<< idx).testBit i = false := testBit_lt_of_lt hbit (by omega)
        simp [hik, h1, h2]
    rw [heq]
    exact Nat.mod_lt _ (Nat.two_pow_pos k)

lemma setBitNat_testBit {w idx i : ℕ} {b : Bool} (h0 : w.testBit idx = false) :
    (setBitNat w idx b).testBit i = if i = idx then b else w.testBit i := by
  unfold setBitNat
  by_cases heq : i = idx
  · subst heq
    cases b <;> simp [h0]
  · cases b
    · simp [heq]
    · simp only [↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hle : idx ≤ i
      · simp [heq, hle, testBit_lt_of_lt (m := 1) (by norm_num : 1 < 2 ^ 1) (by omega : 1 ≤ i - idx)]
      · simp [heq, hle]

def initSeedNat (k r : ℕ) (label : Fin (6 * r - 5) → Bool) : ℕ :=
  stepFold (fun idx =>
    if h1 : k - (2 * r - 2) ≤ idx ∧ idx < k then
      label ⟨idx - (k - (2 * r - 2)), by omega⟩
    else if h2 : idx < 4 * r - 3 then
      label ⟨idx + (2 * r - 2), by omega⟩
    else false) k

lemma initSeedNat_lt (k r : ℕ) (label : Fin (6 * r - 5) → Bool) :
    initSeedNat k r label < 2 ^ k :=
  stepFold_lt _ k

lemma initSeedNat_testBit {k r : ℕ} (hr : 4 ≤ r)
    (label : Fin (6 * r - 5) → Bool) (idx : ℕ) (hidx : idx < k) :
    (initSeedNat k r label).testBit idx =
      if h1 : k - (2 * r - 2) ≤ idx then
        label ⟨idx - (k - (2 * r - 2)), by omega⟩
      else if h2 : idx < 4 * r - 3 then
        label ⟨idx + (2 * r - 2), by omega⟩
      else false := by
  unfold initSeedNat
  rw [stepFold_testBit]
  simp only [hidx, ↓reduceIte, and_true]

def solveRows (k r u : ℕ) (w0 : ℕ) : ℕ → ℕ
  | 0 => w0
  | t + 1 =>
    let w := solveRows k r u w0 t
    let p := k - 1 - t
    let piv := p - (2 * r - 2)
    setBitNat w piv ((firstK k r w u).testBit p)

def solveCols (k r v : ℕ) (w0 : ℕ) : ℕ → ℕ
  | 0 => w0
  | t + 1 =>
    let w := solveCols k r v w0 t
    let h := (k + 1) / 2
    let p := k - h + (r + 2) - t
    let piv := p - (3 * r + 1)
    setBitNat w piv ((secondK k r w v).testBit p)

def decodeNat (k r u v : ℕ) (label : Fin (6 * r - 5) → Bool) : ℕ :=
  let h := (k + 1) / 2
  let w0 := initSeedNat k r label
  let w1 := solveRows k r u w0 h
  solveCols k r v w1 (r + 3)

lemma solveRows_lt {k r u w0 : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw0 : w0 < 2 ^ k) (t : ℕ) : solveRows k r u w0 t < 2 ^ k := by
  induction t with
  | zero => exact hw0
  | succ t ih =>
    unfold solveRows
    exact setBitNat_lt ih (by omega)

lemma solveCols_lt {k r v w0 : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw0 : w0 < 2 ^ k) (t : ℕ) : solveCols k r v w0 t < 2 ^ k := by
  induction t with
  | zero => exact hw0
  | succ t ih =>
    unfold solveCols
    exact setBitNat_lt ih (by omega)

lemma decodeNat_lt {k r u v : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (label : Fin (6 * r - 5) → Bool) : decodeNat k r u v label < 2 ^ k :=
  solveCols_lt hr hk (solveRows_lt hr hk (initSeedNat_lt k r label) _) _

lemma solveRows_spec {k r u w0 : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw0 : w0 < 2 ^ k) (hu : u < 2 ^ k)
    (hzero : ∀ idx, 4 * r - 3 ≤ idx → idx < k - (2 * r - 2) → w0.testBit idx = false)
    (t : ℕ) (ht : t ≤ (k + 1) / 2) :
    let w := solveRows k r u w0 t
    (∀ idx, idx < k - (2 * r - 2) - t ∨ k - (2 * r - 2) ≤ idx → w.testBit idx = w0.testBit idx) ∧
    (∀ q, k - t ≤ q → q < k → (firstK k r w u).testBit q = false) := by
  induction t with
  | zero =>
    exact ⟨fun _ _ => rfl, fun _ h1 h2 => by omega⟩
  | succ t ih =>
    rcases ih (by omega) with ⟨hpres, hdone⟩
    set w := solveRows k r u w0 t
    set p := k - 1 - t
    set piv := p - (2 * r - 2)
    have hw_lt : w < 2 ^ k := solveRows_lt hr hk hw0 t
    have hpiv_eq : piv = k - (2 * r - 2) - (t + 1) := by omega
    have hpiv0 : w.testBit piv = false := by
      rw [hpres piv (by left; omega)]
      exact hzero piv (by omega) (by omega)
    set w' := setBitNat w piv ((firstK k r w u).testBit p)
    have hw'_lt : w' < 2 ^ k := setBitNat_lt hw_lt (by omega)
    have hbit : ∀ i, w'.testBit i = if i = piv then (firstK k r w u).testBit p else w.testBit i :=
      fun i => setBitNat_testBit hpiv0
    change (∀ idx, idx < k - (2 * r - 2) - (t + 1) ∨ k - (2 * r - 2) ≤ idx →
        w'.testBit idx = w0.testBit idx) ∧
      (∀ q, k - (t + 1) ≤ q → q < k → (firstK k r w' u).testBit q = false)
    refine ⟨?_, ?_⟩
    · intro idx hidx
      have hne : idx ≠ piv := by omega
      rw [hbit idx, ite_eq_right_iff.mpr (fun h => absurd h hne), hpres idx (by omega)]
    · intro q hq1 hq2
      have hcone : ∀ d, 1 ≤ d → d ≤ 5 * r - 3 →
          w'.testBit ((q + k - (2 * r - 2) + d) % k) = w.testBit ((q + k - (2 * r - 2) + d) % k) := by
        intro d hd1 hd2
        have hne : (q + k - (2 * r - 2) + d) % k ≠ piv := by
          by_cases hwrap : q - (2 * r - 2) + d < k
          · have hmod : (q + k - (2 * r - 2) + d) % k = q - (2 * r - 2) + d := by
              have hsum : q + k - (2 * r - 2) + d = (q - (2 * r - 2) + d) + k := by omega
              rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
            rw [hmod]; omega
          · have hmod : (q + k - (2 * r - 2) + d) % k = q - (2 * r - 2) + d - k := by
              have hsum : q + k - (2 * r - 2) + d = (q - (2 * r - 2) + d - k) + 2 * k := by omega
              rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]; omega
        rw [hbit _, ite_eq_right_iff.mpr (fun h => absurd h hne)]
      have hxor := firstK_xor_pivot hr hk hw'_lt hw_lt hu hq2 hcone
      have hqpiv : (q + k - (2 * r - 2)) % k = q - (2 * r - 2) := by
        have hsum : q + k - (2 * r - 2) = (q - (2 * r - 2)) + k := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hqpiv] at hxor
      by_cases hqp : q = p
      · subst hqp
        rw [hbit piv, ite_eq_left_iff.mpr (fun h => absurd rfl h), hpiv0, Bool.xor_false] at hxor
        cases hfw : (firstK k r w u).testBit p <;> cases hfw' : (firstK k r w' u).testBit p <;>
          simp_all
      · have hne : q - (2 * r - 2) ≠ piv := by omega
        have hweq : w'.testBit (q - (2 * r - 2)) = w.testBit (q - (2 * r - 2)) := by
          rw [hbit _, ite_eq_right_iff.mpr (fun h => absurd h hne)]
        have hfeq := bool_eq_of_xor_eq hxor hweq
        rw [hfeq]
        exact hdone q (by omega) hq2

lemma solveCols_spec {k r v w0 : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw0 : w0 < 2 ^ k) (hv : v < 2 ^ k)
    (hzero : ∀ idx, k - (k + 1) / 2 - (3 * r + 1) ≤ idx → idx < k - (k + 1) / 2 - (2 * r - 2) →
      w0.testBit idx = false)
    (t : ℕ) (ht : t ≤ r + 3) :
    let h := (k + 1) / 2
    let w := solveCols k r v w0 t
    (∀ idx, idx < k - h - (2 * r - 2) - t ∨ k - h - (2 * r - 2) ≤ idx →
        w.testBit idx = w0.testBit idx) ∧
    (∀ q, k - h + (r + 3) - t ≤ q → q < k - h + (r + 3) → (secondK k r w v).testBit q = false) := by
  set h := (k + 1) / 2
  induction t with
  | zero =>
    exact ⟨fun _ _ => rfl, fun _ h1 h2 => by omega⟩
  | succ t ih =>
    rcases ih (by omega) with ⟨hpres, hdone⟩
    set w := solveCols k r v w0 t
    set p := k - h + (r + 2) - t
    set piv := p - (3 * r + 1)
    have hw_lt : w < 2 ^ k := solveCols_lt hr hk hw0 t
    have hpiv_eq : piv = k - h - (2 * r - 2) - (t + 1) := by omega
    have hpiv0 : w.testBit piv = false := by
      rw [hpres piv (by left; omega)]
      exact hzero piv (by omega) (by omega)
    set w' := setBitNat w piv ((secondK k r w v).testBit p)
    have hw'_lt : w' < 2 ^ k := setBitNat_lt hw_lt (by omega)
    have hbit : ∀ i, w'.testBit i = if i = piv then (secondK k r w v).testBit p else w.testBit i :=
      fun i => setBitNat_testBit hpiv0
    change (∀ idx, idx < k - h - (2 * r - 2) - (t + 1) ∨ k - h - (2 * r - 2) ≤ idx →
        w'.testBit idx = w0.testBit idx) ∧
      (∀ q, k - h + (r + 3) - (t + 1) ≤ q → q < k - h + (r + 3) →
        (secondK k r w' v).testBit q = false)
    refine ⟨?_, ?_⟩
    · intro idx hidx
      have hne : idx ≠ piv := by omega
      rw [hbit idx, ite_eq_right_iff.mpr (fun h => absurd h hne), hpres idx (by omega)]
    · intro q hq1 hq2
      have hqlt : q < k := by omega
      have hcone : ∀ d, 1 ≤ d → d ≤ 7 * r - 2 →
          w'.testBit ((q + k - (3 * r + 1) + d) % k) = w.testBit ((q + k - (3 * r + 1) + d) % k) := by
        intro d hd1 hd2
        have hne : (q + k - (3 * r + 1) + d) % k ≠ piv := by
          by_cases hwrap : q - (3 * r + 1) + d < k
          · have hmod : (q + k - (3 * r + 1) + d) % k = q - (3 * r + 1) + d := by
              have hsum : q + k - (3 * r + 1) + d = (q - (3 * r + 1) + d) + k := by omega
              rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
            rw [hmod]; omega
          · have hmod : (q + k - (3 * r + 1) + d) % k = q - (3 * r + 1) + d - k := by
              have hsum : q + k - (3 * r + 1) + d = (q - (3 * r + 1) + d - k) + 2 * k := by omega
              rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]; omega
        rw [hbit _, ite_eq_right_iff.mpr (fun h => absurd h hne)]
      have hxor := secondK_xor_pivot hr hk hw'_lt hw_lt hv hqlt hcone
      have hqpiv : (q + k - (3 * r + 1)) % k = q - (3 * r + 1) := by
        have hsum : q + k - (3 * r + 1) = (q - (3 * r + 1)) + k := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hqpiv] at hxor
      by_cases hqp : q = p
      · subst hqp
        rw [hbit piv, ite_eq_left_iff.mpr (fun h => absurd rfl h), hpiv0, Bool.xor_false] at hxor
        cases hsw : (secondK k r w v).testBit p <;> cases hsw' : (secondK k r w' v).testBit p <;>
          simp_all
      · have hne : q - (3 * r + 1) ≠ piv := by omega
        have hweq : w'.testBit (q - (3 * r + 1)) = w.testBit (q - (3 * r + 1)) := by
          rw [hbit _, ite_eq_right_iff.mpr (fun h => absurd h hne)]
        have hseq := bool_eq_of_xor_eq hxor hweq
        rw [hseq]
        exact hdone q (by omega) hq2

lemma first_agree_of_outside_row_cone {k r w1 w2 u : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k)
    (hagree : ∀ idx, idx < 4 * r - 3 ∨ k - (k + 1) / 2 - (2 * r - 2) ≤ idx →
      idx < k → w1.testBit idx = w2.testBit idx) :
    ∀ p, k - (k + 1) / 2 ≤ p → p < k →
      (firstK k r w1 u).testBit p = (firstK k r w2 u).testBit p := by
  intro p hp1 hp2
  have hbit : ∀ d ≤ 5 * r - 3,
      w1.testBit ((p + k - (2 * r - 2) + d) % k) = w2.testBit ((p + k - (2 * r - 2) + d) % k) := by
    intro d hd
    by_cases hwrap : p - (2 * r - 2) + d < k
    · have hmod : (p + k - (2 * r - 2) + d) % k = p - (2 * r - 2) + d := by
        have hsum : p + k - (2 * r - 2) + d = (p - (2 * r - 2) + d) + k := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
      rw [hmod]
      exact hagree _ (by right; omega) hwrap
    · have hmod : (p + k - (2 * r - 2) + d) % k = p - (2 * r - 2) + d - k := by
        have hsum : p + k - (2 * r - 2) + d = (p - (2 * r - 2) + d - k) + 2 * k := by omega
        rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact hagree _ (by left; omega) (by omega)
  have hxor := firstK_xor_pivot hr hk hw1 hw2 hu hp2 (fun d _ hd => hbit d hd)
  have h0 := hbit 0 (by omega)
  rw [Nat.add_zero] at h0
  exact bool_eq_of_xor_eq hxor h0

lemma second_agree_of_outside_col_cone {k r w1 w2 v : ℕ}
    (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hv : v < 2 ^ k)
    (hagree : ∀ idx, idx < 4 * r - 3 ∨ k - (k + 1) / 2 - (3 * r + 1) ≤ idx →
      idx < k → w1.testBit idx = w2.testBit idx) :
    ∀ p, k - (k + 1) / 2 ≤ p → p < k →
      (secondK k r w1 v).testBit p = (secondK k r w2 v).testBit p := by
  intro p hp1 hp2
  have hbit : ∀ d ≤ 7 * r - 2,
      w1.testBit ((p + k - (3 * r + 1) + d) % k) = w2.testBit ((p + k - (3 * r + 1) + d) % k) := by
    intro d hd
    by_cases hwrap : p - (3 * r + 1) + d < k
    · have hmod : (p + k - (3 * r + 1) + d) % k = p - (3 * r + 1) + d := by
        have hsum : p + k - (3 * r + 1) + d = (p - (3 * r + 1) + d) + k := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
      rw [hmod]
      exact hagree _ (by right; omega) hwrap
    · have hmod : (p + k - (3 * r + 1) + d) % k = p - (3 * r + 1) + d - k := by
        have hsum : p + k - (3 * r + 1) + d = (p - (3 * r + 1) + d - k) + 2 * k := by omega
        rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact hagree _ (by left; omega) (by omega)
  have hxor := secondK_xor_pivot hr hk hw1 hw2 hv hp2 (fun d _ hd => hbit d hd)
  have h0 := hbit 0 (by omega)
  rw [Nat.add_zero] at h0
  exact bool_eq_of_xor_eq hxor h0

lemma decodeNat_props {k r u v : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (label : Fin (6 * r - 5) → Bool) :
    let h := (k + 1) / 2
    let w := decodeNat k r u v label
    (∀ j : Fin (6 * r - 5), w.testBit ((k - (2 * r - 2) + j.val) % k) = label j) ∧
    (∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) → w.testBit i.val = false) ∧
    firstK k r w u < 2 ^ (k - h) ∧
    (∀ j : Fin (r + 3), (secondK k r w v).testBit (k - h + j.val) = false) := by
  set h := (k + 1) / 2
  set w0 := initSeedNat k r label
  have hw0_lt : w0 < 2 ^ k := initSeedNat_lt k r label
  have hzero0 : ∀ idx, 4 * r - 3 ≤ idx → idx < k - (2 * r - 2) → w0.testBit idx = false := by
    intro idx h1 h2
    rw [initSeedNat_testBit hr label idx (by omega)]
    have hn1 : ¬(k - (2 * r - 2) ≤ idx) := by omega
    have hn2 : ¬(idx < 4 * r - 3) := by omega
    simp [hn1, hn2]
  set w1 := solveRows k r u w0 h
  have hw1_lt : w1 < 2 ^ k := solveRows_lt hr hk hw0_lt h
  rcases solveRows_spec hr hk hw0_lt hu hzero0 h le_rfl with ⟨hpres1, hdone1⟩
  have hzero1 : ∀ idx, k - h - (3 * r + 1) ≤ idx → idx < k - h - (2 * r - 2) →
      w1.testBit idx = false := by
    intro idx h1 h2
    rw [hpres1 idx (by left; omega)]
    exact hzero0 idx (by omega) (by omega)
  set w2 := solveCols k r v w1 (r + 3)
  have hw2_lt : w2 < 2 ^ k := solveCols_lt hr hk hw1_lt (r + 3)
  rcases solveCols_spec hr hk hw1_lt hv hzero1 (r + 3) le_rfl with ⟨hpres2, hdone2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hlt : j.val < 2 * r - 2
    · have hmod : (k - (2 * r - 2) + j.val) % k = k - (2 * r - 2) + j.val :=
        Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      change w2.testBit (k - (2 * r - 2) + j.val) = label j
      rw [hpres2 _ (by right; omega), hpres1 _ (by right; omega),
        initSeedNat_testBit hr label _ (by omega)]
      have hge : k - (2 * r - 2) ≤ k - (2 * r - 2) + j.val := by omega
      simp only [hge, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
    · have hmod : (k - (2 * r - 2) + j.val) % k = j.val - (2 * r - 2) := by
        have hsum : k - (2 * r - 2) + j.val = (j.val - (2 * r - 2)) + k := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      change w2.testBit (j.val - (2 * r - 2)) = label j
      rw [hpres2 _ (by left; omega), hpres1 _ (by left; omega),
        initSeedNat_testBit hr label _ (by omega)]
      have hn1 : ¬(k - (2 * r - 2) ≤ j.val - (2 * r - 2)) := by omega
      have h2 : j.val - (2 * r - 2) < 4 * r - 3 := by omega
      simp only [hn1, ↓reduceDIte, h2]
      congr 1; apply Fin.ext; dsimp; omega
  · intro i hi1 hi2
    change w2.testBit i.val = false
    rw [hpres2 i.val (by left; omega), hpres1 i.val (by left; omega)]
    exact hzero0 i.val hi1 (by omega)
  · rw [lt_two_pow_iff_high_bits_false (firstK_lt hu)]
    intro p hp1 hp2
    have heq := first_agree_of_outside_row_cone hr hk hw2_lt hw1_lt hu
      (fun idx hidx _ => hpres2 idx (by omega)) p hp1 hp2
    change (firstK k r w2 u).testBit p = false
    rw [heq]
    exact hdone1 p hp1 hp2
  · intro j
    change (secondK k r w2 v).testBit (k - h + j.val) = false
    exact hdone2 (k - h + j.val) (by omega) (by omega)

lemma unique_normalized {k r u v w1 w2 : ℕ} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (hseed : ∀ j : Fin (6 * r - 5),
      w1.testBit ((k - (2 * r - 2) + j.val) % k) = w2.testBit ((k - (2 * r - 2) + j.val) % k))
    (hcan1 : ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - (k + 1) / 2 - (3 * r + 1) →
      w1.testBit i.val = false)
    (hcan2 : ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - (k + 1) / 2 - (3 * r + 1) →
      w2.testBit i.val = false)
    (hf1 : firstK k r w1 u < 2 ^ (k - (k + 1) / 2))
    (hf2 : firstK k r w2 u < 2 ^ (k - (k + 1) / 2))
    (hs1 : ∀ j : Fin (r + 3), (secondK k r w1 v).testBit (k - (k + 1) / 2 + j.val) = false)
    (hs2 : ∀ j : Fin (r + 3), (secondK k r w2 v).testBit (k - (k + 1) / 2 + j.val) = false) :
    w1 = w2 := by
  set h := (k + 1) / 2
  have hlow : ∀ idx < 4 * r - 3, w1.testBit idx = w2.testBit idx := by
    intro idx hidx
    have hs := hseed ⟨idx + (2 * r - 2), by omega⟩
    have hmod : (k - (2 * r - 2) + (idx + (2 * r - 2))) % k = idx := by
      have hsum : k - (2 * r - 2) + (idx + (2 * r - 2)) = idx + k := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simpa [hmod] using hs
  have hhigh : ∀ idx, k - (2 * r - 2) ≤ idx → idx < k → w1.testBit idx = w2.testBit idx := by
    intro idx h1 h2
    have hs := hseed ⟨idx - (k - (2 * r - 2)), by omega⟩
    have hmod : (k - (2 * r - 2) + (idx - (k - (2 * r - 2)))) % k = idx := by
      have hsum : k - (2 * r - 2) + (idx - (k - (2 * r - 2))) = idx := by omega
      rw [hsum, Nat.mod_eq_of_lt h2]
    simpa [hmod] using hs
  have hrow : ∀ t ≤ h, ∀ idx, k - (2 * r - 2) - t ≤ idx → idx < k →
      w1.testBit idx = w2.testBit idx := by
    intro t ht
    induction t with
    | zero =>
      intro idx h1 h2
      exact hhigh idx (by omega) h2
    | succ t ih =>
      have ih' := ih (by omega)
      intro idx h1 h2
      by_cases heq : idx = k - (2 * r - 2) - (t + 1)
      · set p := k - 1 - t
        have hp1 : k - h ≤ p := by omega
        have hp2 : p < k := by omega
        have hcone : ∀ d, 1 ≤ d → d ≤ 5 * r - 3 →
            w1.testBit ((p + k - (2 * r - 2) + d) % k) = w2.testBit ((p + k - (2 * r - 2) + d) % k) := by
          intro d hd1 hd2
          by_cases hwrap : p - (2 * r - 2) + d < k
          · have hmod : (p + k - (2 * r - 2) + d) % k = p - (2 * r - 2) + d := by
              have hsum : p + k - (2 * r - 2) + d = (p - (2 * r - 2) + d) + k := by omega
              rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
            rw [hmod]
            exact ih' _ (by omega) hwrap
          · have hmod : (p + k - (2 * r - 2) + d) % k = p - (2 * r - 2) + d - k := by
              have hsum : p + k - (2 * r - 2) + d = (p - (2 * r - 2) + d - k) + 2 * k := by omega
              rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
            exact hlow _ (by omega)
        have hxor := firstK_xor_pivot hr hk hw1 hw2 hu hp2 hcone
        have h1f : (firstK k r w1 u).testBit p = false :=
          (lt_two_pow_iff_high_bits_false (firstIter_lt hu r)).mp hf1 p hp1 hp2
        have h2f : (firstK k r w2 u).testBit p = false :=
          (lt_two_pow_iff_high_bits_false (firstIter_lt hu r)).mp hf2 p hp1 hp2
        have hpiv : (p + k - (2 * r - 2)) % k = idx := by
          have hsum : p + k - (2 * r - 2) = idx + k := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
        rw [hpiv] at hxor
        exact bool_xor_eq_of_eq hxor (by rw [h1f, h2f])
      · exact ih' idx (by omega) h2
  have hcol : ∀ t ≤ r + 3, ∀ idx, k - h - (2 * r - 2) - t ≤ idx → idx < k →
      w1.testBit idx = w2.testBit idx := by
    intro t ht
    induction t with
    | zero =>
      intro idx h1 h2
      exact hrow h le_rfl idx (by omega) h2
    | succ t ih =>
      have ih' := ih (by omega)
      intro idx h1 h2
      by_cases heq : idx = k - h - (2 * r - 2) - (t + 1)
      · set p := k - h + (r + 2) - t
        have hp2 : p < k := by omega
        have hcone : ∀ d, 1 ≤ d → d ≤ 7 * r - 2 →
            w1.testBit ((p + k - (3 * r + 1) + d) % k) = w2.testBit ((p + k - (3 * r + 1) + d) % k) := by
          intro d hd1 hd2
          by_cases hwrap : p - (3 * r + 1) + d < k
          · have hmod : (p + k - (3 * r + 1) + d) % k = p - (3 * r + 1) + d := by
              have hsum : p + k - (3 * r + 1) + d = (p - (3 * r + 1) + d) + k := by omega
              rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hwrap]
            rw [hmod]
            exact ih' _ (by omega) hwrap
          · have hmod : (p + k - (3 * r + 1) + d) % k = p - (3 * r + 1) + d - k := by
              have hsum : p + k - (3 * r + 1) + d = (p - (3 * r + 1) + d - k) + 2 * k := by omega
              rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
            exact hlow _ (by omega)
        have hxor := secondK_xor_pivot hr hk hw1 hw2 hv hp2 hcone
        have h1s : (secondK k r w1 v).testBit p = false := by
          have hj := hs1 ⟨r + 2 - t, by omega⟩
          have hpeq : k - h + (r + 2 - t) = p := by omega
          simpa [hpeq] using hj
        have h2s : (secondK k r w2 v).testBit p = false := by
          have hj := hs2 ⟨r + 2 - t, by omega⟩
          have hpeq : k - h + (r + 2 - t) = p := by omega
          simpa [hpeq] using hj
        have hpiv : (p + k - (3 * r + 1)) % k = idx := by
          have hsum : p + k - (3 * r + 1) = idx + k := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
        rw [hpiv] at hxor
        exact bool_xor_eq_of_eq hxor (by rw [h1s, h2s])
      · exact ih' idx (by omega) h2
  apply Nat.eq_of_testBit_eq
  intro idx
  by_cases hik : idx < k
  · by_cases h1 : idx < 4 * r - 3
    · exact hlow idx h1
    · by_cases h2 : idx < k - h - (3 * r + 1)
      · rw [hcan1 ⟨idx, hik⟩ (by dsimp; omega) (by dsimp; omega),
          hcan2 ⟨idx, hik⟩ (by dsimp; omega) (by dsimp; omega)]
      · exact hcol (r + 3) le_rfl idx (by omega) hik
  · rw [testBit_lt_of_lt hw1 (by omega), testBit_lt_of_lt hw2 (by omega)]

def normNat (k r w : ℕ) : ℕ :=
  let h := (k + 1) / 2
  stepFold (fun idx =>
    if 4 * r - 3 ≤ idx ∧ idx < k - h - (3 * r + 1) then false else w.testBit idx) k

lemma normNat_lt (k r w : ℕ) : normNat k r w < 2 ^ k :=
  stepFold_lt _ k

lemma normNat_testBit {k r w idx : ℕ} (hidx : idx < k) :
    (normNat k r w).testBit idx =
      if 4 * r - 3 ≤ idx ∧ idx < k - (k + 1) / 2 - (3 * r + 1) then false else w.testBit idx := by
  unfold normNat
  rw [stepFold_testBit]
  simp [hidx]

end PEqualNP.Outside.L_meta_25506_aux

theorem PEqualNP.Outside.L_meta_25506 : (∀ (k r : Nat), 4 ≤ r → (k + 1) / 2 + (7 * r - 2) ≤ k →
  ∀ u v : Fin (2 ^ k),
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
  let s := 6 * r - 5
  let seedOf := fun (w : Fin (2 ^ k)) (j : Fin s) =>
    w.val.testBit ((k - (2 * r - 2) + j.val) % k)
  let canonical := fun (w : Fin (2 ^ k)) =>
    ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) →
      w.val.testBit i.val = false
  let selected := fun (w : Fin (2 ^ k)) =>
    first w.val u.val < 2 ^ (k - h) ∧
      ∀ j : Fin (r + 3), (second w.val v.val).testBit (k - h + j.val) = false
  let joint := fun (w : Fin (2 ^ k)) =>
    first w.val u.val < 2 ^ (k - h) ∧ second w.val v.val < 2 ^ (k - h)
  ∃ decode : (Fin s → Bool) → Fin (2 ^ k),
    (∀ (label : Fin s → Bool) (key : Fin (2 ^ k)),
      key = decode label ↔ seedOf key = label ∧ canonical key ∧ selected key) ∧
    ((∃ raw, joint raw) ↔ ∃ label, joint (decode label))) := by
  intro k r hr hk u v
  open PEqualNP.Outside.L_meta_25506_aux in
  let decode : (Fin (6 * r - 5) → Bool) → Fin (2 ^ k) :=
    fun label => ⟨decodeNat k r u.val v.val label, decodeNat_lt hr hk label⟩
  refine ⟨decode, ?_, ?_⟩
  · intro label key
    rcases decodeNat_props hr hk u.isLt v.isLt label with ⟨hseedD, hcanD, hfD, hsD⟩
    constructor
    · rintro rfl
      refine ⟨?_, hcanD, hfD, hsD⟩
      funext j
      exact hseedD j
    · rintro ⟨hseedK, hcanK, hfK, hsK⟩
      apply Fin.ext
      apply unique_normalized hr hk u.isLt v.isLt key.isLt (decodeNat_lt hr hk label)
      · intro j
        have h1 : key.val.testBit ((k - (2 * r - 2) + j.val) % k) = label j := by
          simpa using congrFun hseedK j
        rw [h1, hseedD j]
      · exact hcanK
      · exact hcanD
      · exact hfK
      · exact hfD
      · exact hsK
      · exact hsD
  · constructor
    · rintro ⟨raw, hrawF, hrawS⟩
      set h := (k + 1) / 2
      let w : Fin (2 ^ k) := ⟨normNat k r raw.val, normNat_lt k r raw.val⟩
      let label : Fin (6 * r - 5) → Bool := fun j => w.val.testBit ((k - (2 * r - 2) + j.val) % k)
      have hwAgree : ∀ idx, idx < 4 * r - 3 ∨ k - h - (3 * r + 1) ≤ idx → idx < k →
          w.val.testBit idx = raw.val.testBit idx := by
        intro idx hidx hik
        change (normNat k r raw.val).testBit idx = raw.val.testBit idx
        rw [normNat_testBit hik]
        have hn : ¬(4 * r - 3 ≤ idx ∧ idx < k - h - (3 * r + 1)) := by omega
        rw [ite_eq_right_iff.mpr (fun hc => absurd hc hn)]
      have hwF : firstK k r w.val u.val < 2 ^ (k - h) := by
        rw [lt_two_pow_iff_high_bits_false (firstK_lt u.isLt)]
        intro p hp1 hp2
        rw [first_agree_of_outside_row_cone hr hk w.isLt raw.isLt u.isLt
          (fun idx hidx hik => hwAgree idx (by omega) hik) p hp1 hp2]
        exact (lt_two_pow_iff_high_bits_false (firstK_lt u.isLt)).mp hrawF p hp1 hp2
      have hwS : secondK k r w.val v.val < 2 ^ (k - h) := by
        rw [lt_two_pow_iff_high_bits_false (secondK_lt v.isLt)]
        intro p hp1 hp2
        rw [second_agree_of_outside_col_cone hr hk w.isLt raw.isLt v.isLt hwAgree p hp1 hp2]
        exact (lt_two_pow_iff_high_bits_false (secondK_lt v.isLt)).mp hrawS p hp1 hp2
      have hwCan : ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) →
          w.val.testBit i.val = false := by
        intro i hi1 hi2
        change (normNat k r raw.val).testBit i.val = false
        rw [normNat_testBit i.isLt]
        have hi2' : i.val < k - (k + 1) / 2 - (3 * r + 1) := hi2
        simp [hi1, hi2']
      have hwSel : ∀ j : Fin (r + 3), (secondK k r w.val v.val).testBit (k - h + j.val) = false := by
        intro j
        exact (lt_two_pow_iff_high_bits_false (secondIter_lt v.isLt r)).mp hwS
          (k - h + j.val) (by omega) (by omega)
      rcases decodeNat_props hr hk u.isLt v.isLt label with ⟨hseedD, hcanD, hfD, hsD⟩
      have hwEq : w = decode label := by
        apply Fin.ext
        apply unique_normalized hr hk u.isLt v.isLt w.isLt (decodeNat_lt hr hk label)
        · intro j
          exact (hseedD j).symm
        · exact hwCan
        · exact hcanD
        · exact hwF
        · exact hfD
        · exact hwSel
        · exact hsD
      exact ⟨label, by rw [← hwEq]; exact ⟨hwF, hwS⟩⟩
    · rintro ⟨label, hjoint⟩
      exact ⟨decode label, hjoint⟩
