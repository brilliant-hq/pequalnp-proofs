import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_25521

def rot (k s word : ℕ) : ℕ := ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0

def first (k u c key : ℕ) : ℕ :=
  step k ((rot k 1 key ^^^ u) ^^^ rot k 1 (rot k 1 key ^^^ u) ^^^ rot k (k - 1) (rot k 1 key ^^^ u))
    ^^^ key ^^^ c

theorem rot_lt (k s w : ℕ) : rot k s w < 2 ^ k := Nat.mod_lt _ (by positivity)

theorem rot_testBit {k s w b : ℕ} (hw : w < 2 ^ k) (hb : b < k) (hs : s % k < k) :
    (rot k s w).testBit b = w.testBit ((b + (k - s % k)) % k) := by
  unfold rot
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hb, decide_true, Bool.true_and]
  by_cases h : s % k ≤ b
  · have e1 : (b + (k - s % k)) % k = b - s % k := by
      have : b + (k - s % k) = k + (b - s % k) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : w.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [e1, e2]; simp [h]
  · have e1 : (b + (k - s % k)) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e1]; simp [h]

theorem fold_testBit (g : ℕ → Bool) (n j : ℕ) :
    ((List.range n).foldl (fun acc b => acc ||| ((g b).toNat <<< b)) 0).testBit j
      = (decide (j < n) && g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih,
      Nat.testBit_shiftLeft]
    by_cases h1 : j < n
    · have h2 : ¬ (j ≥ n) := by omega
      have h3 : j < n + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : j = n
      · subst h2; cases g j <;> simp
      · have h3 : j - n ≠ 0 := by omega
        have h4 : ¬ j < n + 1 := by omega
        cases g n <;> simp [h1, h4] <;>
          (intro _; exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h3))

theorem step_testBit (k y b : ℕ) :
    (step k y).testBit b = (decide (b < k) &&
      xor (y.testBit b) (!(y.testBit ((b + 1) % k)) && y.testBit ((b + 2) % k))) :=
  fold_testBit _ k b


theorem val_add_nat {k : ℕ} [NeZero k] (z : ZMod k) (n : ℕ) : (z + (n : ZMod k)).val = (z.val + n) % k := by
  rw [← ZMod.val_natCast]; congr 1; push_cast; rw [ZMod.natCast_zmod_val]

theorem negcast {k : ℕ} {c : ℕ} (h : c ≤ k) : ((k - c : ℕ) : ZMod k) = -(c : ZMod k) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem val_sub_one {k : ℕ} [NeZero k] (hk : 1 ≤ k) (z : ZMod k) : (z - 1).val = (z.val + (k - 1)) % k := by
  rw [← val_add_nat, negcast hk]; congr 1; push_cast; ring

theorem val_add_one {k : ℕ} [NeZero k] (z : ZMod k) : (z + 1).val = (z.val + 1) % k := by
  rw [← val_add_nat]; simp

theorem val_add_two {k : ℕ} [NeZero k] (z : ZMod k) : (z + 2).val = (z.val + 2) % k := by
  rw [← val_add_nat]; simp

def Xz (k : ℕ) (w u : ℕ) (z : ZMod k) : Bool := xor (w.testBit (z - 1).val) (u.testBit z.val)

def Yz (k : ℕ) (w u : ℕ) (z : ZMod k) : Bool :=
  xor (xor (Xz k w u z) (Xz k w u (z - 1))) (Xz k w u (z + 1))

def Bz (k : ℕ) (w u c : ℕ) (z : ZMod k) : Bool :=
  xor (xor (xor (Yz k w u z) (!(Yz k w u (z + 1)) && Yz k w u (z + 2))) (w.testBit z.val))
    (c.testBit z.val)

theorem x_testBit {k : ℕ} [NeZero k] (hk : 2 ≤ k) {w : ℕ} (u : ℕ) (hw : w < 2 ^ k) (z : ZMod k) :
    (rot k 1 w ^^^ u).testBit z.val = Xz k w u z := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.testBit_xor, rot_testBit hw (ZMod.val_lt z) (Nat.mod_lt _ (by omega)), h1,
    ← val_sub_one (by omega)]
  rfl

theorem y_testBit {k : ℕ} [NeZero k] (hk : 2 ≤ k) {w u : ℕ} (hw : w < 2 ^ k) (hu : u < 2 ^ k) (z : ZMod k) :
    ((rot k 1 w ^^^ u) ^^^ rot k 1 (rot k 1 w ^^^ u) ^^^ rot k (k - 1) (rot k 1 w ^^^ u)).testBit z.val
      = Yz k w u z := by
  have hx : rot k 1 w ^^^ u < 2 ^ k := Nat.xor_lt_two_pow (rot_lt _ _ _) hu
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : k - (k - 1) = 1 := by omega
  rw [Nat.testBit_xor, Nat.testBit_xor, rot_testBit hx (ZMod.val_lt z) (Nat.mod_lt _ (by omega)),
    rot_testBit hx (ZMod.val_lt z) (Nat.mod_lt _ (by omega)), h1, h2, h3,
    ← val_sub_one (by omega), ← val_add_one, x_testBit hk u hw, x_testBit hk u hw, x_testBit hk u hw]
  rfl

theorem first_testBit {k : ℕ} [NeZero k] (hk : 2 ≤ k) {w u : ℕ} (c : ℕ) (hw : w < 2 ^ k) (hu : u < 2 ^ k) (z : ZMod k) :
    (first k u c w).testBit z.val = Bz k w u c z := by
  unfold first
  rw [Nat.testBit_xor, Nat.testBit_xor, step_testBit, ← val_add_one, ← val_add_two,
    y_testBit hk hw hu, y_testBit hk hw hu, y_testBit hk hw hu]
  simp [Bz, ZMod.val_lt z]

theorem toggle_testBit {k : ℕ} [NeZero k] {q : ℕ} (hq : q < k) (w : ℕ) (z : ZMod k) :
    (w ^^^ 2 ^ q).testBit z.val = xor (w.testBit z.val) (decide (z = (q : ZMod k))) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro h; rw [h, ZMod.natCast_zmod_val]
  · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hq]

theorem bool9 : ∀ a b c d e f g h i : Bool,
    xor (xor (xor (xor a g) d) (xor (xor b h) e)) (xor (xor c i) f)
      = xor (xor (xor (xor a d) (xor b e)) (xor c f)) (xor (xor g h) i) := by decide

theorem xor3 (m : ℕ) :
    xor (xor (decide (m = 1)) (decide (m = 2))) (decide (m = 0)) = decide (m < 3) := by
  by_cases h0 : m = 0
  · subst h0; simp
  · by_cases h1 : m = 1
    · subst h1; simp
    · by_cases h2 : m = 2
      · subst h2; simp
      · have : ¬ m < 3 := by omega
        simp [h0, h1, h2, this]

theorem cast_eq_small {k : ℕ} (hk : 3 ≤ k) (n c : ℕ) (hc : c < 3) :
    ((n : ZMod k) = (c : ZMod k)) ↔ n % k = c := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (a := c) (by omega)]

theorem toggle_Y {k : ℕ} [NeZero k] (hk : 3 ≤ k) {q : ℕ} (hq : q < k) (w u : ℕ) (z : ZMod k) (n : ℕ)
    (hn : z - (q : ZMod k) = (n : ZMod k)) :
    Yz k (w ^^^ 2 ^ q) u z = xor (Yz k w u z) (decide (n % k < 3)) := by
  have e1 : (z - 1 = (q : ZMod k)) ↔ n % k = 1 := by
    rw [← cast_eq_small hk n 1 (by norm_num), ← hn]; push_cast
    constructor <;> intro h <;> linear_combination h
  have e2 : (z - 1 - 1 = (q : ZMod k)) ↔ n % k = 2 := by
    rw [← cast_eq_small hk n 2 (by norm_num), ← hn]; push_cast
    constructor <;> intro h <;> linear_combination h
  have e0 : (z + 1 - 1 = (q : ZMod k)) ↔ n % k = 0 := by
    rw [← cast_eq_small hk n 0 (by norm_num), ← hn]; push_cast
    constructor <;> intro h <;> linear_combination h
  rw [← xor3 (n % k)]
  simp only [Yz, Xz, toggle_testBit hq, decide_eq_decide.mpr e1, decide_eq_decide.mpr e2,
    decide_eq_decide.mpr e0]
  exact bool9 _ _ _ _ _ _ _ _ _

def agB (y0 y1 y2 d0 d1 d2 dp : Bool) : Bool :=
  (xor y0 (!y1 && y2) == xor (xor (xor y0 d0) (!(xor y1 d1) && xor y2 d2)) dp)

theorem bool_ag : ∀ y0 y1 y2 d0 d1 d2 dp wb cb : Bool,
    (xor (xor (xor y0 (!y1 && y2)) wb) cb
      == xor (xor (xor (xor y0 d0) (!(xor y1 d1) && xor y2 d2)) (xor wb dp)) cb)
      = agB y0 y1 y2 d0 d1 d2 dp := by decide

theorem agB_far : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 false false false false = true := by decide
theorem agB_0 : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 false false true false = y1 := by decide
theorem agB_1 : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 false true true false = (y1 == y2) := by decide
theorem agB_2 : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 true true true true = (y1 == y2) := by decide
theorem agB_3 : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 true true false false = y2 := by decide
theorem agB_4 : ∀ y0 y1 y2 : Bool, agB y0 y1 y2 true false false false = false := by decide

def AG (k : ℕ) (w u c p : ℕ) (z : ZMod k) : Bool := Bz k w u c z == Bz k (w ^^^ 2 ^ p) u c z

theorem agree_gen {k : ℕ} [NeZero k] (hk : 3 ≤ k) {p : ℕ} (hp : p < k) (w u c n : ℕ) :
    AG k w u c p ((p : ZMod k) + (n : ZMod k))
      = agB (Yz k w u ((p : ZMod k) + (n : ZMod k))) (Yz k w u ((p : ZMod k) + (n : ZMod k) + 1))
          (Yz k w u ((p : ZMod k) + (n : ZMod k) + 2))
          (decide (n % k < 3)) (decide ((n + 1) % k < 3)) (decide ((n + 2) % k < 3))
          (decide (n % k = 0)) := by
  have h0 : (p : ZMod k) + (n : ZMod k) - (p : ZMod k) = (n : ZMod k) := by ring
  have h1 : (p : ZMod k) + (n : ZMod k) + 1 - (p : ZMod k) = ((n + 1 : ℕ) : ZMod k) := by
    push_cast; ring
  have h2 : (p : ZMod k) + (n : ZMod k) + 2 - (p : ZMod k) = ((n + 2 : ℕ) : ZMod k) := by
    push_cast; ring
  have hd : ((p : ZMod k) + (n : ZMod k) = (p : ZMod k)) ↔ n % k = 0 := by
    rw [← cast_eq_small hk n 0 (by norm_num)]; push_cast
    constructor <;> intro h <;> linear_combination h
  simp only [AG, Bz, toggle_Y hk hp w u _ n h0, toggle_Y hk hp w u _ (n + 1) h1,
    toggle_Y hk hp w u _ (n + 2) h2, toggle_testBit hp, decide_eq_decide.mpr hd]
  exact bool_ag _ _ _ _ _ _ _ _ _

theorem ag_far {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c n : ℕ) (h3 : 3 ≤ n) (hn : n + 3 ≤ k) :
    AG k w u c p ((p : ZMod k) + (n : ZMod k)) = true := by
  rw [agree_gen (by omega) hp, Nat.mod_eq_of_lt (show n < k by omega),
    Nat.mod_eq_of_lt (show n + 1 < k by omega), Nat.mod_eq_of_lt (show n + 2 < k by omega),
    decide_eq_false (show ¬ n < 3 by omega), decide_eq_false (show ¬ n + 1 < 3 by omega),
    decide_eq_false (show ¬ n + 2 < 3 by omega), decide_eq_false (show ¬ n = 0 by omega)]
  exact agB_far _ _ _

theorem ag_0 {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c : ℕ) :
    AG k w u c p ((p : ZMod k) + ((k - 2 : ℕ) : ZMod k)) = Yz k w u ((p : ZMod k) - 1) := by
  have hz : (p : ZMod k) + ((k - 2 : ℕ) : ZMod k) + 1 = (p : ZMod k) - 1 := by
    rw [negcast (by omega)]; push_cast; ring
  rw [agree_gen (by omega) hp, Nat.mod_eq_of_lt (show k - 2 < k by omega),
    Nat.mod_eq_of_lt (show k - 2 + 1 < k by omega), show k - 2 + 2 = k by omega, Nat.mod_self,
    decide_eq_false (show ¬ k - 2 < 3 by omega), decide_eq_false (show ¬ k - 2 + 1 < 3 by omega),
    decide_eq_true (show 0 < 3 by norm_num), decide_eq_false (show ¬ k - 2 = 0 by omega), agB_0, hz]

theorem ag_1 {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c : ℕ) :
    AG k w u c p ((p : ZMod k) + ((k - 1 : ℕ) : ZMod k))
      = (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)) := by
  have hz : (p : ZMod k) + ((k - 1 : ℕ) : ZMod k) + 1 = (p : ZMod k) := by
    rw [negcast (by omega)]; push_cast; ring
  have hz2 : (p : ZMod k) + ((k - 1 : ℕ) : ZMod k) + 2 = (p : ZMod k) + 1 := by
    rw [negcast (by omega)]; push_cast; ring
  rw [agree_gen (by omega) hp, Nat.mod_eq_of_lt (show k - 1 < k by omega),
    show k - 1 + 1 = k by omega, Nat.mod_self, show k - 1 + 2 = k + 1 by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show 1 < k by omega),
    decide_eq_false (show ¬ k - 1 < 3 by omega), decide_eq_true (show 0 < 3 by norm_num),
    decide_eq_true (show 1 < 3 by norm_num), decide_eq_false (show ¬ k - 1 = 0 by omega), agB_1,
    hz, hz2]

theorem ag_2 {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c : ℕ) :
    AG k w u c p ((p : ZMod k) + ((k : ℕ) : ZMod k))
      = (Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2)) := by
  have hz : (p : ZMod k) + ((k : ℕ) : ZMod k) + 1 = (p : ZMod k) + 1 := by
    rw [ZMod.natCast_self]; ring
  have hz2 : (p : ZMod k) + ((k : ℕ) : ZMod k) + 2 = (p : ZMod k) + 2 := by
    rw [ZMod.natCast_self]; ring
  rw [agree_gen (by omega) hp, Nat.mod_self, Nat.add_mod_left, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt (show 2 < k by omega),
    decide_eq_true (show 0 < 3 by norm_num), decide_eq_true (show 1 < 3 by norm_num),
    decide_eq_true (show 2 < 3 by norm_num), decide_eq_true (show (0 : ℕ) = 0 by rfl), agB_2,
    hz, hz2]

theorem ag_3 {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c : ℕ) :
    AG k w u c p ((p : ZMod k) + ((k + 1 : ℕ) : ZMod k)) = Yz k w u ((p : ZMod k) + 3) := by
  have hz2 : (p : ZMod k) + ((k + 1 : ℕ) : ZMod k) + 2 = (p : ZMod k) + 3 := by
    push_cast; rw [ZMod.natCast_self]; ring
  rw [agree_gen (by omega) hp, show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega,
    Nat.add_mod_left, Nat.add_mod_left, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show 1 < k by omega), Nat.mod_eq_of_lt (show 2 < k by omega),
    Nat.mod_eq_of_lt (show 3 < k by omega),
    decide_eq_true (show 1 < 3 by norm_num), decide_eq_true (show 2 < 3 by norm_num),
    decide_eq_false (show ¬ 3 < 3 by norm_num), decide_eq_false (show ¬ (1 : ℕ) = 0 by norm_num),
    agB_3, hz2]

theorem ag_4 {k : ℕ} [NeZero k] (hk : 5 ≤ k) {p : ℕ} (hp : p < k) (w u c n : ℕ) (hn : n % k = 2) :
    AG k w u c p ((p : ZMod k) + (n : ZMod k)) = false := by
  have h1 : (n + 1) % k = 3 := by
    rw [Nat.add_mod, hn, Nat.mod_eq_of_lt (show 1 < k by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (n + 2) % k = 4 := by
    rw [Nat.add_mod, hn, Nat.mod_eq_of_lt (show 2 < k by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [agree_gen (by omega) hp, hn, h1, h2,
    decide_eq_true (show 2 < 3 by norm_num), decide_eq_false (show ¬ 3 < 3 by norm_num),
    decide_eq_false (show ¬ 4 < 3 by norm_num), decide_eq_false (show ¬ (2 : ℕ) = 0 by norm_num),
    agB_4]

def Cond (k : ℕ) (u p e w : ℕ) : Bool :=
  (((true && Yz k w u ((p : ZMod k) - 1))
    && (decide (e < 1) || (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1))))
    && (decide (e < 2) || (Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2))))
    && (decide (e < 3) || Yz k w u ((p : ZMod k) + 3))

theorem agrees_eq {k : ℕ} [NeZero k] (hk : 5 ≤ k) (r e : ℕ) (hr : 4 ≤ r) (hke : k + 3 + e = 5 * r) {p : ℕ}
    (hp : p < k) (w u c : ℕ) :
    (List.range (4 * r - 3)).all
        (fun j => AG k w u c p ((p : ZMod k) + ((r - 1 + j : ℕ) : ZMod k)))
      = if e < 4 then Cond k u p e w else false := by
  by_cases he : e < 4
  · rw [if_pos he]
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    constructor
    · intro h
      have m : ∀ j, j < 4 * r - 3 → j ∈ List.range (4 * r - 3) := fun j hj => List.mem_range.mpr hj
      have c0 := h (k - r - 1) (m _ (by omega))
      rw [show r - 1 + (k - r - 1) = k - 2 by omega, ag_0 hk hp] at c0
      have c1 : e < 1 ∨ (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)) = true := by
        by_cases h1 : e < 1
        · exact Or.inl h1
        · have := h (k - r) (m _ (by omega))
          rw [show r - 1 + (k - r) = k - 1 by omega, ag_1 hk hp] at this
          exact Or.inr this
      have c2 : e < 2 ∨ (Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2)) = true := by
        by_cases h1 : e < 2
        · exact Or.inl h1
        · have := h (k - r + 1) (m _ (by omega))
          rw [show r - 1 + (k - r + 1) = k by omega, ag_2 hk hp] at this
          exact Or.inr this
      have c3 : e < 3 ∨ Yz k w u ((p : ZMod k) + 3) = true := by
        by_cases h1 : e < 3
        · exact Or.inl h1
        · have := h (k - r + 2) (m _ (by omega))
          rw [show r - 1 + (k - r + 2) = k + 1 by omega, ag_3 hk hp] at this
          exact Or.inr this
      simp only [Cond, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.true_and]
      exact ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩
    · intro hc j hj
      simp only [Cond, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.true_and] at hc
      obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := hc
      have hj' : j < 4 * r - 3 := List.mem_range.mp hj
      have hcase : r - 1 + j + 3 ≤ k ∨ r - 1 + j = k - 2 ∨ r - 1 + j = k - 1 ∨ r - 1 + j = k
          ∨ r - 1 + j = k + 1 := by omega
      rcases hcase with h | h | h | h | h
      · exact ag_far hk hp w u c _ (by omega) h
      · rw [h, ag_0 hk hp]; exact c0
      · rw [h, ag_1 hk hp]; rcases c1 with c1 | c1
        · omega
        · exact c1
      · rw [h, ag_2 hk hp]; rcases c2 with c2 | c2
        · omega
        · exact c2
      · rw [h, ag_3 hk hp]; rcases c3 with c3 | c3
        · omega
        · exact c3
  · rw [if_neg he]
    cases hall : (List.range (4 * r - 3)).all
        (fun j => AG k w u c p ((p : ZMod k) + ((r - 1 + j : ℕ) : ZMod k)))
    · rfl
    · exfalso
      have hk0 : 0 < k := by omega
      have ha : (r - 1) % k < k := Nat.mod_lt _ hk0
      have hjlt : (k + 2 - (r - 1) % k) % k < 4 * r - 3 := by
        by_cases hkr : k ≤ 4 * r - 3
        · exact lt_of_lt_of_le (Nat.mod_lt _ hk0) hkr
        · have h1 : (r - 1) % k = r - 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1]
          exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
      have hmod : (r - 1 + (k + 2 - (r - 1) % k) % k) % k = 2 := by
        rw [Nat.add_mod, Nat.mod_mod]
        by_cases h2 : (r - 1) % k ≤ 2
        · rw [show k + 2 - (r - 1) % k = k + (2 - (r - 1) % k) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show 2 - (r - 1) % k < k by omega),
            show (r - 1) % k + (2 - (r - 1) % k) = 2 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        · rw [Nat.mod_eq_of_lt (show k + 2 - (r - 1) % k < k by omega),
            show (r - 1) % k + (k + 2 - (r - 1) % k) = k + 2 by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
      have := List.all_eq_true.mp hall _ (List.mem_range.mpr hjlt)
      rw [ag_4 hk hp w u c _ hmod] at this
      exact Bool.false_ne_true this

theorem pos_eq {k : ℕ} (hk : 1 ≤ k) (r i j : ℕ) (hr : 1 ≤ r) :
    ((((i + r * k + 1 - r) % k + j : ℕ)) : ZMod k)
      = (((i + (2 * r) * k + 2 - 2 * r) % k : ℕ) : ZMod k) + ((r - 1 + j : ℕ) : ZMod k) := by
  have h1 : r ≤ i + r * k + 1 := by nlinarith
  have h2 : 2 * r ≤ i + (2 * r) * k + 2 := by nlinarith
  push_cast [ZMod.natCast_mod]
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hr]
  push_cast
  rw [ZMod.natCast_self]
  ring

theorem list_card (n : ℕ) (f : ℕ → Bool) :
    ((List.range n).filter f).length = ((Finset.range n).filter (fun w => f w = true)).card := by
  rfl

theorem halve {k : ℕ} {q : ℕ} (hq : q < k) (Q Pb : ℕ → Bool) (hQ : ∀ w, Q (w ^^^ 2 ^ q) = Q w)
    (hP : ∀ w, Pb (w ^^^ 2 ^ q) = !Pb w) :
    2 * ((Finset.range (2 ^ k)).filter (fun w => (Q w && Pb w) = true)).card
      = ((Finset.range (2 ^ k)).filter (fun w => Q w = true)).card := by
  have hinv : ∀ w : ℕ, (w ^^^ 2 ^ q) ^^^ 2 ^ q = w := by
    intro w; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hlt : ∀ w : ℕ, w < 2 ^ k → w ^^^ 2 ^ q < 2 ^ k := fun w hw =>
    Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by norm_num) hq)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.range (2 ^ k)).filter (fun w => Q w = true)) (fun w => Pb w = true)
  rw [Finset.filter_filter, Finset.filter_filter] at hsum
  have hc : ((Finset.range (2 ^ k)).filter (fun w => Q w = true ∧ Pb w = true)).card
      = ((Finset.range (2 ^ k)).filter (fun w => Q w = true ∧ ¬ Pb w = true)).card := by
    apply Finset.card_bij (fun w _ => w ^^^ 2 ^ q)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      refine ⟨hlt a ha.1, ?_, ?_⟩
      · rw [hQ]; exact ha.2.1
      · rw [hP, ha.2.2]; simp
    · intro a _ b _ h
      have := congrArg (fun x => x ^^^ 2 ^ q) h
      simpa [hinv] using this
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨b ^^^ 2 ^ q, ?_, hinv b⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt b hb.1, ?_, ?_⟩
      · rw [hQ]; exact hb.2.1
      · rw [hP]; cases hpb : Pb b
        · rfl
        · exact absurd hpb hb.2.2
  have hand : ((Finset.range (2 ^ k)).filter (fun w => (Q w && Pb w) = true))
      = ((Finset.range (2 ^ k)).filter (fun w => Q w = true ∧ Pb w = true)) := by
    apply Finset.filter_congr; intro x _; simp
  rw [hand]; omega

theorem tY {k : ℕ} [NeZero k] (hk : 7 ≤ k) (Q z : ZMod k) (w u n : ℕ) (hn : z - Q = (n : ZMod k)) :
    Yz k (w ^^^ 2 ^ Q.val) u z = xor (Yz k w u z) (decide (n % k < 3)) :=
  toggle_Y (by omega) (ZMod.val_lt Q) w u z n (by rw [ZMod.natCast_zmod_val]; exact hn)

theorem tY_inv {k : ℕ} [NeZero k] (hk : 7 ≤ k) (Q z : ZMod k) (w u m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h : z - Q = -(m : ZMod k)) : Yz k (w ^^^ 2 ^ Q.val) u z = Yz k w u z := by
  rw [tY hk Q z w u (k - m) (by rw [negcast (by omega)]; exact h),
    Nat.mod_eq_of_lt (by omega), decide_eq_false (show ¬ k - m < 3 by omega)]
  simp

theorem tY_flip {k : ℕ} [NeZero k] (hk : 7 ≤ k) (Q z : ZMod k) (w u m : ℕ) (hm : m ≤ 2)
    (h : z - Q = (m : ZMod k)) : Yz k (w ^^^ 2 ^ Q.val) u z = !Yz k w u z := by
  rw [tY hk Q z w u m h, Nat.mod_eq_of_lt (by omega), decide_eq_true (show m < 3 by omega)]
  simp

theorem count {k : ℕ} [NeZero k] (hk : 7 ≤ k) (u p e : ℕ) (he : e < 4) :
    ((List.range (2 ^ k)).filter (fun w => Cond k u p e w)).length = 2 ^ (k - (e + 1)) := by
  rw [list_card]
  have f0 : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) - 3).val) u ((p : ZMod k) - 1)
      = !Yz k w u ((p : ZMod k) - 1) :=
    fun w => tY_flip hk _ _ w u 2 (by norm_num) (by push_cast; ring)
  have i1a : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 1).val) u ((p : ZMod k) - 1)
      = Yz k w u ((p : ZMod k) - 1) :=
    fun w => tY_inv hk _ _ w u 2 (by norm_num) (by norm_num) (by push_cast; ring)
  have i1b : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 1).val) u (p : ZMod k) = Yz k w u (p : ZMod k) :=
    fun w => tY_inv hk _ _ w u 1 (by norm_num) (by norm_num) (by push_cast; ring)
  have f1 : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 1).val) u ((p : ZMod k) + 1)
      = !Yz k w u ((p : ZMod k) + 1) :=
    fun w => tY_flip hk _ _ w u 0 (by norm_num) (by push_cast; ring)
  have i2a : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 2).val) u ((p : ZMod k) - 1)
      = Yz k w u ((p : ZMod k) - 1) :=
    fun w => tY_inv hk _ _ w u 3 (by norm_num) (by norm_num) (by push_cast; ring)
  have i2b : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 2).val) u (p : ZMod k) = Yz k w u (p : ZMod k) :=
    fun w => tY_inv hk _ _ w u 2 (by norm_num) (by norm_num) (by push_cast; ring)
  have i2c : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 2).val) u ((p : ZMod k) + 1)
      = Yz k w u ((p : ZMod k) + 1) :=
    fun w => tY_inv hk _ _ w u 1 (by norm_num) (by norm_num) (by push_cast; ring)
  have f2 : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 2).val) u ((p : ZMod k) + 2)
      = !Yz k w u ((p : ZMod k) + 2) :=
    fun w => tY_flip hk _ _ w u 0 (by norm_num) (by push_cast; ring)
  have i3a : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 3).val) u ((p : ZMod k) - 1)
      = Yz k w u ((p : ZMod k) - 1) :=
    fun w => tY_inv hk _ _ w u 4 (by norm_num) (by norm_num) (by push_cast; ring)
  have i3b : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 3).val) u (p : ZMod k) = Yz k w u (p : ZMod k) :=
    fun w => tY_inv hk _ _ w u 3 (by norm_num) (by norm_num) (by push_cast; ring)
  have i3c : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 3).val) u ((p : ZMod k) + 1)
      = Yz k w u ((p : ZMod k) + 1) :=
    fun w => tY_inv hk _ _ w u 2 (by norm_num) (by norm_num) (by push_cast; ring)
  have i3d : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 3).val) u ((p : ZMod k) + 2)
      = Yz k w u ((p : ZMod k) + 2) :=
    fun w => tY_inv hk _ _ w u 1 (by norm_num) (by norm_num) (by push_cast; ring)
  have f3 : ∀ w, Yz k (w ^^^ 2 ^ ((p : ZMod k) + 3).val) u ((p : ZMod k) + 3)
      = !Yz k w u ((p : ZMod k) + 3) :=
    fun w => tY_flip hk _ _ w u 0 (by norm_num) (by push_cast; ring)
  have H0 : ((Finset.range (2 ^ k)).filter (fun _ : ℕ => true = true)).card = 2 ^ k := by simp
  have H1 := halve (ZMod.val_lt ((p : ZMod k) - 3)) (fun _ => true)
    (fun w => Yz k w u ((p : ZMod k) - 1)) (fun _ => rfl) f0
  have H2 := halve (ZMod.val_lt ((p : ZMod k) + 1)) (fun w => true && Yz k w u ((p : ZMod k) - 1))
    (fun w => Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1))
    (fun w => by simp only [i1a])
    (fun w => by
      simp only [i1b, f1]
      cases Yz k w u (p : ZMod k) <;> cases Yz k w u ((p : ZMod k) + 1) <;> rfl)
  have H3 := halve (ZMod.val_lt ((p : ZMod k) + 2))
    (fun w => (true && Yz k w u ((p : ZMod k) - 1))
      && (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)))
    (fun w => Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2))
    (fun w => by simp only [i2a, i2b, i2c])
    (fun w => by
      simp only [i2c, f2]
      cases Yz k w u ((p : ZMod k) + 1) <;> cases Yz k w u ((p : ZMod k) + 2) <;> rfl)
  have H4 := halve (ZMod.val_lt ((p : ZMod k) + 3))
    (fun w => ((true && Yz k w u ((p : ZMod k) - 1))
      && (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)))
      && (Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2)))
    (fun w => Yz k w u ((p : ZMod k) + 3))
    (fun w => by simp only [i3a, i3b, i3c, i3d])
    f3
  have E1 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have E2 : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have E3 : (2 : ℕ) ^ k = 8 * 2 ^ (k - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  have E4 : (2 : ℕ) ^ k = 16 * 2 ^ (k - 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  interval_cases e
  · have hf : ((Finset.range (2 ^ k)).filter (fun w => Cond k u p 0 w = true))
        = ((Finset.range (2 ^ k)).filter
            (fun w => ((fun _ : ℕ => true) w && (fun w => Yz k w u ((p : ZMod k) - 1)) w) = true)) := by
      apply Finset.filter_congr; intro x _; simp [Cond]
    rw [hf]; simp only [Nat.zero_add] ; omega
  · have hf : ((Finset.range (2 ^ k)).filter (fun w => Cond k u p 1 w = true))
        = ((Finset.range (2 ^ k)).filter (fun w =>
            ((fun w => true && Yz k w u ((p : ZMod k) - 1)) w
              && (fun w => Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)) w) = true)) := by
      apply Finset.filter_congr; intro x _; simp [Cond]
    rw [hf]; simp only [Nat.reduceAdd]; omega
  · have hf : ((Finset.range (2 ^ k)).filter (fun w => Cond k u p 2 w = true))
        = ((Finset.range (2 ^ k)).filter (fun w =>
            ((fun w => (true && Yz k w u ((p : ZMod k) - 1))
                && (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1))) w
              && (fun w => Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2)) w) = true)) := by
      apply Finset.filter_congr; intro x _; simp [Cond]
    rw [hf]; simp only [Nat.reduceAdd]; omega
  · have hf : ((Finset.range (2 ^ k)).filter (fun w => Cond k u p 3 w = true))
        = ((Finset.range (2 ^ k)).filter (fun w =>
            ((fun w => ((true && Yz k w u ((p : ZMod k) - 1))
                && (Yz k w u (p : ZMod k) == Yz k w u ((p : ZMod k) + 1)))
                && (Yz k w u ((p : ZMod k) + 1) == Yz k w u ((p : ZMod k) + 2))) w
              && (fun w => Yz k w u ((p : ZMod k) + 3)) w) = true)) := by
      apply Finset.filter_congr; intro x _; simp [Cond]
    rw [hf]; simp only [Nat.reduceAdd]; omega


end PEqualNP.Outside.L_meta_25521

theorem PEqualNP.Outside.L_meta_25521 : (∀ (k r e : Nat), 4 ≤ r → 5 ≤ k → k + 3 + e = 5 * r →
  ∀ (u i : Nat) (constant : Fin (2 ^ k)), u < 2 ^ k → i < k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let first := fun (key : Nat) =>
    let x := rot 1 key ^^^ u
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ key ^^^ constant.val
  let keyBit := (i + (2 * r) * k + 2 - 2 * r) % k
  let left := (i + r * k + 1 - r) % k
  let agrees := fun (w : Nat) =>
    let before := first w
    let after := first (w ^^^ (1 <<< keyBit))
    (List.range (4 * r - 3)).all (fun j =>
      before.testBit ((left + j) % k) == after.testBit ((left + j) % k))
  ((List.range (2 ^ k)).filter agrees).length =
    (if e < 4 then 2 ^ (k - (e + 1)) else 0)) := by
  intro k r e hr hk hke u i constant hu hi
  intro rot step first keyBit left agrees
  have : NeZero k := ⟨by omega⟩
  have hp : keyBit < k := Nat.mod_lt _ (by omega)
  have key : ∀ w ∈ List.range (2 ^ k), agrees w
      = (if e < 4 then PEqualNP.Outside.L_meta_25521.Cond k u keyBit e w else false) := by
    intro w hw
    have hw' : w < 2 ^ k := List.mem_range.mp hw
    have hw2 : w ^^^ 2 ^ keyBit < 2 ^ k :=
      Nat.xor_lt_two_pow hw' (Nat.pow_lt_pow_right (by norm_num) hp)
    rw [← PEqualNP.Outside.L_meta_25521.agrees_eq hk r e hr hke hp w u constant.val]
    show (List.range (4 * r - 3)).all (fun j =>
        (PEqualNP.Outside.L_meta_25521.first k u constant.val w).testBit ((left + j) % k)
          == (PEqualNP.Outside.L_meta_25521.first k u constant.val
                (w ^^^ (1 <<< keyBit))).testBit ((left + j) % k)) = _
    congr 1
    funext j
    have hz : (left + j) % k = ((left + j : ℕ) : ZMod k).val := (ZMod.val_natCast _ _).symm
    rw [hz, Nat.one_shiftLeft,
      PEqualNP.Outside.L_meta_25521.first_testBit (by omega) constant.val hw' hu,
      PEqualNP.Outside.L_meta_25521.first_testBit (by omega) constant.val hw2 hu,
      PEqualNP.Outside.L_meta_25521.pos_eq (by omega) r i j (by omega)]
    rfl
  rw [List.filter_congr key]
  by_cases he : e < 4
  · simp only [if_pos he]
    exact PEqualNP.Outside.L_meta_25521.count (by omega) u keyBit e he
  · simp only [if_neg he]
    simp
