import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_378_aux

def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

def step (k x : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i)
      (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

def stateAux (k : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (w : Fin (2 ^ k)) (t : Nat) : Nat :=
  (List.range t).foldl (fun prev j =>
    step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * j) w.val ^^^ (c (j + 1)).val)
    (rot k 1 w.val ^^^ u.val)

lemma rot_lt (k s w : Nat) : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_rot (k s w i : Nat) (hw : w < 2 ^ k) (hi : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hs : s % k < k := Nat.mod_lt s hk
  unfold rot
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hfalse : w.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hfalse, Bool.or_false, hmod]
  · have hlt : i + k - s % k < k := by omega
    have hmod : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt hlt]
      omega
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hmod]

lemma foldl_step_props (k x : Nat) (n : Nat) (hn : n ≤ k) :
    let f := fun (acc i : Nat) =>
      acc ||| ((xor (x.testBit i)
        (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)
    (List.range n).foldl f 0 < 2 ^ n ∧
    ∀ i < n, ((List.range n).foldl f 0).testBit i =
      xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k)) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    intro i hi
    omega
  | succ m ih =>
    obtain ⟨hlt, hbit⟩ := ih (by omega)
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    dsimp only
    rw [hr, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range m).foldl (fun acc i =>
      acc ||| ((xor (x.testBit i)
        (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
    set b := xor (x.testBit m) (!(x.testBit ((m + 1) % k)) && x.testBit ((m + 2) % k))
    have hlt_b : b.toNat <<< m < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ']
      cases b <;> simp
    have hlt_acc : acc < 2 ^ (m + 1) :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨Nat.or_lt_two_pow hlt_acc hlt_b, ?_⟩
    intro i hi
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.or_false]
      exact hbit i him
    · have heq : i = m := by omega
      subst heq
      have hacc_false : acc.testBit i = false := Nat.testBit_lt_two_pow hlt
      rw [hacc_false, Bool.false_or, decide_eq_true (Nat.le_refl i), Bool.true_and, Nat.sub_self]
      show b.toNat.testBit 0 = b
      cases b <;> rfl

lemma step_lt (k x : Nat) : step k x < 2 ^ k :=
  (foldl_step_props k x k (Nat.le_refl k)).1

lemma testBit_step (k x i : Nat) (hi : i < k) :
    (step k x).testBit i =
      xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k)) :=
  (foldl_step_props k x k (Nat.le_refl k)).2 i hi

lemma stateAux_zero (k : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (w : Fin (2 ^ k)) :
    stateAux k u c w 0 = rot k 1 w.val ^^^ u.val := rfl

lemma stateAux_succ (k : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (w : Fin (2 ^ k)) (t : Nat) :
    stateAux k u c w (t + 1) =
      step k (stateAux k u c w t ^^^ rot k 1 (stateAux k u c w t) ^^^ rot k (k - 1) (stateAux k u c w t)) ^^^
      rot k (2 * t) w.val ^^^ (c (t + 1)).val := by
  unfold stateAux
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma stateAux_lt (k : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (w : Fin (2 ^ k)) (t : Nat) :
    stateAux k u c w t < 2 ^ k := by
  induction t with
  | zero =>
    rw [stateAux_zero]
    exact Nat.xor_lt_two_pow (rot_lt k 1 w.val) u.isLt
  | succ m _ =>
    rw [stateAux_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k (2 * m) w.val)) (c (m + 1)).isLt

lemma mod_add_sub_cancel (k p d : Nat) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ((p + d) % k + k - 1 % k) % k = (p + (d - 1)) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp [Nat.mod_one]
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : (p + d) % k < k := Nat.mod_lt _ (by omega)
    have hdiv := Nat.div_add_mod (p + d) k
    have h2 : (p + d) % k + k - 1 = (p + (d - 1)) + k - k * ((p + d) / k) := by omega
    have h3 : ((p + d) % k + k - 1) + k * ((p + d) / k) = (p + (d - 1)) + k := by omega
    have h4 := congrArg (· % k) h3
    simp only [Nat.add_mul_mod_self_left, Nat.add_mod_right] at h4
    exact h4

lemma mod_add_one (k p d : Nat) :
    ((p + d) % k + 1) % k = (p + (d + 1)) % k := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma mod_add_two (k p d : Nat) :
    ((p + d) % k + 2) % k = (p + (d + 2)) % k := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma testBit_rot_k_sub_1 (k prev q : Nat) (hk : 2 ≤ k) (hprev : prev < 2 ^ k) (hq : q < k) :
    (rot k (k - 1) prev).testBit q = prev.testBit ((q + 1) % k) := by
  rw [testBit_rot k (k - 1) prev q hprev hq]
  have h1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : q + k - (k - 1) = q + 1 := by omega
  rw [h2]

lemma testBit_lin (k prev q : Nat) (hk : 2 ≤ k) (hprev : prev < 2 ^ k) (hq : q < k) :
    (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev).testBit q =
      xor (xor (prev.testBit q) (prev.testBit ((q + k - 1 % k) % k))) (prev.testBit ((q + 1) % k)) := by
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot k 1 prev q hprev hq,
      testBit_rot_k_sub_1 k prev q hk hprev hq]

lemma step_lin_eq (k prev1 prev2 p d : Nat) (hk : 2 ≤ k)
    (hp1 : prev1 < 2 ^ k) (hp2 : prev2 < 2 ^ k) (hd : 1 ≤ d)
    (h0 : prev1.testBit ((p + d) % k) = prev2.testBit ((p + d) % k))
    (h1 : prev1.testBit ((p + (d + 1)) % k) = prev2.testBit ((p + (d + 1)) % k))
    (h2 : prev1.testBit ((p + (d + 2)) % k) = prev2.testBit ((p + (d + 2)) % k))
    (h3 : prev1.testBit ((p + (d + 3)) % k) = prev2.testBit ((p + (d + 3)) % k)) :
    let x1 := prev1 ^^^ rot k 1 prev1 ^^^ rot k (k - 1) prev1
    let x2 := prev2 ^^^ rot k 1 prev2 ^^^ rot k (k - 1) prev2
    xor ((step k x1).testBit ((p + d) % k)) ((step k x2).testBit ((p + d) % k)) =
      xor (prev1.testBit ((p + (d - 1)) % k)) (prev2.testBit ((p + (d - 1)) % k)) := by
  dsimp only
  have hq0 : (p + d) % k < k := Nat.mod_lt _ (by omega)
  have hq1 : (p + (d + 1)) % k < k := Nat.mod_lt _ (by omega)
  have hq2 : (p + (d + 2)) % k < k := Nat.mod_lt _ (by omega)
  rw [testBit_step k _ _ hq0, testBit_step k _ _ hq0]
  rw [mod_add_one k p d, mod_add_two k p d]
  rw [testBit_lin k prev1 _ hk hp1 hq0, testBit_lin k prev2 _ hk hp2 hq0]
  rw [testBit_lin k prev1 _ hk hp1 hq1, testBit_lin k prev2 _ hk hp2 hq1]
  rw [testBit_lin k prev1 _ hk hp1 hq2, testBit_lin k prev2 _ hk hp2 hq2]
  rw [mod_add_sub_cancel k p d (by omega) hd,
      mod_add_sub_cancel k p (d + 1) (by omega) (by omega),
      mod_add_sub_cancel k p (d + 2) (by omega) (by omega)]
  rw [mod_add_one k p d, mod_add_one k p (d + 1), mod_add_one k p (d + 2)]
  have hm1 : d + 1 - 1 = d := by omega
  have hm2 : d + 2 - 1 = d + 1 := by omega
  have ha2 : d + 1 + 1 = d + 2 := by omega
  have ha3 : d + 2 + 1 = d + 3 := by omega
  rw [hm1, hm2, ha2, ha3, h0, h1, h2, h3]
  cases prev1.testBit ((p + (d - 1)) % k) <;>
  cases prev2.testBit ((p + (d - 1)) % k) <;>
  cases prev2.testBit ((p + d) % k) <;>
  cases prev2.testBit ((p + (d + 1)) % k) <;>
  cases prev2.testBit ((p + (d + 2)) % k) <;>
  cases prev2.testBit ((p + (d + 3)) % k) <;> rfl

lemma key_xor_eq_start_xor (k j : Nat) (u w v : Fin (2 ^ k)) (p d : Nat)
    (hk : 2 ≤ k) (hge : 2 * j ≤ d + 1) :
    xor ((rot k (2 * j) w.val).testBit ((p + d) % k)) ((rot k (2 * j) v.val).testBit ((p + d) % k)) =
      xor ((rot k 1 w.val ^^^ u.val).testBit ((p + (d + 1 - 2 * j)) % k))
          ((rot k 1 v.val ^^^ u.val).testBit ((p + (d + 1 - 2 * j)) % k)) := by
  have hq : (p + d) % k < k := Nat.mod_lt _ (by omega)
  have ht : (p + (d + 1 - 2 * j)) % k < k := Nat.mod_lt _ (by omega)
  rw [testBit_rot k (2 * j) w.val _ w.isLt hq, testBit_rot k (2 * j) v.val _ v.isLt hq]
  rw [Nat.testBit_xor, Nat.testBit_xor,
      testBit_rot k 1 w.val _ w.isLt ht, testBit_rot k 1 v.val _ v.isLt ht]
  have hidx : ((p + d) % k + k - (2 * j) % k) % k =
      ((p + (d + 1 - 2 * j)) % k + k - 1 % k) % k := by
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have ha := Nat.div_add_mod (p + d) k
    have hb := Nat.div_add_mod (2 * j) k
    have hc := Nat.div_add_mod (p + (d + 1 - 2 * j)) k
    have hm1 : (p + d) % k < k := Nat.mod_lt _ (by omega)
    have hm2 : (2 * j) % k < k := Nat.mod_lt _ (by omega)
    have hm3 : (p + (d + 1 - 2 * j)) % k < k := Nat.mod_lt _ (by omega)
    have heq1 : ((p + d) % k + k - (2 * j) % k) + (2 * j) + k * ((p + d) / k) =
        ((p + (d + 1 - 2 * j)) % k + k - 1) + (2 * j) + k * ((p + (d + 1 - 2 * j)) / k) + k * ((2 * j) / k) := by
      omega
    have hmod_eq : (((p + d) % k + k - (2 * j) % k) + k * ((p + d) / k) + (2 * j)) % k =
        (((p + (d + 1 - 2 * j)) % k + k - 1) + k * ((p + (d + 1 - 2 * j)) / k) + k * ((2 * j) / k) + (2 * j)) % k := by
      congr 1; omega
    have hL : (((p + d) % k + k - (2 * j) % k) + k * ((p + d) / k) + (2 * j)) % k =
        (((p + d) % k + k - (2 * j) % k) + (2 * j)) % k := by
      rw [Nat.add_right_comm, Nat.add_mul_mod_self_left]
    have hR : (((p + (d + 1 - 2 * j)) % k + k - 1) + k * ((p + (d + 1 - 2 * j)) / k) + k * ((2 * j) / k) + (2 * j)) % k =
        (((p + (d + 1 - 2 * j)) % k + k - 1) + (2 * j)) % k := by
      have : ((p + (d + 1 - 2 * j)) % k + k - 1) + k * ((p + (d + 1 - 2 * j)) / k) + k * ((2 * j) / k) + (2 * j) =
          (((p + (d + 1 - 2 * j)) % k + k - 1) + (2 * j)) + k * (((p + (d + 1 - 2 * j)) / k) + ((2 * j) / k)) := by
        rw [Nat.mul_add]; omega
      rw [this, Nat.add_mul_mod_self_left]
    rw [hL, hR] at hmod_eq
    have hcancel : ∀ x y z : Nat, (x + z) % k = (y + z) % k → x % k = y % k := by
      intro x y z hxy
      have hxz : ((x + z) + (k - z % k)) % k = ((y + z) + (k - z % k)) % k := by
        rw [Nat.add_mod, hxy, ← Nat.add_mod]
      have hzlt : z % k < k := Nat.mod_lt z (by omega)
      have hzs : (z + (k - z % k)) % k = 0 := by
        have := Nat.div_add_mod z k
        have h1' : z + (k - z % k) = k * (z / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        rw [h1', Nat.mul_mod_right]
      have hl' : ((x + z) + (k - z % k)) % k = x % k := by
        rw [Nat.add_assoc, Nat.add_mod, hzs, Nat.add_zero, Nat.mod_mod]
      have hr' : ((y + z) + (k - z % k)) % k = y % k := by
        rw [Nat.add_assoc, Nat.add_mod, hzs, Nat.add_zero, Nat.mod_mod]
      rw [hl', hr'] at hxz
      exact hxz
    exact hcancel _ _ (2 * j) hmod_eq
  rw [hidx]
  cases w.val.testBit (((p + (d + 1 - 2 * j)) % k + k - 1 % k) % k) <;>
  cases v.val.testBit (((p + (d + 1 - 2 * j)) % k + k - 1 % k) % k) <;>
  cases u.val.testBit ((p + (d + 1 - 2 * j)) % k) <;> rfl

lemma xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

lemma state_xor_step (k : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k))
    (w v : Fin (2 ^ k)) (t p d : Nat) (hk : 2 ≤ k) (hd : 1 ≤ d) (hge : 2 * t ≤ d + 1)
    (h0 : (stateAux k u c w t).testBit ((p + d) % k) = (stateAux k u c v t).testBit ((p + d) % k))
    (h1 : (stateAux k u c w t).testBit ((p + (d + 1)) % k) = (stateAux k u c v t).testBit ((p + (d + 1)) % k))
    (h2 : (stateAux k u c w t).testBit ((p + (d + 2)) % k) = (stateAux k u c v t).testBit ((p + (d + 2)) % k))
    (h3 : (stateAux k u c w t).testBit ((p + (d + 3)) % k) = (stateAux k u c v t).testBit ((p + (d + 3)) % k)) :
    xor ((stateAux k u c w (t + 1)).testBit ((p + d) % k))
        ((stateAux k u c v (t + 1)).testBit ((p + d) % k)) =
      xor (xor ((stateAux k u c w t).testBit ((p + (d - 1)) % k))
               ((stateAux k u c v t).testBit ((p + (d - 1)) % k)))
          (xor ((rot k 1 w.val ^^^ u.val).testBit ((p + (d + 1 - 2 * t)) % k))
               ((rot k 1 v.val ^^^ u.val).testBit ((p + (d + 1 - 2 * t)) % k))) := by
  rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
  have hst := step_lin_eq k (stateAux k u c w t) (stateAux k u c v t) p d hk
    (stateAux_lt k u c w t) (stateAux_lt k u c v t) hd h0 h1 h2 h3
  have hky := key_xor_eq_start_xor k t u w v p d hk hge
  have hre : ∀ s1 s2 k1 k2 cc : Bool,
      xor (xor (xor s1 k1) cc) (xor (xor s2 k2) cc) = xor (xor s1 s2) (xor k1 k2) := by
    intro s1 s2 k1 k2 cc; cases s1 <;> cases s2 <;> cases k1 <;> cases k2 <;> cases cc <;> rfl
  rw [hre, hst, hky]

lemma state_agree_window (k _r : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k))
    (w v : Fin (2 ^ k)) (p : Nat) (width : Nat) (hk : 2 ≤ k)
    (hwin : ∀ d : Nat, 1 ≤ d → d ≤ width →
      (rot k 1 w.val ^^^ u.val).testBit ((p + d) % k) =
      (rot k 1 v.val ^^^ u.val).testBit ((p + d) % k)) :
    ∀ t : Nat, ∀ d : Nat, max t (2 * t - 3) + 1 ≤ d → d + 3 * t ≤ width →
      (stateAux k u c w t).testBit ((p + d) % k) =
      (stateAux k u c v t).testBit ((p + d) % k) := by
  intro t
  induction t with
  | zero =>
    intro d hd1 hd2
    rw [stateAux_zero, stateAux_zero]
    exact hwin d (by omega) (by omega)
  | succ m ih =>
    intro d hd1 hd2
    have hL : max m (2 * m - 3) + 1 ≤ d - 1 := by omega
    have hge : 2 * m ≤ d := by omega
    have hm1 : (stateAux k u c w m).testBit ((p + (d - 1)) % k) =
               (stateAux k u c v m).testBit ((p + (d - 1)) % k) :=
      ih (d - 1) hL (by omega)
    have h0 := ih d (by omega) (by omega)
    have h1 := ih (d + 1) (by omega) (by omega)
    have h2 := ih (d + 2) (by omega) (by omega)
    have h3 := ih (d + 3) (by omega) (by omega)
    have hxor := state_xor_step k u c w v m p d hk (by omega) (by omega) h0 h1 h2 h3
    have hkey : (rot k 1 w.val ^^^ u.val).testBit ((p + (d + 1 - 2 * m)) % k) =
                (rot k 1 v.val ^^^ u.val).testBit ((p + (d + 1 - 2 * m)) % k) :=
      hwin (d + 1 - 2 * m) (by omega) (by omega)
    rw [hm1, hkey] at hxor
    have hff : xor (xor ((stateAux k u c v m).testBit ((p + (d - 1)) % k))
                        ((stateAux k u c v m).testBit ((p + (d - 1)) % k)))
                   (xor ((rot k 1 v.val ^^^ u.val).testBit ((p + (d + 1 - 2 * m)) % k))
                        ((rot k 1 v.val ^^^ u.val).testBit ((p + (d + 1 - 2 * m)) % k))) = false := by
      simp
    rw [hff] at hxor
    exact (xor_eq_false_iff _ _).mp hxor

end PEqualNP.Outside.L_lib_378_aux

open PEqualNP.Outside.L_lib_378_aux in
theorem PEqualNP.Outside.L_lib_378 : (∀ (k r : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)),
  1 ≤ r → r ≠ 3 →
  let left := max r (2 * r - 3)
  let width := left + 3 * r
  width < k →
  let rot := fun (s w : Nat) =>
    ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k
  let step := fun (x : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (x.testBit i)
        (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
  let start := fun (w : Fin (2 ^ k)) => rot 1 w.val ^^^ u.val
  let state := fun (w : Fin (2 ^ k)) =>
    (List.range r).foldl (fun prev j =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * j) w.val ^^^ (c (j + 1)).val)
      (start w)
  ∀ (i : Fin k) (w v : Fin (2 ^ k)),
    let p := (i.val + k - left) % k
    (∀ j : Fin width,
      (start w).testBit ((p + 1 + j.val) % k) =
      (start v).testBit ((p + 1 + j.val) % k)) →
    xor ((state w).testBit i.val) ((state v).testBit i.val) =
      xor ((start w).testBit p) ((start v).testBit p)) := by
  intro k r u c hr hr3 left width hwk rotF stepF startF stateF i w v p hagree
  have hk2 : 2 ≤ k := by omega
  have hwin : ∀ d : Nat, 1 ≤ d → d ≤ width →
      (PEqualNP.Outside.L_lib_378_aux.rot k 1 w.val ^^^ u.val).testBit ((p + d) % k) =
      (PEqualNP.Outside.L_lib_378_aux.rot k 1 v.val ^^^ u.val).testBit ((p + d) % k) := by
    intro d hd1 hd2
    have h := hagree ⟨d - 1, by omega⟩
    have heq : p + 1 + (d - 1) = p + d := by omega
    change (PEqualNP.Outside.L_lib_378_aux.rot k 1 w.val ^^^ u.val).testBit ((p + 1 + (d - 1)) % k) =
      (PEqualNP.Outside.L_lib_378_aux.rot k 1 v.val ^^^ u.val).testBit ((p + 1 + (d - 1)) % k) at h
    rwa [heq] at h
  have hp_lt : p < k := Nat.mod_lt _ (by omega)
  have hi_eq : i.val = (p + left) % k := by
    have hleft_lt : left < k := by omega
    have h1 : (i.val + k - left) + left = i.val + k := by omega
    have h2 : (p + left) % k = ((i.val + k - left) + left) % k := by
      simp only [p, Nat.mod_add_mod]
    rw [h2, h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hp0 : (p + 0) % k = p := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt hp_lt]
  change xor ((stateAux k u c w r).testBit i.val) ((stateAux k u c v r).testBit i.val) =
    xor ((PEqualNP.Outside.L_lib_378_aux.rot k 1 w.val ^^^ u.val).testBit p)
        ((PEqualNP.Outside.L_lib_378_aux.rot k 1 v.val ^^^ u.val).testBit p)
  rw [hi_eq]
  have hcases : r = 1 ∨ r = 2 ∨ 4 ≤ r := by omega
  rcases hcases with rfl | rfl | hr4
  · have hleft1 : left = 1 := by simp [left]
    have hwidth1 : width = 4 := by simp [width, left]
    rw [hleft1]
    have h0 := state_agree_window k 1 u c w v p width hk2 hwin 0 1 (by omega) (by omega)
    have h1 := state_agree_window k 1 u c w v p width hk2 hwin 0 2 (by omega) (by omega)
    have h2 := state_agree_window k 1 u c w v p width hk2 hwin 0 3 (by omega) (by omega)
    have h3 := state_agree_window k 1 u c w v p width hk2 hwin 0 4 (by omega) (by omega)
    have hxor := state_xor_step k u c w v 0 p 1 hk2 (by omega) (by omega) h0 h1 h2 h3
    have hkey := hwin 2 (by omega) (by omega)
    rw [stateAux_zero, stateAux_zero] at hxor
    simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero, hp0, hkey, Bool.xor_self, Bool.xor_false] at hxor
    exact hxor
  · have hleft2 : left = 2 := by simp [left]
    have hwidth2 : width = 8 := by simp [width, left]
    rw [hleft2]
    have hs1 : xor ((stateAux k u c w 1).testBit ((p + 1) % k))
                   ((stateAux k u c v 1).testBit ((p + 1) % k)) =
               xor ((PEqualNP.Outside.L_lib_378_aux.rot k 1 w.val ^^^ u.val).testBit p)
                   ((PEqualNP.Outside.L_lib_378_aux.rot k 1 v.val ^^^ u.val).testBit p) := by
      have h0 := state_agree_window k 2 u c w v p width hk2 hwin 0 1 (by omega) (by omega)
      have h1 := state_agree_window k 2 u c w v p width hk2 hwin 0 2 (by omega) (by omega)
      have h2 := state_agree_window k 2 u c w v p width hk2 hwin 0 3 (by omega) (by omega)
      have h3 := state_agree_window k 2 u c w v p width hk2 hwin 0 4 (by omega) (by omega)
      have hxor := state_xor_step k u c w v 0 p 1 hk2 (by omega) (by omega) h0 h1 h2 h3
      have hkey := hwin 2 (by omega) (by omega)
      rw [stateAux_zero, stateAux_zero] at hxor
      simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero, hp0, hkey, Bool.xor_self, Bool.xor_false] at hxor
      exact hxor
    have h0 := state_agree_window k 2 u c w v p width hk2 hwin 1 2 (by omega) (by omega)
    have h1 := state_agree_window k 2 u c w v p width hk2 hwin 1 3 (by omega) (by omega)
    have h2 := state_agree_window k 2 u c w v p width hk2 hwin 1 4 (by omega) (by omega)
    have h3 := state_agree_window k 2 u c w v p width hk2 hwin 1 5 (by omega) (by omega)
    have hxor := state_xor_step k u c w v 1 p 2 hk2 (by omega) (by omega) h0 h1 h2 h3
    have hkey := hwin 1 (by omega) (by omega)
    simp only [show 2 - 1 = 1 by rfl, hkey, Bool.xor_self, Bool.xor_false] at hxor
    rw [hs1] at hxor
    exact hxor
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hm1 := state_agree_window k (m + 1) u c w v p width hk2 hwin m (left - 1) (by omega) (by omega)
    have h0 := state_agree_window k (m + 1) u c w v p width hk2 hwin m left (by omega) (by omega)
    have h1 := state_agree_window k (m + 1) u c w v p width hk2 hwin m (left + 1) (by omega) (by omega)
    have h2 := state_agree_window k (m + 1) u c w v p width hk2 hwin m (left + 2) (by omega) (by omega)
    have h3 := state_agree_window k (m + 1) u c w v p width hk2 hwin m (left + 3) (by omega) (by omega)
    have hxor := state_xor_step k u c w v m p left hk2 (by omega) (by omega) h0 h1 h2 h3
    have hzero : left + 1 - 2 * m = 0 := by omega
    rw [hm1, hzero, hp0, Bool.xor_self, Bool.false_xor] at hxor
    exact hxor
