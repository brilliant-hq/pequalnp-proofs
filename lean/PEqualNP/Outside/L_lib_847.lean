import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_847

private theorem split_prime_power (p b : ℕ) (hb : 0 < b) : p ^ b = p * p ^ (b - 1) := by
  conv_lhs => rw [show b = (b - 1) + 1 by omega, pow_succ, mul_comm]

private theorem dvd_mul_choose (q j : ℕ) (hq : 0 < q) (hj : 0 < j) :
    q ∣ j * q.choose j := by
  have h := Nat.add_one_mul_choose_eq (q - 1) (j - 1)
  rw [show q - 1 + 1 = q by omega, show j - 1 + 1 = j by omega] at h
  rw [mul_comm j, ← h]
  exact dvd_mul_right ..

private theorem choose_dvd (p b j : ℕ) (hp : p.Prime)
    (hj : 0 < j) (hjq : j < p ^ b) : p ∣ (p ^ b).choose j := by
  have hdvd := dvd_mul_choose (p ^ b) j (pow_pos hp.pos _) hj
  by_contra hn
  have h := ((hp.coprime_iff_not_dvd.2 hn).pow_left b).dvd_of_dvd_mul_right hdvd
  exact (not_le_of_gt hjq) (Nat.le_of_dvd hj h)

private theorem choose_dvd_sq (p b j : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hj : 0 < j) (hjd : j < p ^ (b - 1)) (hjq : j < p ^ b) :
    p ^ 2 ∣ (p ^ b).choose j := by
  obtain ⟨k, hk⟩ := choose_dvd p b j hp hj hjq
  have hdvd := dvd_mul_choose (p ^ b) j (pow_pos hp.pos _) hj
  rw [hk, ← Nat.mul_assoc, Nat.mul_comm j p, Nat.mul_assoc, split_prime_power p b hb] at hdvd
  have hd : p ^ (b - 1) ∣ j * k := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
  have hpk : p ∣ k := by
    by_contra hn
    have hdj := ((hp.coprime_iff_not_dvd.2 hn).pow_left (b - 1)).dvd_of_dvd_mul_right hd
    exact (not_le_of_gt hjd) (Nat.le_of_dvd hj hdj)
  obtain ⟨l, hl⟩ := hpk
  exact ⟨l, by rw [hk, hl, pow_two, mul_assoc]⟩

private theorem minus_one_prime_pow (p m : ℕ) (hp : p.Prime) :
    (-1 : ZMod p) ^ (p ^ m) = -1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := add_pow_char_pow (p := p) (-1 : ZMod p) 1 m
  have hne : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [neg_add_cancel, zero_pow hne, one_pow] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem minus_one_before_prime_pow (p m : ℕ) (hp : p.Prime) :
    (-1 : ZMod p) ^ (p ^ m - 1) = 1 := by
  have hpos : 0 < p ^ m := pow_pos hp.pos _
  have h := minus_one_prime_pow p m hp
  conv_lhs at h => rw [show p ^ m = p ^ m - 1 + 1 by omega, pow_succ]
  simpa using h

private theorem choose_before_prime_pow (p b j : ℕ) (hp : p.Prime)
    (hj : j < p ^ b) : ((p ^ b - 1).choose j : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hq : 0 < p ^ b := pow_pos hp.pos _
    have h := Nat.choose_succ_succ' (p ^ b - 1) j
    rw [show p ^ b - 1 + 1 = p ^ b by omega] at h
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 (choose_dvd p b (j + 1) hp (by omega) hj)
    rw [h, Nat.cast_add, ih (by omega)] at hz
    rw [pow_succ, mul_neg, mul_one]
    exact eq_neg_of_add_eq_zero_right hz

private theorem choose_center (p b : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ ((p ^ b - 1).choose (p ^ (b - 1) - 1) : ℤ) - 1 := by
  have hd : p ^ (b - 1) ≤ p ^ b := pow_right_mono₀ hp.one_le (by omega)
  have hpos : 0 < p ^ (b - 1) := pow_pos hp.pos _
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  push_cast
  rw [choose_before_prime_pow p b _ hp (by omega), minus_one_before_prime_pow p _ hp, sub_self]

private theorem signed_choose (p b j : ℕ) (hp : p.Prime) (hj : j < p ^ b) :
    (p : ℤ) ∣ (-1 : ℤ) ^ (p ^ b - 1 - j) * ((p ^ b - 1).choose j : ℤ) - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  push_cast
  rw [choose_before_prime_pow p b j hp hj, ← pow_add,
    show p ^ b - 1 - j + j = p ^ b - 1 by omega, minus_one_before_prime_pow p b hp, sub_self]

private theorem choose_factor (p b j : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hj : j ∈ Finset.Ico 1 (p ^ b)) :
    let q := p ^ b
    let d := p ^ (b - 1)
    ∃ c w : ℕ, q.choose j = p ^ c * w ∧ q ≤ j + c * (q - d) ∧
      (j ≠ d → q < j + c * (q - d)) := by
  dsimp only
  obtain ⟨hj1, hjq⟩ := Finset.mem_Ico.1 hj
  have htwo : 2 * p ^ (b - 1) ≤ p ^ b := calc
    _ ≤ p * p ^ (b - 1) := Nat.mul_le_mul_right _ hp.two_le
    _ = _ := (split_prime_power p b hb).symm
  by_cases hd : p ^ (b - 1) ≤ j
  · obtain ⟨w, hw⟩ := choose_dvd p b j hp (by omega) hjq
    refine ⟨1, w, by simpa using hw, ?_, ?_⟩ <;> omega
  · obtain ⟨w, hw⟩ := choose_dvd_sq p b j hp hb (by omega) (by omega) hjq
    refine ⟨2, w, hw, ?_, ?_⟩ <;> omega

private theorem power_recurrence {B : Type*} [CommRing B] (q : ℕ) (hq : 0 < q)
    (X : B) (hX : X ^ q = 1) (t : ℕ) (ht : q ≤ t) :
    (X - 1) ^ t = -(∑ j ∈ Finset.Ico 1 q, (X - 1) ^ (t - q + j) * (q.choose j : B)) := by
  have hrange : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hbase : (X - 1) ^ q = -(∑ j ∈ Finset.Ico 1 q, (X - 1) ^ j * (q.choose j : B)) := by
    have h := add_pow (X - 1) (1 : B) q
    rw [sub_add_cancel, hX, Finset.sum_range_succ, hrange,
      Finset.sum_insert (by simp : 0 ∉ Finset.Ico 1 q)] at h
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at h
    linear_combination -h
  calc
    (X - 1) ^ t = (X - 1) ^ (t - q) * (X - 1) ^ q := by
      rw [← pow_add, Nat.sub_add_cancel ht]
    _ = _ := by simp_rw [hbase, mul_neg, Finset.mul_sum, ← mul_assoc, ← pow_add]

private theorem weighted_vanishing {B : Type*} [CommRing B] (p b a : ℕ)
    (hp : p.Prime) (hb : 0 < b) (ha : 0 < a) (X : B) (hX : X ^ (p ^ b) = 1)
    (hpzero : (p : B) ^ a = 0) (t e : ℕ)
    (hweight : p ^ b - 1 + (a - 1) * (p ^ b - p ^ (b - 1)) <
      t + e * (p ^ b - p ^ (b - 1))) :
    (p : B) ^ e * (X - 1) ^ t = 0 := by
  let q := p ^ b
  let d := p ^ (b - 1)
  let φ := q - d
  let L := q - 1 + (a - 1) * φ
  change L < t + e * φ at hweight
  have hq : 0 < q := pow_pos hp.pos _
  induction t using Nat.strong_induction_on generalizing e with
  | ind t ih =>
    by_cases ht : t < q
    · have he : a ≤ e := by
        by_contra hn
        have hle : e * φ ≤ (a - 1) * φ := Nat.mul_le_mul_right _ (by omega)
        dsimp only [L] at hweight
        omega
      rw [← Nat.add_sub_of_le he, pow_add, hpzero, zero_mul, zero_mul]
    · have htq : q ≤ t := by omega
      rw [power_recurrence q hq X hX t htq, mul_neg, Finset.mul_sum]
      apply neg_eq_zero.mpr
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨c, w, hw, hc, _⟩ := choose_factor p b j hp hb hj
      change q.choose j = p ^ c * w at hw
      change q ≤ j + c * φ at hc
      have hjq := (Finset.mem_Ico.1 hj).2
      have hzero := ih (t - q + j) (by omega) (e + c) (by rw [Nat.add_mul]; omega)
      calc
        _ = (p : B) ^ (e + c) * (X - 1) ^ (t - q + j) * (w : B) := by
          rw [hw, Nat.cast_mul, Nat.cast_pow, pow_add]
          ring
        _ = 0 := by rw [hzero, zero_mul]

private theorem mul_intCast_eq {B : Type*} [CommRing B] (p : ℕ) (u v : ℤ)
    (h : (p : ℤ) ∣ u - v) (z : B) (hz : (p : B) * z = 0) :
    z * (u : B) = z * (v : B) := by
  obtain ⟨w, hw⟩ := h
  have hw' := congrArg (fun c : ℤ => (c : B)) hw
  push_cast at hw'
  apply sub_eq_zero.mp
  rw [← mul_sub, hw', ← mul_assoc, mul_comm z, hz, zero_mul]

private theorem boundary_recurrence {B : Type*} [CommRing B] (p b a : ℕ)
    (hp : p.Prime) (hb : 0 < b) (ha : 0 < a) (X : B) (hX : X ^ (p ^ b) = 1)
    (hpzero : (p : B) ^ a = 0) (t e : ℕ) (ht : p ^ b ≤ t)
    (hweight : t + e * (p ^ b - p ^ (b - 1)) = p ^ b - 1 + (a - 1) * (p ^ b - p ^ (b - 1))) :
    (p : B) ^ e * (X - 1) ^ t = -((p : B) ^ (e + 1) * (X - 1) ^ (t - (p ^ b - p ^ (b - 1)))) := by
  let q := p ^ b
  let d := p ^ (b - 1)
  let φ := q - d
  let L := q - 1 + (a - 1) * φ
  change t + e * φ = L at hweight
  change q ≤ t at ht
  change _ = -((p : B) ^ (e + 1) * (X - 1) ^ (t - φ))
  have hq : 0 < q := pow_pos hp.pos _
  have hd : 0 < d := pow_pos hp.pos _
  have hqpd : q = p * d := split_prime_power p b hb
  have hdq : d < q := pow_lt_pow_right₀ hp.one_lt (by omega : b - 1 < b)
  have hw : q.choose d = p * (q - 1).choose (d - 1) := by
    simpa only [← hqpd] using Nat.choose_mul_right (m := p) (Nat.ne_of_gt hd)
  have ht' : t - q + d = t - φ := by dsimp only [φ]; omega
  rw [power_recurrence q hq X hX t ht, mul_neg, Finset.mul_sum, Finset.sum_eq_single d]
  · rw [ht', hw, Nat.cast_mul]
    let z := (p : B) ^ (e + 1) * (X - 1) ^ (t - φ)
    have hz : (p : B) * z = 0 := by
      calc
        _ = (p : B) ^ (e + 2) * (X - 1) ^ (t - φ) := by
          dsimp only [z]
          rw [show e + 2 = (e + 1) + 1 by omega, pow_succ]
          ring
        _ = 0 := by
          apply weighted_vanishing p b a hp hb ha X hX hpzero
          change L < t - φ + (e + 2) * φ
          have hφ : 0 < φ := by dsimp only [φ]; omega
          have hφt : φ ≤ t := by dsimp only [φ]; omega
          rw [Nat.add_mul]
          omega
    have heq := mul_intCast_eq p _ _ (choose_center p b hp) z hz
    push_cast at heq
    change z * ((q - 1).choose (d - 1) : B) = z * 1 at heq
    calc
      _ = -(z * ((q - 1).choose (d - 1) : B)) := by
        dsimp only [z]
        rw [pow_succ]
        ring
      _ = -z := by rw [heq, mul_one]
  · intro j hj hjd
    obtain ⟨c, w, hwj, _, hc⟩ := choose_factor p b j hp hb hj
    change q.choose j = p ^ c * w at hwj
    have hjw : q < j + c * φ := hc hjd
    have hzero : (p : B) ^ (e + c) * (X - 1) ^ (t - q + j) = 0 := by
      apply weighted_vanishing p b a hp hb ha X hX hpzero
      change L < t - q + j + (e + c) * φ
      rw [Nat.add_mul]
      omega
    calc
      _ = (p : B) ^ (e + c) * (X - 1) ^ (t - q + j) * (w : B) := by
        rw [hwj, Nat.cast_mul, Nat.cast_pow, pow_add]
        ring
      _ = 0 := by rw [hzero, zero_mul]
  · exact fun h => (h (Finset.mem_Ico.2 ⟨hd, hdq⟩)).elim

private theorem powers_at_cutoff {B : Type*} [CommRing B] (p b a : ℕ)
    (hp : p.Prime) (hb : 0 < b) (ha : 0 < a) (X : B) (hX : X ^ (p ^ b) = 1)
    (hpzero : (p : B) ^ a = 0) :
    let q := p ^ b
    let L := q - 1 + (a - 1) * (q - p ^ (b - 1))
    (X - 1) ^ L = (-(p : B)) ^ (a - 1) * (∑ j ∈ Finset.range q, X ^ j) ∧
      ∀ n > L, (X - 1) ^ n = 0 := by
  let q := p ^ b
  let φ := q - p ^ (b - 1)
  let L := q - 1 + (a - 1) * φ
  have hq : 0 < q := pow_pos hp.pos _
  have hφ : 0 < φ := by
    have hdq : p ^ (b - 1) < p ^ b := pow_lt_pow_right₀ hp.one_lt (by omega)
    exact Nat.sub_pos_of_lt hdq
  have hbdy (i e : ℕ) (hie : e + i = a - 1) :
      (p : B) ^ e * (X - 1) ^ (q - 1 + i * φ) =
        (-1 : B) ^ i * (p : B) ^ (e + i) * (X - 1) ^ (q - 1) := by
    induction i generalizing e with
    | zero => simp
    | succ i ih =>
      have ht : q ≤ q - 1 + (i + 1) * φ := by rw [Nat.add_mul]; omega
      have hw : q - 1 + (i + 1) * φ + e * φ = L := by
        dsimp only [L]
        rw [Nat.add_assoc, ← Nat.add_mul, show i + 1 + e = a - 1 by omega]
      have hr := boundary_recurrence p b a hp hb ha X hX hpzero _ e ht hw
      change _ = -((p : B) ^ (e + 1) * (X - 1) ^ (q - 1 + (i + 1) * φ - φ)) at hr
      rw [show q - 1 + (i + 1) * φ - φ = q - 1 + i * φ by rw [Nat.add_mul]; omega,
        ih (e + 1) (by omega)] at hr
      rw [hr, show e + 1 + i = e + (i + 1) by omega, pow_succ (-1 : B) i]
      ring
  have hL := hbdy (a - 1) 0 (by omega)
  simp only [pow_zero, one_mul, zero_add] at hL
  rw [← mul_pow, neg_one_mul] at hL
  change (X - 1) ^ L = _ ∧ ∀ n > L, (X - 1) ^ n = 0
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hL, sub_eq_add_neg, add_pow, show q - 1 + 1 = q by omega, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    let z := (-(p : B)) ^ (a - 1) * X ^ j
    have hz : (p : B) * z = 0 := by
      calc
        _ = (p : B) ^ a * ((-1 : B) ^ (a - 1) * X ^ j) := by
          dsimp only [z]
          have hpow : (p : B) ^ a = (p : B) ^ (a - 1) * p := by
            rw [← pow_succ, show a - 1 + 1 = a by omega]
          rw [neg_eq_neg_one_mul (p : B), mul_pow, hpow]
          ring
        _ = 0 := by rw [hpzero, zero_mul]
    have heq := mul_intCast_eq p _ _ (signed_choose p b j hp (Finset.mem_range.1 hj)) z hz
    push_cast at heq
    simpa only [z, mul_one, mul_assoc] using heq
  · simpa using weighted_vanishing p b a hp hb ha X hX hpzero n 0 (by simpa using hn)

private theorem binomial_recovery {B : Type*} [CommRing B] (X : B) (L : ℕ)
    (hvanish : ∀ n > L, (X - 1) ^ n = 0) (v : ℕ) :
    (∑ n ∈ Finset.range (L + 1), (X - 1) ^ n * (v.choose n : B)) = X ^ v := by
  have h := add_pow (X - 1) (1 : B) v
  simp only [sub_add_cancel, one_pow, mul_one] at h
  rw [h]
  by_cases hv : v ≤ L
  · symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    simp only [Finset.mem_range]
    intro n _ hn
    simp [Nat.choose_eq_zero_of_lt (show v < n by omega)]
  · refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    simp only [Finset.mem_range]
    intro n _ hn
    rw [hvanish n (by omega), zero_mul]

end PEqualNP.Outside.L_lib_847

open PEqualNP.Outside.L_lib_847 in
theorem PEqualNP.Outside.L_lib_847 : (∀ (p b a : ℕ), Nat.Prime p → 0 < b → 0 < a →
  let q := p^b
  let L := q-1+(a-1)*(q-q/p)
  let R := ZMod (p^a)
  let K := fun (n u : ℕ) =>
    ∑ j ∈ Finset.range (n+1),
      if j % q = u then (-1 : R)^(n-j) * (Nat.choose n j : R) else 0
  (∀ u < q, K L u = (-(p : R))^(a-1) ∧ K L u ≠ 0) ∧
  (∀ n > L, ∀ u < q, K n u = 0) ∧
  ∀ v : ℕ, ∀ u < q,
    (∑ n ∈ Finset.range (L+1), (Nat.choose v n : R) * K n u) =
      (if v % q = u then 1 else 0)) := by
  intro p b a hp hb ha
  let q := p ^ b
  let L := q - 1 + (a - 1) * (q - q / p)
  let R := ZMod (p ^ a)
  let K (n u : ℕ) : R := ∑ j ∈ Finset.range (n + 1),
    if j % q = u then (-1 : R) ^ (n - j) * (n.choose j : R) else 0
  change (∀ u < q, K L u = (-(p : R)) ^ (a - 1) ∧ K L u ≠ 0) ∧
    (∀ n > L, ∀ u < q, K n u = 0) ∧
    ∀ v : ℕ, ∀ u < q,
      (∑ n ∈ Finset.range (L + 1), (v.choose n : R) * K n u) = (if v % q = u then 1 else 0)
  let B := AddMonoidAlgebra R (ZMod q)
  let X : B := AddMonoidAlgebra.single (1 : ZMod q) (1 : R)
  let coeff (u : ℕ) : B →+ R :=
    { toFun := fun F => F.coeff (u : ZMod q)
      map_zero' := by simp
      map_add' := by intros; rfl }
  let scalar : R →+* B := AddMonoidAlgebra.singleZeroRingHom
  have hscalar (c : R) (F : B) (u : ℕ) : coeff u (scalar c * F) = c * coeff u F :=
    AddMonoidAlgebra.coeff_single_zero_mul ..
  have hXpow (v : ℕ) : X ^ v = AddMonoidAlgebra.single (v : ZMod q) (1 : R) := by
    change (AddMonoidAlgebra.single (1 : ZMod q) (1 : R)) ^ v = _
    rw [AddMonoidAlgebra.single_pow, one_pow, nsmul_one]
  have hX : X ^ (p ^ b) = 1 := by
    change X ^ q = 1
    rw [hXpow, ZMod.natCast_self, AddMonoidAlgebra.one_def]
  have hRzero : (p : R) ^ a = 0 := by
    simpa only [Nat.cast_pow] using ZMod.natCast_self (p ^ a)
  have hpzero : (p : B) ^ a = 0 := by
    simpa only [map_pow, map_natCast, map_zero] using congrArg scalar hRzero
  have hdiv : q / p = p ^ (b - 1) := by
    have hq : q = p * p ^ (b - 1) := split_prime_power p b hb
    rw [hq, Nat.mul_div_cancel_left _ hp.pos]
  have hcut := powers_at_cutoff p b a hp hb ha X hX hpzero
  change (X - 1) ^ (q - 1 + (a - 1) * (q - p ^ (b - 1))) = _ ∧
    (∀ n > q - 1 + (a - 1) * (q - p ^ (b - 1)), (X - 1) ^ n = 0) at hcut
  rw [← hdiv] at hcut
  obtain ⟨hboundary, hvanish⟩ := hcut
  have hdelta (v u : ℕ) (hu : u < q) :
      coeff u (X ^ v) = if v % q = u then 1 else 0 := by
    rw [hXpow]
    change (AddMonoidAlgebra.single (v : ZMod q) (1 : R)).coeff (u : ZMod q) = _
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt hu]
  have hk (n u : ℕ) (hu : u < q) : coeff u ((X - 1) ^ n) = K n u := by
    rw [sub_eq_add_neg, add_pow, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : scalar ((-1 : R) ^ (n - j) * (n.choose j : R)) =
        (-1 : B) ^ (n - j) * (n.choose j : B) := by
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    rw [mul_assoc, ← hs, mul_comm (X ^ j), hscalar, hdelta j u hu]
    split <;> simp
  have hsum (u : ℕ) (hu : u < q) : coeff u (∑ j ∈ Finset.range q, X ^ j) = 1 := by
    rw [map_sum, Finset.sum_eq_single u]
    · simp [hdelta u u hu, Nat.mod_eq_of_lt hu]
    · intro j hj hne
      simp [hdelta j u hu, Nat.mod_eq_of_lt (Finset.mem_range.1 hj), hne]
    · exact fun h => (h (Finset.mem_range.2 hu)).elim
  have hnz : (-(p : R)) ^ (a - 1) ≠ 0 := by
    have hnzp : (p : R) ^ (a - 1) ≠ 0 := by
      intro hz
      have hc : ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) = 0 := by simpa only [Nat.cast_pow] using hz
      have h := (ZMod.natCast_eq_zero_iff _ _).1 hc
      have hlt : p ^ (a - 1) < p ^ a := pow_lt_pow_right₀ hp.one_lt (by omega)
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (pow_pos hp.pos _) h)
    by_cases he : Even (a - 1)
    · rwa [he.neg_pow]
    · rwa [(Nat.not_even_iff_odd.1 he).neg_pow, neg_ne_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hs : scalar ((-(p : R)) ^ (a - 1)) = (-(p : B)) ^ (a - 1) := by
      simp only [map_pow, map_neg, map_natCast]
    have h : K L u = (-(p : R)) ^ (a - 1) := by
      rw [← hk L u hu, show (X - 1) ^ L = _ from hboundary, ← hs, hscalar, hsum u hu, mul_one]
    exact ⟨h, h ▸ hnz⟩
  · intro n hn u hu
    rw [← hk n u hu, hvanish n hn, map_zero]
  · intro v u hu
    have hr := congrArg (coeff u) (binomial_recovery X L hvanish v)
    rw [map_sum, hdelta v u hu] at hr
    convert hr using 1
    refine Finset.sum_congr rfl fun n _ => ?_
    have hs : scalar (v.choose n : R) = (v.choose n : B) := map_natCast _ _
    rw [mul_comm ((X - 1) ^ n), ← hs, hscalar, hk n u hu]
