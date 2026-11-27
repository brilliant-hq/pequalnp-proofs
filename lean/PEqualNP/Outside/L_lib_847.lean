import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_847

open Polynomial Finset

noncomputable def Yp : ℤ[X] := X + C (-1)

def Mem (P q t : ℕ) (f : ℤ[X]) : Prop :=
  ∃ g h : ℤ[X], f = (C (P : ℤ)) ^ t * g + (X ^ q - 1) * h

theorem mem_zero (P q t : ℕ) : Mem P q t 0 := ⟨0, 0, by ring⟩

theorem mem_add {P q t : ℕ} {f g : ℤ[X]} (hf : Mem P q t f) (hg : Mem P q t g) :
    Mem P q t (f + g) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  exact ⟨a + c, b + d, by ring⟩

theorem mem_sub {P q t : ℕ} {f g : ℤ[X]} (hf : Mem P q t f) (hg : Mem P q t g) :
    Mem P q t (f - g) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  exact ⟨a - c, b - d, by ring⟩

theorem mem_mul {P q t : ℕ} {f : ℤ[X]} (hf : Mem P q t f) (r : ℤ[X]) : Mem P q t (r * f) := by
  obtain ⟨a, b, rfl⟩ := hf
  exact ⟨r * a, r * b, by ring⟩

theorem mem_Cmul {P q t : ℕ} {f : ℤ[X]} (hf : Mem P q t f) (s : ℕ) :
    Mem P q (t + s) ((C (P : ℤ)) ^ s * f) := by
  obtain ⟨a, b, rfl⟩ := hf
  exact ⟨a, (C (P : ℤ)) ^ s * b, by ring⟩

theorem mem_pow (P q t : ℕ) (g : ℤ[X]) : Mem P q t ((C (P : ℤ)) ^ t * g) := ⟨g, 0, by ring⟩

theorem mem_le {P q s t : ℕ} {f : ℤ[X]} (hst : s ≤ t) (hf : Mem P q t f) : Mem P q s f := by
  obtain ⟨a, b, rfl⟩ := hf
  refine ⟨(C (P : ℤ)) ^ (t - s) * a, b, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hst]

/-! binomial facts -/

theorem dvd_ch {p b k : ℕ} (hp : p.Prime) (h0 : 0 < k) (hk : k < p ^ b) : p ∣ (p ^ b).choose k :=
  hp.dvd_choose_pow (by omega) (by omega)

theorem key_mul (q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    q * (q - 1).choose (k - 1) = q.choose k * k := by
  have := Nat.add_one_mul_choose_eq (q - 1) (k - 1)
  rwa [Nat.sub_add_cancel hq, Nat.sub_add_cancel hk] at this

theorem dvd_ch2 {p b k : ℕ} (hp : p.Prime) (hb : 0 < b) (h0 : 0 < k) (hk : k < p ^ (b - 1)) :
    p ^ 2 ∣ (p ^ b).choose k := by
  have hkq : k ≤ p ^ b := by
    have : p ^ (b - 1) ≤ p ^ b := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hm := hp.emultiplicity_choose_prime_pow hkq (by omega)
  have hmk : multiplicity p k < b - 1 := by
    have h1 : p ^ multiplicity p k ≤ k := Nat.le_of_dvd h0 (pow_multiplicity_dvd p k)
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h1 hk)
  apply pow_dvd_iff_le_emultiplicity.mpr
  rw [hm]
  exact_mod_cast (by omega : 2 ≤ b - multiplicity p k)

theorem ch_alt {p b : ℕ} (hp : p.Prime) :
    ∀ j, j < p ^ b → (p : ℤ) ∣ (((p ^ b - 1).choose j : ℕ) : ℤ) - (-1) ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hq : 0 < p ^ b := pow_pos hp.pos b
    have h1 := ih (by omega)
    have h2 : (p : ℤ) ∣ (((p ^ b).choose (j + 1) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_ch hp (by omega) hj)
    have h3 : (p ^ b).choose (j + 1) = (p ^ b - 1).choose j + (p ^ b - 1).choose (j + 1) := by
      conv_lhs => rw [show p ^ b = p ^ b - 1 + 1 by omega]
      exact Nat.choose_succ_succ _ _
    rw [h3] at h2
    push_cast at h2
    have : (((p ^ b - 1).choose (j + 1) : ℕ) : ℤ) - (-1) ^ (j + 1) =
        ((((p ^ b - 1).choose j : ℕ) : ℤ) + (((p ^ b - 1).choose (j + 1) : ℕ) : ℤ)) -
          ((((p ^ b - 1).choose j : ℕ) : ℤ) - (-1) ^ j) := by ring
    rw [this]
    exact dvd_sub h2 h1

theorem sign_lem {p : ℕ} (hp : p.Prime) (c : ℕ) : (p : ℤ) ∣ (-1) ^ (p ^ c - 1) - 1 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rcases Nat.even_or_odd (2 ^ c - 1) with he | ho
    · rw [he.neg_one_pow]; simp
    · rw [ho.neg_one_pow]; exact ⟨-1, by norm_num⟩
  · have : Even (p ^ c - 1) := Nat.Odd.sub_odd (hodd.pow) odd_one
    rw [this.neg_one_pow]; simp


theorem cm_eq {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    (p ^ b).choose (p ^ (b - 1)) = p * (p ^ b - 1).choose (p ^ (b - 1) - 1) := by
  have hm : 0 < p ^ (b - 1) := pow_pos hp.pos _
  have hq : p ^ b = p * p ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h := key_mul (p ^ b) (p ^ (b - 1)) (pow_pos hp.pos b) hm
  rw [hq] at h
  have h2 : p ^ (b - 1) * (p * (p * p ^ (b - 1) - 1).choose (p ^ (b - 1) - 1)) =
      p ^ (b - 1) * (p * p ^ (b - 1)).choose (p ^ (b - 1)) := by
    rw [mul_comm (p ^ (b - 1)) ((p * p ^ (b - 1)).choose _), ← h]; ring
  rw [hq]
  exact (Nat.eq_of_mul_eq_mul_left hm h2).symm

theorem cm_mod {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    (p : ℤ) ∣ ((((p ^ b).choose (p ^ (b - 1)) / p : ℕ) : ℤ)) - 1 := by
  rw [cm_eq hp hb, Nat.mul_div_cancel_left _ hp.pos]
  have hm : 0 < p ^ (b - 1) := pow_pos hp.pos _
  have hlt : p ^ (b - 1) - 1 < p ^ b := by
    have : p ^ (b - 1) ≤ p ^ b := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have h1 := ch_alt hp (p ^ (b - 1) - 1) hlt
  have h2 := sign_lem hp (b - 1)
  have : ((((p ^ b - 1).choose (p ^ (b - 1) - 1)) : ℕ) : ℤ) - 1 =
      (((((p ^ b - 1).choose (p ^ (b - 1) - 1)) : ℕ) : ℤ) - (-1) ^ (p ^ (b - 1) - 1)) +
        ((-1) ^ (p ^ (b - 1) - 1) - 1) := by ring
  rw [this]
  exact dvd_add h1 h2

/-! the identity for Yp^q -/

theorem X_eq : (X : ℤ[X]) = Yp + 1 := by
  simp [Yp]

theorem natcast_poly (n : ℕ) : ((n : ℕ) : ℤ[X]) = C ((n : ℕ) : ℤ) := by simp

theorem E_id {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    Yp ^ (p ^ b) = (X ^ (p ^ b) - 1) - C (p : ℤ) * (Yp ^ (p ^ (b - 1)) *
      (C ((((p ^ b).choose (p ^ (b - 1)) / p : ℕ) : ℤ)) +
        Yp * ∑ k ∈ Ico (p ^ (b - 1) + 1) (p ^ b),
          C ((((p ^ b).choose k / p : ℕ) : ℤ)) * Yp ^ (k - p ^ (b - 1) - 1)) +
      C (p : ℤ) * (Yp * ∑ k ∈ Ico 1 (p ^ (b - 1)),
          C ((((p ^ b).choose k / p ^ 2 : ℕ) : ℤ)) * Yp ^ (k - 1))) := by
  set q := p ^ b with hqdef
  set m := p ^ (b - 1) with hmdef
  have hm : 0 < m := pow_pos hp.pos _
  have hmq : m < q := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hsum : (X : ℤ[X]) ^ q = ∑ k ∈ range (q + 1), Yp ^ k * ((q.choose k : ℕ) : ℤ[X]) := by
    rw [X_eq, add_pow]; simp
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    ← Finset.sum_Ico_consecutive _ (show 1 ≤ m by omega) (show m ≤ q by omega),
    Finset.sum_eq_sum_Ico_succ_bot hmq] at hsum
  have hA : ∑ k ∈ Ico 1 m, Yp ^ k * ((q.choose k : ℕ) : ℤ[X]) =
      C (p : ℤ) * (C (p : ℤ) * (Yp * ∑ k ∈ Ico 1 m, C (((q.choose k / p ^ 2 : ℕ) : ℤ)) *
        Yp ^ (k - 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    have hd := dvd_ch2 hp hb (by omega) (by omega : k < p ^ (b - 1))
    obtain ⟨c, hc⟩ := hd
    rw [natcast_poly, show q.choose k = p ^ 2 * c from hc,
      Nat.mul_div_cancel_left c (pow_pos hp.pos 2)]
    have hk1 : Yp ^ k = Yp * Yp ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hk1]; push_cast; simp only [map_mul, map_pow]; ring
  have hB : ∑ k ∈ Ico (m + 1) q, Yp ^ k * ((q.choose k : ℕ) : ℤ[X]) =
      C (p : ℤ) * (Yp ^ m * (Yp * ∑ k ∈ Ico (m + 1) q, C (((q.choose k / p : ℕ) : ℤ)) *
        Yp ^ (k - m - 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    have hd := dvd_ch hp (by omega : 0 < k) (by omega : k < p ^ b)
    obtain ⟨c, hc⟩ := hd
    rw [natcast_poly, show q.choose k = p * c from hc, Nat.mul_div_cancel_left c hp.pos]
    have hk1 : Yp ^ k = Yp ^ m * (Yp * Yp ^ (k - m - 1)) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [hk1]; push_cast; simp only [map_mul]; ring
  have hM : Yp ^ m * ((q.choose m : ℕ) : ℤ[X]) =
      C (p : ℤ) * (Yp ^ m * C (((q.choose m / p : ℕ) : ℤ))) := by
    have hd := dvd_ch hp hm hmq
    obtain ⟨c, hc⟩ := hd
    rw [natcast_poly, show q.choose m = p * c from hc, Nat.mul_div_cancel_left c hp.pos]
    push_cast; simp only [map_mul]; ring
  rw [hA, hM, hB] at hsum
  simp only [pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one] at hsum
  rw [hsum]; ring

/-! valuation bound -/

theorem P_bound {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    ∀ t n, p ^ (b - 1) + t * (p ^ b - p ^ (b - 1)) ≤ n → Mem p (p ^ b) t (Yp ^ n) := by
  set q := p ^ b with hqdef
  set m := p ^ (b - 1) with hmdef
  have hm : 0 < m := pow_pos hp.pos _
  have hqm : q = p * m := by rw [hqdef, hmdef, ← pow_succ']; congr 1; omega
  have h2m : 2 * m ≤ q := by rw [hqm]; exact Nat.mul_le_mul_right _ hp.two_le
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro n hn
    rcases t with _ | s
    · exact ⟨Yp ^ n, 0, by simp⟩
    · set φ := q - m with hφ
      have hsφ : (s + 1) * φ = s * φ + φ := by ring
      rw [hsφ] at hn
      have hnq : q ≤ n := by omega
      have hpow : Yp ^ n = Yp ^ q * Yp ^ (n - q) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, E_id hp hb]
      set U := (C ((((p ^ b).choose (p ^ (b - 1)) / p : ℕ) : ℤ)) +
        Yp * ∑ k ∈ Ico (p ^ (b - 1) + 1) (p ^ b),
          C ((((p ^ b).choose k / p : ℕ) : ℤ)) * Yp ^ (k - p ^ (b - 1) - 1))
      set W := ∑ k ∈ Ico 1 (p ^ (b - 1)), C ((((p ^ b).choose k / p ^ 2 : ℕ) : ℤ)) * Yp ^ (k - 1)
      have h2 : Mem p q (s + 1) ((C (p : ℤ)) ^ 1 * (U * Yp ^ (m + (n - q)))) :=
        mem_Cmul (mem_mul (ih s (by omega) _ (by omega)) U) 1
      have h3 : Mem p q (s + 1) ((C (p : ℤ)) ^ 2 * (W * Yp ^ (n - q + 1))) := by
        rcases s with _ | r
        · exact mem_le (by omega) (mem_pow p q 2 _)
        · have hr : m + r * φ ≤ n - q + 1 := by
            have : (r + 1) * φ = r * φ + φ := by ring
            omega
          exact mem_le (by omega) (mem_Cmul (mem_mul (ih r (by omega) _ hr) W) 2)
      have h1 : Mem p q (s + 1) ((X ^ q - 1) * Yp ^ (n - q)) := ⟨0, Yp ^ (n - q), by ring⟩
      have heq : ((X : ℤ[X]) ^ q - 1 - C (p : ℤ) * (Yp ^ m * U + C (p : ℤ) * (Yp * W))) *
          Yp ^ (n - q) = (X ^ q - 1) * Yp ^ (n - q) - (C (p : ℤ)) ^ 1 * (U * Yp ^ (m + (n - q)))
          - (C (p : ℤ)) ^ 2 * (W * Yp ^ (n - q + 1)) := by
        rw [pow_add, pow_succ]; ring
      rw [heq]
      exact mem_sub (mem_sub h1 h2) h3


theorem Q_exact {p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    ∀ t, Mem p (p ^ b) (t + 1) (Yp ^ (p ^ b - 1 + t * (p ^ b - p ^ (b - 1))) -
      (-C (p : ℤ)) ^ t * Yp ^ (p ^ b - 1)) := by
  set q := p ^ b with hqdef
  set m := p ^ (b - 1) with hmdef
  have hm : 0 < m := pow_pos hp.pos _
  have hqm : q = p * m := by rw [hqdef, hmdef, ← pow_succ']; congr 1; omega
  have h2m : 2 * m ≤ q := by rw [hqm]; exact Nat.mul_le_mul_right _ hp.two_le
  set φ := q - m with hφ
  intro t
  induction t with
  | zero =>
    have : Yp ^ (q - 1 + 0 * φ) - (-C (p : ℤ)) ^ 0 * Yp ^ (q - 1) = 0 := by simp
    rw [this]; exact mem_zero _ _ _
  | succ t ih =>
    set N := t * φ with hN
    have hsφ : (t + 1) * φ = N + φ := by rw [hN]; ring
    have h1 : Yp ^ (q - 1 + (t + 1) * φ) = Yp ^ q * Yp ^ (N + φ - 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : Yp ^ (q - 1 + N) = Yp ^ m * Yp ^ (N + φ - 1) := by
      rw [← pow_add]; congr 1; omega
    have h3 : Yp ^ (q + N) = Yp ^ m * Yp * Yp ^ (N + φ - 1) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    have h4 : Yp ^ (N + φ) = Yp * Yp ^ (N + φ - 1) := by
      rw [← pow_succ']; congr 1; omega
    obtain ⟨e, he⟩ := cm_mod hp hb
    have hce : C ((((p ^ b).choose (p ^ (b - 1)) / p : ℕ) : ℤ)) = 1 + C (p : ℤ) * C e := by
      have : ((((p ^ b).choose (p ^ (b - 1)) / p : ℕ) : ℤ)) = 1 + p * e := by linarith
      rw [this, map_add, map_mul, map_one]
    rw [h1, E_id hp hb, hce]
    set U1 := ∑ k ∈ Ico (p ^ (b - 1) + 1) (p ^ b),
          C ((((p ^ b).choose k / p : ℕ) : ℤ)) * Yp ^ (k - p ^ (b - 1) - 1)
    set W := ∑ k ∈ Ico 1 (p ^ (b - 1)), C ((((p ^ b).choose k / p ^ 2 : ℕ) : ℤ)) * Yp ^ (k - 1)
    have m1 : Mem p q (t + 1 + 1) ((C (p : ℤ)) ^ 1 *
        (Yp ^ (q - 1 + N) - (-C (p : ℤ)) ^ t * Yp ^ (q - 1))) := mem_Cmul ih 1
    have m2 : Mem p q (t + 1 + 1) ((C (p : ℤ)) ^ 2 * (C e * Yp ^ (q - 1 + N))) :=
      mem_Cmul (mem_mul (P_bound hp hb t (q - 1 + N) (by show m + t * φ ≤ _; omega)) (C e)) 2
    have m3 : Mem p q (t + 1 + 1) ((C (p : ℤ)) ^ 1 * (U1 * Yp ^ (q + N))) :=
      mem_Cmul (mem_mul (P_bound hp hb (t + 1) (q + N) (by show m + (t + 1) * φ ≤ _; omega)) U1) 1
    have m4 : Mem p q (t + 1 + 1) ((C (p : ℤ)) ^ 2 * (W * Yp ^ (N + φ))) :=
      mem_Cmul (mem_mul (P_bound hp hb t (N + φ) (by show m + t * φ ≤ _; omega)) W) 2
    have m0 : Mem p q (t + 1 + 1) ((X ^ q - 1) * Yp ^ (N + φ - 1)) := ⟨0, Yp ^ (N + φ - 1), by ring⟩
    have heq : ((X : ℤ[X]) ^ q - 1 - C (p : ℤ) * (Yp ^ m * (1 + C (p : ℤ) * C e + Yp * U1) +
        C (p : ℤ) * (Yp * W))) * Yp ^ (N + φ - 1) - (-C (p : ℤ)) ^ (t + 1) * Yp ^ (q - 1) =
        (X ^ q - 1) * Yp ^ (N + φ - 1) -
        (C (p : ℤ)) ^ 1 * (Yp ^ (q - 1 + N) - (-C (p : ℤ)) ^ t * Yp ^ (q - 1)) -
        (C (p : ℤ)) ^ 2 * (C e * Yp ^ (q - 1 + N)) -
        (C (p : ℤ)) ^ 1 * (U1 * Yp ^ (q + N)) - (C (p : ℤ)) ^ 2 * (W * Yp ^ (N + φ)) := by
      rw [h2, h3, h4]; ring
    rw [heq]
    exact mem_sub (mem_sub (mem_sub (mem_sub m0 m1) m2) m3) m4

/-! the residue sum map -/

noncomputable def rho (q u : ℕ) (f : ℤ[X]) : ℤ := f.sum (fun j c => if j % q = u then c else 0)

theorem rho_add (q u : ℕ) (f g : ℤ[X]) : rho q u (f + g) = rho q u f + rho q u g :=
  Polynomial.sum_add_index f g _ (fun i => by simp) (fun i a b => by split_ifs <;> simp)

theorem rho_zero (q u : ℕ) : rho q u 0 = 0 := Polynomial.sum_zero_index _

theorem rho_Cmul (q u : ℕ) (c : ℤ) (f : ℤ[X]) : rho q u (C c * f) = c * rho q u f := by
  rw [← smul_eq_C_mul, rho, rho, Polynomial.sum_smul_index _ _ _ (fun i => by simp)]
  unfold Polynomial.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  split_ifs <;> simp

theorem rho_monomial (q u n : ℕ) (c : ℤ) : rho q u (monomial n c) = if n % q = u then c else 0 :=
  Polynomial.sum_monomial_index _ _ (by simp)

theorem rho_Xq_mul (q u : ℕ) (h : ℤ[X]) : rho q u (X ^ q * h) = rho q u h := by
  induction h using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, rho_add, rho_add, hf, hg]
  | monomial n c => rw [X_pow_mul_monomial, rho_monomial, rho_monomial, Nat.add_mod_right]

theorem rho_sub (q u : ℕ) (f g : ℤ[X]) : rho q u (f - g) = rho q u f - rho q u g := by
  have := rho_add q u (f - g) g
  rw [sub_add_cancel] at this
  linarith

theorem rho_sum (q u : ℕ) (s : Finset ℕ) (f : ℕ → ℤ[X]) :
    rho q u (∑ n ∈ s, f n) = ∑ n ∈ s, rho q u (f n) := by
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]

theorem rho_mem {p q a : ℕ} (u : ℕ) {f : ℤ[X]} (h : Mem p q a f) :
    ((rho q u f : ℤ) : ZMod (p ^ a)) = 0 := by
  obtain ⟨g, h, rfl⟩ := h
  rw [rho_add, ← map_pow, rho_Cmul, sub_mul, one_mul, rho_sub, rho_Xq_mul, sub_self, add_zero]
  push_cast
  rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem rho_Yp (q u n : ℕ) : rho q u (Yp ^ n) =
    ∑ j ∈ range (n + 1), if j % q = u then (-1) ^ (n - j) * ((n.choose j : ℕ) : ℤ) else 0 := by
  rw [rho, Polynomial.sum_over_range' _ (fun _ => by simp) (n + 1)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Yp, coeff_X_add_C_pow]
  · calc natDegree (Yp ^ n) ≤ n * natDegree Yp := natDegree_pow_le
      _ = n := by rw [Yp, natDegree_X_add_C, mul_one]
      _ < n + 1 := by omega

theorem rho_Xpow (q u v : ℕ) : rho q u (X ^ v) = if v % q = u then 1 else 0 := by
  rw [X_pow_eq_monomial, rho_monomial]


def Kf (p b a n u : ℕ) : ZMod (p ^ a) :=
  ∑ j ∈ Finset.range (n + 1),
    if j % p ^ b = u then (-1 : ZMod (p ^ a)) ^ (n - j) * (Nat.choose n j : ZMod (p ^ a)) else 0

theorem Kf_eq (p b a n u : ℕ) : Kf p b a n u = ((rho (p ^ b) u (Yp ^ n) : ℤ) : ZMod (p ^ a)) := by
  rw [Kf, rho_Yp]
  simp only [Int.cast_sum, apply_ite ((↑) : ℤ → ZMod (p ^ a)), Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_zero]

theorem rho_top {p b : ℕ} (hp : p.Prime) (u : ℕ) (hu : u < p ^ b) :
    (p : ℤ) ∣ rho (p ^ b) u (Yp ^ (p ^ b - 1)) - 1 := by
  have hq : 0 < p ^ b := pow_pos hp.pos b
  rw [rho_Yp, Nat.sub_add_cancel hq]
  have : ∀ j ∈ range (p ^ b), (if j % p ^ b = u then (-1 : ℤ) ^ (p ^ b - 1 - j) *
      (((p ^ b - 1).choose j : ℕ) : ℤ) else 0) =
      if j = u then (-1 : ℤ) ^ (p ^ b - 1 - j) * (((p ^ b - 1).choose j : ℕ) : ℤ) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.mod_eq_of_lt hj]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq', ite_cond_eq_true _ _ (eq_true (Finset.mem_range.mpr hu))]
  have h1 := ch_alt hp u hu
  have h2 := sign_lem hp b
  have h3 : (-1 : ℤ) ^ (p ^ b - 1 - u) * (-1) ^ u = (-1) ^ (p ^ b - 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have : (-1 : ℤ) ^ (p ^ b - 1 - u) * (((p ^ b - 1).choose u : ℕ) : ℤ) - 1 =
      (-1) ^ (p ^ b - 1 - u) * ((((p ^ b - 1).choose u : ℕ) : ℤ) - (-1) ^ u) +
        ((-1) ^ (p ^ b - 1) - 1) := by
    rw [← h3]; ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right h1 _) h2

theorem main_aux (p b a : ℕ) (hp : p.Prime) (hb : 0 < b) (ha : 0 < a) :
    (∀ u < p ^ b, Kf p b a (p ^ b - 1 + (a - 1) * (p ^ b - p ^ b / p)) u =
        (-(p : ZMod (p ^ a))) ^ (a - 1) ∧
      Kf p b a (p ^ b - 1 + (a - 1) * (p ^ b - p ^ b / p)) u ≠ 0) ∧
    (∀ n > p ^ b - 1 + (a - 1) * (p ^ b - p ^ b / p), ∀ u < p ^ b, Kf p b a n u = 0) ∧
    ∀ v : ℕ, ∀ u < p ^ b,
      (∑ n ∈ Finset.range (p ^ b - 1 + (a - 1) * (p ^ b - p ^ b / p) + 1),
        (Nat.choose v n : ZMod (p ^ a)) * Kf p b a n u) = (if v % p ^ b = u then 1 else 0) := by
  have hdiv : p ^ b / p = p ^ (b - 1) := by
    have := Nat.pow_div (show 1 ≤ b from hb) hp.pos
    rwa [pow_one] at this
  rw [hdiv]
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hm : 0 < p ^ (b - 1) := pow_pos hp.pos _
  have hmq : p ^ (b - 1) < p ^ b := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hvan : ∀ n, p ^ b - 1 + a' * (p ^ b - p ^ (b - 1)) < n → ∀ u, Kf p b (a' + 1) n u = 0 := by
    intro n hn u
    rw [Kf_eq]
    apply rho_mem
    apply P_bound hp hb
    have : (a' + 1) * (p ^ b - p ^ (b - 1)) = a' * (p ^ b - p ^ (b - 1)) + (p ^ b - p ^ (b - 1)) := by
      ring
    omega
  have hz : (p : ZMod (p ^ (a' + 1))) ^ (a' + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hval : ∀ u < p ^ b, Kf p b (a' + 1) (p ^ b - 1 + a' * (p ^ b - p ^ (b - 1))) u =
      (-(p : ZMod (p ^ (a' + 1)))) ^ a' := by
    intro u hu
    have h0 := rho_mem u (Q_exact hp hb a')
    have hC : (-C (p : ℤ)) ^ a' = C ((-(p : ℤ)) ^ a') := by rw [map_pow, map_neg]
    rw [rho_sub, hC, rho_Cmul, Int.cast_sub, sub_eq_zero] at h0
    rw [Kf_eq, h0]
    obtain ⟨w, hw⟩ := rho_top hp u hu
    have hr : rho (p ^ b) u (Yp ^ (p ^ b - 1)) = 1 + p * w := by linarith
    rw [hr]
    push_cast
    linear_combination ((-1) ^ a' * (w : ZMod (p ^ (a' + 1)))) * hz
  refine ⟨fun u hu => ⟨hval u hu, ?_⟩, fun n hn u _ => hvan n hn u, ?_⟩
  · rw [hval u hu]
    intro h
    have h2 : (p : ZMod (p ^ (a' + 1))) ^ a' = 0 := by
      have : (p : ZMod (p ^ (a' + 1))) ^ a' =
          (-1) ^ a' * (-(p : ZMod (p ^ (a' + 1)))) ^ a' := by
        rw [← mul_pow]; ring
      rw [this, h, mul_zero]
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (pow_pos hp.pos _) h2
    have := Nat.pow_lt_pow_right hp.one_lt (show a' < a' + 1 by omega)
    omega
  · intro v u hu
    have hX : (X : ℤ[X]) ^ v = ∑ n ∈ range (v + 1), C (((v.choose n : ℕ) : ℤ)) * Yp ^ n := by
      rw [X_eq, add_pow]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [one_pow, mul_one, natcast_poly, mul_comm]
    have hrho := congrArg (rho (p ^ b) u) hX
    rw [rho_Xpow, rho_sum] at hrho
    simp only [rho_Cmul] at hrho
    have hcast := congrArg (Int.cast : ℤ → ZMod (p ^ (a' + 1))) hrho
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, apply_ite ((↑) : ℤ → ZMod (p ^ (a' + 1))),
      Int.cast_one, Int.cast_zero, ← Kf_eq] at hcast
    rw [hcast]
    set L := p ^ b - 1 + a' * (p ^ b - p ^ (b - 1))
    have e1 : ∀ n ∈ range (L + v + 1), n ∉ range (L + 1) →
        (Nat.choose v n : ZMod (p ^ (a' + 1))) * Kf p b (a' + 1) n u = 0 := by
      intro n _ hn
      rw [Finset.mem_range] at hn
      rw [hvan n (by omega) u, mul_zero]
    have e2 : ∀ n ∈ range (L + v + 1), n ∉ range (v + 1) →
        (Nat.choose v n : ZMod (p ^ (a' + 1))) * Kf p b (a' + 1) n u = 0 := by
      intro n _ hn
      rw [Finset.mem_range] at hn
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    rw [Finset.sum_subset (Finset.range_mono (show L + 1 ≤ L + v + 1 by omega)) e1,
      Finset.sum_subset (Finset.range_mono (show v + 1 ≤ L + v + 1 by omega)) e2]

end PEqualNP.Outside.L_lib_847

open PEqualNP.Outside.L_lib_847 in
theorem PEqualNP.Outside.L_lib_847 : ∀ (p b a : ℕ), Nat.Prime p → 0 < b → 0 < a →
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
      (if v % q = u then 1 else 0) := by
  intro p b a hp hb ha
  exact main_aux p b a hp hb ha
