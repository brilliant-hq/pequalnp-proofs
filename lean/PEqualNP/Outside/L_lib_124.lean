import Mathlib

/-!
# L-lib-124: for `p' < q` and every `k`, some power `i` has `2 * k * p' ^ i <= q ^ i`

Task T5d of the evasion chain C5. The proof takes `i = 2 * k * p'` when `p' > 0`
(Bernoulli's inequality gives `(p' + 1) ^ i >= (1 + 2 * k) * p' ^ i`), and `i = 1`
when `p' = 0`.
-/

theorem PEqualNP.Outside.L_lib_124 :
    ∀ p' q : ℕ, p' < q → ∀ k : ℕ, ∃ i : ℕ, 2 * k * p' ^ i ≤ q ^ i := by
  intro p' q hpq k
  rcases Nat.eq_zero_or_pos p' with hp | hp
  · subst hp
    exact ⟨1, by simp⟩
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact ⟨0, by simp⟩
    · refine ⟨2 * k * p', ?_⟩
      have hq : p' + 1 ≤ q := by omega
      have hpR : (0 : ℝ) < (p' : ℝ) := by exact_mod_cast hp
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hn : (2 * k * p' : ℕ) = 2 * k * p' := rfl
      -- Bernoulli's inequality at `a = 1 / p'` and `n = 2 * k * p'`.
      have hbern := one_add_mul_le_pow (a := (1 : ℝ) / (p' : ℝ)) (by positivity)
        (2 * k * p')
      have hcoef : (1 : ℝ) + ((2 * k * p' : ℕ) : ℝ) * (1 / (p' : ℝ)) = 1 + 2 * (k : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul]
        field_simp
        ring
      rw [hcoef] at hbern
      have hratio : (1 : ℝ) + 1 / (p' : ℝ) = ((p' : ℝ) + 1) / (p' : ℝ) := by
        field_simp
      have hpowdiv :
          (1 + 1 / (p' : ℝ)) ^ (2 * k * p') =
            ((p' : ℝ) + 1) ^ (2 * k * p') / (p' : ℝ) ^ (2 * k * p') := by
        rw [hratio, div_pow]
      rw [hpowdiv] at hbern
      have hden : (0 : ℝ) < (p' : ℝ) ^ (2 * k * p') := pow_pos hpR _
      have hmul : (1 + 2 * (k : ℝ)) * (p' : ℝ) ^ (2 * k * p') ≤
          ((p' : ℝ) + 1) ^ (2 * k * p') := by
        have := (le_div_iff₀ hden).mp hbern
        linarith
      have hstep : (2 * (k : ℝ)) * (p' : ℝ) ^ (2 * k * p') ≤
          ((p' : ℝ) + 1) ^ (2 * k * p') := by
        nlinarith [hmul, hden, hkR]
      have hqR : ((p' : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hq
      have hqpow : ((p' : ℝ) + 1) ^ (2 * k * p') ≤ (q : ℝ) ^ (2 * k * p') :=
        pow_le_pow_left₀ (by positivity) hqR _
      have hreal : (2 * (k : ℝ)) * (p' : ℝ) ^ (2 * k * p') ≤ (q : ℝ) ^ (2 * k * p') :=
        le_trans hstep hqpow
      have hcast : ((2 * k * p' ^ (2 * k * p') : ℕ) : ℝ) ≤ ((q ^ (2 * k * p') : ℕ) : ℝ) := by
        push_cast
        simpa [mul_assoc] using hreal
      exact_mod_cast hcast
