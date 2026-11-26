import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_130 : (∀ a b : ℝ, a ^ 3 + b ^ 3 = 0 ↔ a + b = 0) ∧ (∀ (u v : Polynomial ℝ) (x : ℝ), Polynomial.eval x (u ^ 3 + v ^ 3) = 0 → Polynomial.eval x (u + v) = 0) := by
  have hreal : ∀ a b : ℝ, a ^ 3 + b ^ 3 = 0 ↔ a + b = 0 := by
    intro a b
    constructor
    · intro h
      have hfac : (a + b) * (a ^ 2 - a * b + b ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact h1
      · have hsq : (2 * a - b) ^ 2 + 3 * b ^ 2 = 0 := by linarith
        have hb : b = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
        have ha : a = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
        linarith
    · intro h
      have : a = -b := by linarith
      rw [this]; ring
  refine ⟨hreal, fun u v x hx => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_pow] at hx ⊢
  exact (hreal (Polynomial.eval x u) (Polynomial.eval x v)).mp hx
