import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_gct_130 : (∀ a b : ℝ, a ^ 3 + b ^ 3 = 0 ↔ a + b = 0) ∧ (∀ (u v : Polynomial ℝ) (x : ℝ), Polynomial.eval x (u ^ 3 + v ^ 3) = 0 → Polynomial.eval x (u + v) = 0) := by
  refine ⟨?_, ?_⟩
  · intro a b
    constructor
    · intro h
      have h2 : (a + b) * (a ^ 2 - a * b + b ^ 2) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · have ha : a = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
        have hb : b = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
        rw [ha, hb]; ring
    · intro h
      have hb : b = -a := by linarith
      rw [hb]; ring
  · intro u v x h
    simp only [Polynomial.eval_add, Polynomial.eval_pow] at h ⊢
    have h2 : (Polynomial.eval x u + Polynomial.eval x v) * ((Polynomial.eval x u) ^ 2 - Polynomial.eval x u * Polynomial.eval x v + (Polynomial.eval x v) ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · have ha : Polynomial.eval x u = 0 := by nlinarith [sq_nonneg (Polynomial.eval x u - Polynomial.eval x v), sq_nonneg (Polynomial.eval x u + Polynomial.eval x v), sq_nonneg (Polynomial.eval x u), sq_nonneg (Polynomial.eval x v)]
      have hb : Polynomial.eval x v = 0 := by nlinarith [sq_nonneg (Polynomial.eval x u - Polynomial.eval x v), sq_nonneg (Polynomial.eval x u + Polynomial.eval x v), sq_nonneg (Polynomial.eval x u), sq_nonneg (Polynomial.eval x v)]
      rw [ha, hb]; ring
