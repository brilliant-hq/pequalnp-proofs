import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_130_aux

theorem cubes (a b : ℝ) : a ^ 3 + b ^ 3 = 0 ↔ a + b = 0 := by
  constructor
  · intro h
    have h1 : (a + b) * (a ^ 2 - a * b + b ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · have ha : a = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
      have hb : b = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
      rw [ha, hb]; ring
  · intro h
    have hb : b = -a := by linarith
    rw [hb]; ring

end PEqualNP.Outside.L_gct_130_aux

theorem PEqualNP.Outside.L_gct_130 : (∀ a b : ℝ, a ^ 3 + b ^ 3 = 0 ↔ a + b = 0) ∧ (∀ (u v : Polynomial ℝ) (x : ℝ), Polynomial.eval x (u ^ 3 + v ^ 3) = 0 → Polynomial.eval x (u + v) = 0) := by
  refine ⟨PEqualNP.Outside.L_gct_130_aux.cubes, ?_⟩
  intro u v x h
  simp only [Polynomial.eval_add, Polynomial.eval_pow] at h ⊢
  exact (PEqualNP.Outside.L_gct_130_aux.cubes _ _).mp h
