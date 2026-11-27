import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_770 : ∀ (k : ℕ) (c a : Fin k → ℝ), Function.Injective a →
  (∀ x : Fin k, (∑ i, c i * (a i) ^ (x : ℕ)) = 0) → ∀ i, c i = 0 := by
  intro k c a ha h
  have hdet : (Matrix.vandermonde a).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr ha
  have hv : Matrix.vecMul c (Matrix.vandermonde a) = 0 := by
    funext x
    have := h x
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] using this
  have hc := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  intro i
  exact congrFun hc i
