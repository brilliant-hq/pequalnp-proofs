import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_776

theorem term (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) : x - y ≤ x * Real.log (x / y) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hy h)
    have h2 : Real.log (x / y) = - Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : x * (y / x - 1) = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

end PEqualNP.Outside.L_lib_776

open PEqualNP.Outside.L_lib_776 in
theorem PEqualNP.Outside.L_lib_776 : ∀ (k : ℕ) (p q : Fin k → ℝ), (∀ i, 0 ≤ p i) → (∀ i, 0 < q i) →
  (∑ i, p i) = 1 → (∑ i, q i) ≤ 1 →
  0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  intro k p q hp hq h1 h2
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => term (p i) (q i) (hp i) (hq i))
  rw [Finset.sum_sub_distrib, h1] at h
  linarith
