import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_127_aux

theorem key (n : ℕ) : multiplicity 2 n.factorial = n - (Nat.digits 2 n).sum := by
  have h := Nat.Prime.sub_one_mul_multiplicity_factorial (n := n) Nat.prime_two
  simpa using h

end PEqualNP.Outside.L_gct_127_aux

theorem PEqualNP.Outside.L_gct_127 : ∀ a b : ℕ, (Nat.digits 2 (a + b)).sum ≤ (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  intro a b
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := Nat.add_choose_mul_factorial_mul_factorial a b
  have hm : multiplicity 2 (a + b).factorial = multiplicity 2 ((a + b).choose b) + multiplicity 2 a.factorial + multiplicity 2 b.factorial := by
    rw [← e, Nat.multiplicity_mul (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_left b a)).ne' (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero b), Nat.multiplicity_mul (Nat.choose_pos (Nat.le_add_left b a)).ne' (Nat.factorial_ne_zero a)]
  rw [PEqualNP.Outside.L_gct_127_aux.key, PEqualNP.Outside.L_gct_127_aux.key, PEqualNP.Outside.L_gct_127_aux.key] at hm
  have ha := Nat.digit_sum_le 2 a
  have hb := Nat.digit_sum_le 2 b
  have hab := Nat.digit_sum_le 2 (a + b)
  omega
