import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_gct_127 : ∀ a b : ℕ, (Nat.digits 2 (a + b)).sum ≤ (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  intro a b
  have key : ∀ n : ℕ, (Nat.digits 2 n).sum = n - multiplicity 2 n.factorial ∧ multiplicity 2 n.factorial ≤ n := by
    intro n
    have := Nat.Prime.sub_one_mul_multiplicity_factorial (p := 2) (n := n) Nat.prime_two
    have h2 : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
    constructor <;> omega
  have hdvd : a.factorial * b.factorial ∣ (a + b).factorial := Nat.factorial_mul_factorial_dvd_factorial_add a b
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul : multiplicity 2 (a.factorial * b.factorial) = multiplicity 2 a.factorial + multiplicity 2 b.factorial :=
    padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)
  have hle : multiplicity 2 a.factorial + multiplicity 2 b.factorial ≤ multiplicity 2 (a + b).factorial := by
    rw [← hmul]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 (dvd_trans (pow_multiplicity_dvd 2 _) hdvd)
  have ha := key a
  have hb := key b
  have hab := key (a + b)
  omega
