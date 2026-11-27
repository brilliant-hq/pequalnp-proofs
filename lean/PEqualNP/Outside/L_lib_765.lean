import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

theorem PEqualNP.Outside.L_lib_765 : ∀ (n k : ℕ), (∑ i ∈ Finset.range (k + 1), Nat.choose n i) ≤ (n + 1) ^ k := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h := Nat.choose_le_pow n (k+1)
    have hp : n^k ≤ (n+1)^k := Nat.pow_le_pow_left (by omega) k
    calc
      _ ≤ (n+1)^k + n^(k+1) := Nat.add_le_add ih h
      _ ≤ (n+1)^k + (n+1)^k*n := by rw [pow_succ n]; exact Nat.add_le_add_left (Nat.mul_le_mul_right n hp) _
      _ = _ := by ring
