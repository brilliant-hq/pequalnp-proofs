import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_765 : ∀ (n k : ℕ), (∑ i ∈ Finset.range (k + 1), Nat.choose n i) ≤ (n + 1) ^ k := by
  intro n k
  calc (∑ i ∈ Finset.range (k + 1), Nat.choose n i)
      ≤ ∑ i ∈ Finset.range (k + 1), n ^ i * Nat.choose k i := by
        apply Finset.sum_le_sum
        intro i hi
        have h1 : Nat.choose n i ≤ n ^ i := Nat.choose_le_pow n i
        have h2 : 1 ≤ Nat.choose k i := Nat.choose_pos (by simp at hi; omega)
        nlinarith
    _ = (n + 1) ^ k := by
        rw [add_pow]
        simp
