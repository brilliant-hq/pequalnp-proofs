import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_132 : (∏ j ∈ Finset.range 6, (Polynomial.X - Polynomial.C ((j : ℤ) + 1))) ∣ ((360 - 342 * Polynomial.X + 42 * Polynomial.X ^ 3 : Polynomial ℤ) ^ 2 - (119 * Polynomial.X ^ 2 - 60 * Polynomial.X ^ 3 + Polynomial.X ^ 4) ^ 2) ∧ ((360 - 342 * Polynomial.X + 42 * Polynomial.X ^ 3 : Polynomial ℤ) ^ 2 - (119 * Polynomial.X ^ 2 - 60 * Polynomial.X ^ 3 + Polynomial.X ^ 4) ^ 2) ≠ 0 := by
  constructor
  · refine ⟨(180 + 99 * Polynomial.X - Polynomial.X ^ 2 : Polynomial ℤ), ?_⟩
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, map_add, map_zero, map_one, map_ofNat]
    ring
  · intro h
    have hev := congrArg (Polynomial.eval (0 : ℤ)) h
    simp at hev
