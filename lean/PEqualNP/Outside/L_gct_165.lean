import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.Funext

theorem PEqualNP.Outside.L_gct_165 : ∀ (d q : ℕ) (l : Fin d → Fin 3 × Fin q → ℂ), (∀ (ε : ℂ) (u : Fin d → ℂ), ∑ j, (ε + ∑ k, u k * l k (0, j)) * (ε + ∑ k, u k * l k (1, j)) * (ε + ∑ k, u k * l k (2, j)) = (q : ℂ) * ε ^ 3) → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (ε : S) (u : Fin d → S), ∑ j, (ε + ∑ k, algebraMap ℂ S (l k (0, j)) * u k) * (ε + ∑ k, algebraMap ℂ S (l k (1, j)) * u k) * (ε + ∑ k, algebraMap ℂ S (l k (2, j)) * u k) = (q : S) * ε ^ 3 := by
  intro d q l h S _ _ ε u
  let P : MvPolynomial (Option (Fin d)) ℂ :=
    (∑ j : Fin q,
      (MvPolynomial.X none + ∑ k : Fin d, MvPolynomial.C (l k (0, j)) * MvPolynomial.X (some k)) *
      (MvPolynomial.X none + ∑ k : Fin d, MvPolynomial.C (l k (1, j)) * MvPolynomial.X (some k)) *
      (MvPolynomial.X none + ∑ k : Fin d, MvPolynomial.C (l k (2, j)) * MvPolynomial.X (some k))) -
    MvPolynomial.C (q : ℂ) * MvPolynomial.X none ^ 3
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [P, map_sub, map_sum, map_mul, map_add, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C, map_zero, sub_eq_zero]
    have hx := h (x none) (fun k => x (some k))
    rw [← hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hswap : ∀ i : Fin 3,
        ∑ k : Fin d, l k (i, j) * x (some k) = ∑ k : Fin d, x (some k) * l k (i, j) := fun i =>
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hswap 0, hswap 1, hswap 2]
  have hS := congrArg (MvPolynomial.aeval (fun x : Option (Fin d) => x.elim ε u)) hP
  simp only [P, map_sub, map_sum, map_mul, map_add, map_pow, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, map_zero, map_natCast, Option.elim_none, Option.elim_some,
    sub_eq_zero] at hS
  exact hS
