import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_785

open Finset

theorem two_mul_sum (r : ℕ) : 2 * ∑ q : Fin r, (q.val + 1) = r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => q + 1) r]
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem main {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (g : ℕ) (D : Fin g → (K →ₗ[F] K)) :
    ∃ V : Submodule F K,
      2 * Module.finrank F K ≤ 2 * Module.finrank F V +
        (∑ i, Module.finrank F (LinearMap.range (D i))) *
        ((∑ i, Module.finrank F (LinearMap.range (D i))) + 1) ∧
      ∀ w ∈ V, ∀ (S : Finset (Fin g)) (x : K),
        x = w * ∑ i ∈ S, D i x → x = 0 := by
  classical
  set n : Fin g → ℕ := fun i => Module.finrank F (LinearMap.range (D i)) with hn
  set r := ∑ i, n i with hr
  let b : ∀ i, Module.Basis (Fin (n i)) F (LinearMap.range (D i)) := fun i => Module.finBasis F _
  let ι := Σ i : Fin g, Fin (n i)
  let u : ι → K := fun p => ((b p.1 p.2 : LinearMap.range (D p.1)) : K)
  let f : ι → (K →ₗ[F] F) := fun p => ((b p.1).coord p.2).comp (D p.1).rangeRestrict
  let e : ι ≃ Fin r := finSigmaFinEquiv
  let P := Σ q : Fin r, Fin (q.val + 1)
  let lo : P → ι := fun pq => e.symm ⟨pq.2.val, lt_of_lt_of_le pq.2.isLt pq.1.isLt⟩
  let Φ : K →ₗ[F] (P → F) :=
    LinearMap.pi (fun pq => (f (lo pq)).comp (LinearMap.mulRight F (u (e.symm pq.1))))
  refine ⟨LinearMap.ker Φ, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 : Module.finrank F (LinearMap.range Φ) ≤ Fintype.card P := by
      have := Submodule.finrank_le (LinearMap.range Φ)
      simpa using this
    have h3 : 2 * Fintype.card P = r * (r + 1) := by
      simp only [P, Fintype.card_sigma, Fintype.card_fin]
      exact two_mul_sum r
    omega
  · intro w hw S x hx
    have hzero : ∀ p q : ι, e p ≤ e q → f p (w * u q) = 0 := by
      intro p q hpq
      have := congrFun (LinearMap.mem_ker.mp hw) ⟨e q, ⟨(e p).val, Nat.lt_succ_of_le hpq⟩⟩
      simpa [Φ, lo, LinearMap.pi_apply] using this
    have hD : ∀ i, D i x = ∑ k : Fin (n i), f ⟨i, k⟩ x • u ⟨i, k⟩ := by
      intro i
      have h := congrArg Subtype.val ((b i).sum_repr ((D i).rangeRestrict x))
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      simp only [f, u, LinearMap.comp_apply, Module.Basis.coord_apply]
      exact h.symm
    have hc : ∀ m : ℕ, ∀ p : ι, (e p).val = m → p.1 ∈ S → f p x = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro p hpm hpS
        have hx' : f p x = ∑ i ∈ S, ∑ k : Fin (n i), f ⟨i, k⟩ x • f p (w * u ⟨i, k⟩) := by
          conv_lhs => rw [hx]
          simp only [hD, Finset.mul_sum, mul_smul_comm, map_sum, map_smul]
        rw [hx']
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro k _
        by_cases hlt : e ⟨i, k⟩ < e p
        · rw [ih (e ⟨i, k⟩).val (by rw [← hpm]; exact Fin.lt_def.mp hlt) ⟨i, k⟩ rfl hi, zero_smul]
        · rw [hzero p ⟨i, k⟩ (not_lt.mp hlt), smul_zero]
    have hS : ∀ i ∈ S, D i x = 0 := fun i hi => by
      rw [hD]
      exact Finset.sum_eq_zero (fun k _ => by rw [hc _ ⟨i, k⟩ rfl hi, zero_smul])
    rw [hx, Finset.sum_eq_zero hS, mul_zero]

end PEqualNP.Outside.L_lib_785

open PEqualNP.Outside.L_lib_785 in
theorem PEqualNP.Outside.L_lib_785 :
  let F := ZMod 2
  ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
      (g : ℕ) (D : Fin g → (K →ₗ[F] K)),
    let r := ∑ i, Module.finrank F (LinearMap.range (D i))
    ∃ V : Submodule F K,
      2 * Module.finrank F K ≤ 2 * Module.finrank F V + r*(r+1) ∧
      ∀ w ∈ V, ∀ (S : Finset (Fin g)) (x : K),
        x = w * ∑ i ∈ S, D i x → x = 0 := by
  intro F K _ _ _ g D r
  exact main g D
