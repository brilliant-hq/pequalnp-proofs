import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 400000

open Matrix

theorem PEqualNP.Outside.L_lib_556 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, ∑ j, H i j * A i j)^2 ≤
      (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  intro n H hn _ horth A
  -- Trivial case.
  by_cases hA : A = 0
  · subst hA; simp
  -- Euclidean setup.
  let E := EuclideanSpace ℝ (Fin n)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let fA := A.toEuclideanLin
  let U := LinearMap.range fA
  haveI : FiniteDimensional ℝ U := by infer_instance
  haveI : CompleteSpace U := FiniteDimensional.completeSpace ℝ U
  haveI : U.HasOrthogonalProjection := by infer_instance
  let p := U.starProjection
  let pc := p.toLinearMap
  let P := LinearMap.toMatrix b.toBasis b.toBasis pc
  -- Idempotence and symmetry of P.
  have hp_idem : IsIdempotentElem (↑p) := U.isIdempotentElem_starProjection
  have hpc_idem : pc * pc = pc := by
    rw [← ContinuousLinearMap.toLinearMap_mul]
    rw [hp_idem.eq]
  have hp_symm : pc.IsSymmetric := U.starProjection_isSymmetric
  have hP2 : P * P = P := by
    rw [← LinearMap.toMatrix_mul (v₁ := b.toBasis) pc pc]
    rw [hpc_idem]
  have hPtrans : Pᵀ = P := by
    have hadj : pc.adjoint = pc := hp_symm.adjoint_eq
    have := LinearMap.toMatrix_adjoint (v₁ := b) (v₂ := b) pc
    simpa [hadj] using this.symm
  -- P * A = A.
  have hPA : P * A = A := by
    have hcomp : pc.comp fA = fA := by
      ext x i
      have hv : U.starProjection (fA x) = fA x :=
        U.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self fA x)
      exact congrArg (fun v : E => v i) hv
    have htoA : LinearMap.toMatrix b.toBasis b.toBasis fA = A := by
      have : fA = Matrix.toLin b.toBasis b.toBasis A := by
        unfold fA
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal (m := Fin n)]
      rw [this]
      exact LinearMap.toMatrix_toLin b.toBasis b.toBasis A
    have hPdef : P = LinearMap.toMatrix b.toBasis b.toBasis pc := rfl
    calc P * A
        = LinearMap.toMatrix b.toBasis b.toBasis (pc.comp fA) := by
            rw [hPdef, ← htoA]
            rw [← LinearMap.toMatrix_mul (v₁ := b.toBasis) pc fA]
            rw [Module.End.mul_eq_comp]
        _ = LinearMap.toMatrix b.toBasis b.toBasis fA := by rw [hcomp]
        _ = A := htoA
  -- trace P = A.rank.
  have htrace : P.trace = (A.rank : ℝ) := by
    have hIsProj : LinearMap.IsProj U pc := by
      refine ⟨fun x => U.starProjection_apply_mem x, ?_⟩
      intro x hx
      exact U.starProjection_eq_self_iff.mpr hx
    have htraceLM : LinearMap.trace ℝ E pc = (Module.finrank ℝ U : ℝ) :=
      LinearMap.IsProj.trace (p := U) hIsProj
    have htr : LinearMap.trace ℝ E pc = P.trace := by
      simpa [P] using (LinearMap.trace_eq_matrix_trace ℝ b.toBasis pc)
    rw [← htr, htraceLM]
    have hr : Module.finrank ℝ U = A.rank := by
      have hUeq : U = LinearMap.range (Matrix.toLin b.toBasis b.toBasis A) := by
        rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal (m := Fin n)]
      rw [hUeq]
      exact (Matrix.rank_eq_finrank_range_toLin A b.toBasis b.toBasis).symm
    rw [hr]
  -- HH^T = n I.
  have hHH : H * Hᵀ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    exact horth i j
  -- Norm of P*H.
  let X := P * H
  have hnormX : (∑ i, ∑ j, X i j ^ 2) = (X * Xᵀ).trace := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hnormPH : (∑ i, ∑ j, ((P * H) i j)^2) = (n : ℝ) * (A.rank : ℝ) := by
    have hX : X = P * H := rfl
    rw [← hX]
    rw [hnormX]
    have h2 : (X * Xᵀ).trace = (Hᵀ * Pᵀ * P * H).trace := by
      rw [hX]
      rw [Matrix.transpose_mul (M := P) (N := H)]
      rw [Matrix.trace_mul_comm (P * H) (Hᵀ * Pᵀ)]
      rw [← Matrix.mul_assoc]
    rw [h2]
    rw [hPtrans]
    have h3 : (Hᵀ * P * P * H).trace = (Hᵀ * P * H).trace := by
      rw [Matrix.mul_assoc Hᵀ P P]
      rw [hP2]
    rw [h3]
    have h4 : (Hᵀ * P * H).trace = (P * H * Hᵀ).trace := by
      exact (Matrix.trace_mul_cycle P H Hᵀ).symm
    rw [h4]
    rw [Matrix.mul_assoc]
    rw [hHH]
    have h5 : (P * ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))).trace = (n : ℝ) * P.trace := by
      simp [Matrix.trace, Matrix.smul_apply, Finset.mul_sum]
    rw [h5, htrace]
  -- Correlation equality.
  have hcorr : (∑ i, ∑ j, H i j * A i j) = (∑ i, ∑ j, (P * H) i j * A i j) := by
    have hsumHA : (∑ i, ∑ j, H i j * A i j) = (Hᵀ * A).trace := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]
    let X := P * H
    have hsumX : (∑ i, ∑ j, X i j * A i j) = (Xᵀ * A).trace := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Finset.sum_comm]
    have hsumPHA : (∑ i, ∑ j, (P * H) i j * A i j) = ((P * H)ᵀ * A).trace := by
      simpa [X] using hsumX
    rw [hsumHA, hsumPHA]
    have htrans : (P * H)ᵀ = Hᵀ * Pᵀ := Matrix.transpose_mul (M := P) (N := H)
    rw [htrans, hPtrans]
    rw [Matrix.mul_assoc, hPA]
  -- Cauchy-Schwarz.
  have hcauchy : (∑ i, ∑ j, (P * H) i j * A i j)^2 ≤
      (∑ i, ∑ j, ((P * H) i j)^2) * (∑ i, ∑ j, (A i j)^2) := by
    rw [← Fintype.sum_prod_type' (fun i j => (P * H) i j * A i j)]
    rw [← Fintype.sum_prod_type' (fun i j => ((P * H) i j)^2)]
    rw [← Fintype.sum_prod_type' (fun i j => (A i j)^2)]
    apply Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
  -- Finish.
  calc (∑ i, ∑ j, H i j * A i j)^2
      = (∑ i, ∑ j, (P * H) i j * A i j)^2 := by rw [hcorr]
    _ ≤ (∑ i, ∑ j, ((P * H) i j)^2) * (∑ i, ∑ j, (A i j)^2) := hcauchy
    _ = (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by rw [hnormPH]