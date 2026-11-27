import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_763

open Matrix Kronecker

theorem decomp {F : Type} [Field F] {n m : ℕ} (A : Matrix (Fin n) (Fin m) F) :
    ∃ r, A.rank = r ∧ ∃ (U : Matrix (Fin n) (Fin r) F) (V : Matrix (Fin r) (Fin m) F),
      A = U * V := by
  let W := LinearMap.range A.mulVecLin
  let bs := Module.finBasisOfFinrankEq F W (rfl : Module.finrank F W = A.rank)
  let w : Fin m → W := fun j => ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨_, rfl, Matrix.of fun i k => (bs k : Fin n → F) i, Matrix.of fun k j => bs.repr (w j) k, ?_⟩
  ext i j
  have h := congrArg (fun x : W => (x : Fin n → F) i) (bs.sum_repr (w j))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  have hw : (w j : Fin n → F) i = A i j := by simp [w, Matrix.mulVec_single]
  rw [← hw, ← h, Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_comm]
  rfl

theorem leftInv {F : Type} [Field F] {p r : ℕ} (M : Matrix (Fin p) (Fin r) F) (h : M.rank = r) :
    ∃ L : Matrix (Fin r) (Fin p) F, L * M = 1 := by
  have hk := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have hr : Module.finrank F (LinearMap.range (Matrix.toLin' M)) = r := h
  rw [hr, Module.finrank_fin_fun] at hk
  have hker : LinearMap.ker (Matrix.toLin' M) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem factors {F : Type} [Field F] {n m : ℕ} (A : Matrix (Fin n) (Fin m) F) :
    ∃ r, A.rank = r ∧ ∃ (U : Matrix (Fin n) (Fin r) F) (V : Matrix (Fin r) (Fin m) F)
      (L : Matrix (Fin r) (Fin n) F) (R : Matrix (Fin m) (Fin r) F),
      A = U * V ∧ L * U = 1 ∧ V * R = 1 := by
  obtain ⟨r, hr, U, V, hA⟩ := decomp A
  refine ⟨r, hr, ?_⟩
  have hU : U.rank = r := by
    apply le_antisymm
    · simpa using U.rank_le_card_width
    · calc r = A.rank := hr.symm
        _ = (U * V).rank := by rw [hA]
        _ ≤ U.rank := rank_mul_le_left _ _
  have hV : Vᵀ.rank = r := by
    rw [rank_transpose]
    apply le_antisymm
    · simpa using V.rank_le_card_height
    · calc r = A.rank := hr.symm
        _ = (U * V).rank := by rw [hA]
        _ ≤ V.rank := rank_mul_le_right _ _
  obtain ⟨L, hL⟩ := leftInv U hU
  obtain ⟨L2, hL2⟩ := leftInv Vᵀ hV
  refine ⟨U, V, L, L2ᵀ, hA, hL, ?_⟩
  have := congrArg Matrix.transpose hL2
  rwa [transpose_mul, transpose_transpose, transpose_one] at this

end PEqualNP.Outside.L_lib_763

open PEqualNP.Outside.L_lib_763 in
theorem PEqualNP.Outside.L_lib_763 : ∀ (F : Type) [Field F] (a b c d : ℕ) (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin c) (Fin d) F),
  let K : Matrix (Fin a × Fin c) (Fin b × Fin d) F := fun p q => A p.1 q.1 * B p.2 q.2
  K.rank = A.rank * B.rank := by
  intro F _ a b c d A B K
  have hK0 : K = Matrix.kroneckerMap (· * ·) A B := rfl
  obtain ⟨r1, hr1, U, V, L, R, hA, hL, hR⟩ := factors A
  obtain ⟨r2, hr2, U', V', L', R', hB, hL', hR'⟩ := factors B
  rw [hr1, hr2]
  subst hA hB
  have hK : K = Matrix.kroneckerMap (· * ·) U U' * Matrix.kroneckerMap (· * ·) V V' := by
    rw [hK0, Matrix.mul_kronecker_mul]
  apply le_antisymm
  · rw [hK]
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    simpa using Matrix.rank_le_card_width (Matrix.kroneckerMap (· * ·) U U')
  · have h1 : Matrix.kroneckerMap (· * ·) L L' * K * Matrix.kroneckerMap (· * ·) R R' = 1 := by
      rw [hK0, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      rw [← Matrix.mul_assoc L U V, hL, Matrix.one_mul, hR, ← Matrix.mul_assoc L' U' V', hL',
        Matrix.one_mul, hR', Matrix.one_kronecker_one]
    have h2 := (Matrix.rank_mul_le_left (Matrix.kroneckerMap (· * ·) L L' * K)
      (Matrix.kroneckerMap (· * ·) R R')).trans (Matrix.rank_mul_le_right _ K)
    rw [h1, Matrix.rank_one] at h2
    simpa using h2
