import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_551_aux

private theorem master_eq (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K)
    (r : ℕ) (U V : Fin r → List (Fin q))
    (hfin : Module.Finite K (Submodule.span K (Set.range (fun u : List (Fin q) =>
      fun v : List (Fin q) => f (u ++ v)))))
    (hrk : Module.finrank K (Submodule.span K (Set.range (fun u : List (Fin q) =>
      fun v : List (Fin q) => f (u ++ v)))) = r)
    (hdet : (Matrix.of (fun i j : Fin r => f (U i ++ V j))).det ≠ 0) :
    let H := Matrix.of (fun i j : Fin r => f (U i ++ V j))
    ∀ u v : List (Fin q),
      f (u ++ v) =
        dotProduct (Matrix.vecMul (fun j => f (u ++ V j)) H⁻¹) (fun i => f (U i ++ v)) := by
  intro H
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  let g : Fin r → R := fun i =>
    ⟨fun v => f (U i ++ v), Submodule.subset_span ⟨U i, rfl⟩⟩
  let ev : R →ₗ[K] (Fin r → K) :=
    { toFun := fun x j => x.1 (V j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hmul_inv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hunit
  have hinv_mul : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hunit
  have hev_lin : ∀ c : Fin r → K, ev (∑ i : Fin r, c i • g i) = Matrix.vecMul c H := by
    intro c
    ext j
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ev,
      LinearMap.coe_mk, AddHom.coe_mk, g, Matrix.vecMul, dotProduct, H, Matrix.of_apply]
  have hev_surj : Function.Surjective ev := by
    intro y
    refine ⟨∑ i : Fin r, (Matrix.vecMul y H⁻¹) i • g i, ?_⟩
    rw [hev_lin, Matrix.vecMul_vecMul, hinv_mul, Matrix.vecMul_one]
  have hev_inj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have hrn := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.mpr hev_surj, finrank_top, Module.finrank_fin_fun, hrk] at hrn
    omega
  intro u v
  let x : R := ⟨fun w => f (u ++ w), Submodule.subset_span ⟨u, rfl⟩⟩
  let c : Fin r → K := Matrix.vecMul (fun j => f (u ++ V j)) H⁻¹
  have heq : x = ∑ i : Fin r, c i • g i := by
    apply hev_inj
    rw [hev_lin c]
    change (fun j => f (u ++ V j)) = Matrix.vecMul (Matrix.vecMul (fun j => f (u ++ V j)) H⁻¹) H
    rw [Matrix.vecMul_vecMul, hinv_mul, Matrix.vecMul_one]
  have hval : x.1 v = (∑ i : Fin r, c i • g i).1 v := congrArg (fun z : R => z.1 v) heq
  simpa [x, g, dotProduct, Submodule.coe_sum, Finset.sum_apply] using hval

private theorem word_mulVec (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K)
    (r : ℕ) (U V : Fin r → List (Fin q))
    (hmaster : ∀ u v : List (Fin q),
      f (u ++ v) = dotProduct
        (Matrix.vecMul (fun j => f (u ++ V j))
          (Matrix.of (fun i j : Fin r => f (U i ++ V j)))⁻¹)
        (fun i => f (U i ++ v))) :
    let H := Matrix.of (fun i j : Fin r => f (U i ++ V j))
    let B := fun a : Fin q => Matrix.of (fun i j : Fin r => f (U i ++ [a] ++ V j)) * H⁻¹
    ∀ w : List (Fin q),
      (fun i : Fin r => f (U i ++ w)) = Matrix.mulVec ((w.map B).prod) (fun i => f (U i)) := by
  intro H B w
  induction w with
  | nil =>
    ext i
    simp
  | cons a w ih =>
    ext i
    have hstep : f (U i ++ a :: w) = f ((U i ++ [a]) ++ w) := by simp
    rw [hstep, hmaster (U i ++ [a]) w, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ← ih]
    rfl

end PEqualNP.Outside.L_lib_551_aux

theorem PEqualNP.Outside.L_lib_551 : ∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  ∀ (r : ℕ) (U V : Fin r → List (Fin q)),
    Module.Finite K R → Module.finrank K R = r →
    let H := Matrix.of (fun i j : Fin r => f (U i ++ V j))
    H.det ≠ 0 →
    let B := fun a : Fin q =>
      Matrix.of (fun i j : Fin r => f (U i ++ [a] ++ V j)) * H⁻¹
    ∀ w : List (Fin q), f w =
      dotProduct (Matrix.vecMul (fun j => f (V j)) H⁻¹)
        (Matrix.mulVec ((w.map B).prod) (fun i => f (U i))) := by
  intro K _ q f R r U V hfin hrk H hdet B w
  have hmaster := PEqualNP.Outside.L_lib_551_aux.master_eq K q f r U V hfin hrk hdet
  have hword := PEqualNP.Outside.L_lib_551_aux.word_mulVec K q f r U V hmaster w
  have h0 := hmaster [] w
  simp only [List.nil_append] at h0
  rw [h0, hword]
