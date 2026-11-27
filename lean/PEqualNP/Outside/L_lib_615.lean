import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_615

open Finset MvPolynomial

noncomputable section

abbrev Pl (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

def ex {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

theorem ex_apply {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ex S j = if j ∈ S then 1 else 0 := by
  simp [ex, Finset.sum_apply', Finsupp.single_apply]

theorem ex_le_one {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ex S j ≤ 1 := by
  rw [ex_apply]; split_ifs <;> omega

theorem ex_inj {n : ℕ} {S T : Finset (Fin n)} (h : ex S = ex T) : S = T := by
  ext j
  have := DFunLike.congr_fun h j
  rw [ex_apply, ex_apply] at this
  by_cases h1 : j ∈ S <;> by_cases h2 : j ∈ T <;> simp_all

theorem ex_degree {n : ℕ} (S : Finset (Fin n)) : (ex S).degree = S.card := by
  simp [ex, map_sum, Finsupp.degree_single]

theorem ex_insert {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (h : i ∉ S) :
    ex (insert i S) = Finsupp.single i 1 + ex S := by
  simp [ex, Finset.sum_insert h]

theorem prodX {n : ℕ} (S : Finset (Fin n)) : ∏ i ∈ S, (X i : Pl n) = monomial (ex S) 1 := by
  rw [ex, monomial_sum_one]
  rfl

theorem coeff_ex_monomial {n : ℕ} (U S : Finset (Fin n)) :
    (monomial (ex S) (1 : ZMod 2) : Pl n).coeff (ex U) = if U = S then 1 else 0 := by
  rw [coeff_monomial]
  by_cases h : U = S
  · simp [h]
  · rw [if_neg (fun h' => h (ex_inj h').symm), if_neg h]

theorem single_add_ex_iff {n : ℕ} (i : Fin n) (S U : Finset (Fin n)) :
    Finsupp.single i 1 + ex S = ex U ↔ i ∉ S ∧ U = insert i S := by
  constructor
  · intro h
    have hi : i ∉ S := by
      intro hi
      have := DFunLike.congr_fun h i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      have h2 := ex_le_one U i
      rw [ex_apply, if_pos hi] at this
      omega
    refine ⟨hi, ?_⟩
    rw [← ex_insert hi] at h
    exact (ex_inj h).symm
  · rintro ⟨hi, rfl⟩
    rw [ex_insert hi]

theorem coeff_X_mul {n : ℕ} (i : Fin n) (S U : Finset (Fin n)) :
    ((X i : Pl n) * monomial (ex S) 1).coeff (ex U) = if i ∉ S ∧ U = insert i S then 1 else 0 := by
  rw [X, monomial_mul_monomial, coeff_monomial, one_mul]
  by_cases h : i ∉ S ∧ U = insert i S
  · rw [if_pos ((single_add_ex_iff i S U).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((single_add_ex_iff i S U).1 h')), if_neg h]

def lin {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) : Pl n := ∑ j, C (g j i) * X j

def cm {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) (ZMod 2) :=
  Matrix.of fun U S => (∏ i ∈ S, lin g i).coeff (ex U)

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem coeff_sq_mul {n : ℕ} (U : Finset (Fin n)) (k : Fin n) (q : Pl n) :
    ((X k) ^ 2 * q).coeff (ex U) = 0 := by
  rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial', if_neg]
  intro h
  have := h k
  simp only [Finsupp.single_eq_same] at this
  have := ex_le_one U k
  omega

theorem coeff_bind {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (U : Finset (Fin n)) (q : Pl n) :
    (bind₁ (lin g) q).coeff (ex U) = ∑ T, cm g U T * q.coeff (ex T) := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    by_cases hsq : ∃ k, 2 ≤ u k
    · obtain ⟨k, hk⟩ := hsq
      have e : monomial u a = (X k) ^ 2 * monomial (u - Finsupp.single k 2) a := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le]
        intro j
        by_cases hj : j = k
        · subst hj; simpa using hk
        · simp [Finsupp.single_apply, Ne.symm hj]
      have hr : ∀ T : Finset (Fin n), (monomial u a : Pl n).coeff (ex T) = 0 := by
        intro T
        rw [coeff_monomial, if_neg]
        intro h
        have := ex_le_one T k
        rw [h] at hk
        omega
      simp only [hr, mul_zero, Finset.sum_const_zero]
      rw [e, map_mul, map_pow, bind₁_X_right, lin, sum_pow_char, Finset.sum_mul, coeff_sum]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [mul_pow, mul_assoc, mul_left_comm, coeff_sq_mul]
    · push Not at hsq
      have hu : u = ex u.support := by
        ext j
        rw [ex_apply]
        have := hsq j
        by_cases hj : j ∈ u.support
        · rw [if_pos hj]
          have : u j ≠ 0 := Finsupp.mem_support_iff.1 hj
          omega
        · rw [if_neg hj]
          exact Finsupp.notMem_support_iff.1 hj
      rw [hu]
      set T0 := u.support
      have e : monomial (ex T0) a = C a * ∏ i ∈ T0, (X i : Pl n) := by
        rw [prodX, C_mul_monomial, mul_one]
      rw [e, map_mul, bind₁_C_right, map_prod, coeff_C_mul]
      simp only [bind₁_X_right, coeff_C_mul, prodX, coeff_ex_monomial, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [cm, Matrix.of_apply, mul_comm]
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [MvPolynomial.coeff_add, mul_add]

theorem lin_mul {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    lin (g * h) i = bind₁ (lin g) (lin h i) := by
  simp only [lin, map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem cm_mul {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) : cm (g * h) = cm g * cm h := by
  ext U S
  rw [Matrix.mul_apply]
  simp only [cm, Matrix.of_apply]
  simp_rw [lin_mul]
  rw [← map_prod, coeff_bind]
  rfl

theorem lin_one {n : ℕ} (i : Fin n) : lin (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i = X i := by
  simp [lin, Matrix.one_apply, apply_ite C]

theorem cm_one {n : ℕ} : cm (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext U S
  simp only [cm, Matrix.of_apply, lin_one, prodX, coeff_ex_monomial, Matrix.one_apply]

theorem cm_homog {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (U S : Finset (Fin n))
    (h : U.card ≠ S.card) : cm g U S = 0 := by
  simp only [cm, Matrix.of_apply]
  have hl : ∀ i, (lin g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  have hp := IsHomogeneous.prod S (lin g) (fun _ => 1) (fun i _ => hl i)
  apply hp.coeff_eq_zero
  rw [ex_degree]
  simpa using h

theorem lin_add {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    lin (g + h) i = lin g i + lin h i := by
  simp only [lin, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem sign_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : ZMod 2) :
    (Equiv.Perm.sign σ) • x = x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · rw [Units.neg_smul, one_smul, ZMod.neg_eq_self_mod_two]

theorem top_coeff {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    cm g univ univ = g.det := by
  simp only [cm, Matrix.of_apply, lin]
  rw [Finset.prod_univ_sum (fun _ => univ) (fun i j => C (g j i) * (X j : Pl n)), coeff_sum]
  have hterm : ∀ f : Fin n → Fin n, (∏ i, C (g (f i) i) * (X (f i) : Pl n)) =
      monomial (∑ i, Finsupp.single (f i) 1) (∏ i, g (f i) i) := by
    intro f
    rw [Finset.prod_mul_distrib, ← map_prod,
      show ∏ i, (X (f i) : Pl n) = monomial (∑ i, Finsupp.single (f i) 1) 1 from
        (monomial_sum_one _ _).symm, C_mul_monomial, mul_one]
  simp_rw [hterm, coeff_monomial]
  rw [Fintype.piFinset_univ, ← Finset.sum_filter, Matrix.det_apply]
  simp_rw [sign_smul]
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) ?_ ?_ ?_ ?_
  · intro σ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Equiv.sum_comp σ (fun j => Finsupp.single j (1 : ℕ))
  · intro a _ b _ h
    exact Equiv.ext (fun x => congrFun h x)
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hs : Function.Surjective f := by
      intro j
      by_contra hne
      push Not at hne
      have := DFunLike.congr_fun hf.2 j
      rw [ex_apply, if_pos (Finset.mem_univ _), Finset.sum_apply'] at this
      simp [Finsupp.single_apply, hne] at this
    exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
  · intro σ _
    rfl

theorem trace_id {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    cm (1 + g) univ univ = ∑ S, cm g S S := by
  simp only [cm, Matrix.of_apply]
  rw [show (∏ i, lin (1 + g) i) = ∏ i, (lin g i + X i) from
    Finset.prod_congr rfl (fun i _ => by rw [lin_add, lin_one, add_comm])]
  rw [Finset.prod_add, Finset.powerset_univ, coeff_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [prodX, coeff_mul_monomial', if_pos, mul_one]
  · congr 1
    ext j
    simp only [Finsupp.tsub_apply, ex_apply]
    by_cases h : j ∈ t <;> simp [h]
  · intro j
    simp only [ex_apply]
    by_cases h : j ∈ t <;> simp [h]

theorem cm_empty {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) : cm g ∅ ∅ = 1 := by
  simp [cm, ex]

/- transvections and permutation matrices -/

def tv {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.transvection i j 1

theorem tv_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) : tv i j * tv i j = 1 := by
  have := Matrix.transvection_mul_transvection_same i j h (1 : ZMod 2) 1
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero] at this
  exact this

theorem lin_tv {n : ℕ} (i j k : Fin n) : lin (tv i j) k = X k + if k = j then X i else 0 := by
  rw [tv, Matrix.transvection, lin_add, lin_one]
  congr 1
  simp only [lin, Matrix.single, Matrix.of_apply]
  by_cases hk : k = j
  · subst hk
    simp [apply_ite C, ite_mul, Finset.sum_ite_eq]
  · simp [hk, Ne.symm hk]

theorem cm_tv {n : ℕ} {i j : Fin n} (hij : i ≠ j) (U S : Finset (Fin n)) :
    cm (tv i j) U S = (if U = S then 1 else 0) +
      (if j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) then 1 else 0) := by
  simp only [cm, Matrix.of_apply]
  simp_rw [lin_tv]
  by_cases hj : j ∈ S
  · rw [← Finset.mul_prod_erase S _ hj, if_pos rfl]
    have : ∏ x ∈ S.erase j, (X x + if x = j then X i else 0 : Pl n) = ∏ x ∈ S.erase j, X x :=
      Finset.prod_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx), add_zero])
    rw [this, prodX, add_mul, MvPolynomial.coeff_add, coeff_X_mul, coeff_X_mul,
      Finset.insert_erase hj]
    congr 1
    · simp
    · simp [Finset.mem_erase, hij, hj]
  · have : ∏ x ∈ S, (X x + if x = j then X i else 0 : Pl n) = ∏ x ∈ S, X x :=
      Finset.prod_congr rfl (fun x hx => by
        rw [if_neg (show x ≠ j from fun h => hj (h ▸ hx)), add_zero])
    rw [this, prodX, coeff_ex_monomial]
    simp [hj]

def pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun l k => if l = σ k then 1 else 0

theorem pm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : pm σ * pm τ = pm (σ * τ) := by
  ext l m
  rw [Matrix.mul_apply]
  simp [pm, Matrix.of_apply, Equiv.Perm.mul_apply]
  by_cases h : l = σ (τ m) <;> simp [h]

theorem pm_one {n : ℕ} : pm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext l m
  simp [pm, Matrix.of_apply, Matrix.one_apply]
  by_cases h : l = m <;> simp [h]

theorem lin_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : lin (pm σ) k = X (σ k) := by
  simp [lin, pm, apply_ite C, ite_mul, Finset.sum_ite_eq']

theorem cm_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (U S : Finset (Fin n)) :
    cm (pm σ) U S = if U = S.map σ.toEmbedding then 1 else 0 := by
  simp only [cm, Matrix.of_apply, lin_pm]
  rw [show ∏ k ∈ S, (X (σ k) : Pl n) = ∏ l ∈ S.map σ.toEmbedding, X l from
    (Finset.prod_map S σ.toEmbedding (fun l => (X l : Pl n))).symm, prodX, coeff_ex_monomial]

/- the matrices over K -/

abbrev VV (n : ℕ) := Fin n → ZMod 2

def ιK (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

def hc (K : Type) [Field K] [CharP K 2] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K := (cm g).map (ιK K)

theorem hc_apply (K : Type) [Field K] [CharP K 2] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2))
    (U S : Finset (Fin n)) : hc K g U S = ιK K (cm g U S) := rfl

theorem hc_mul (K : Type) [Field K] [CharP K 2] {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) :
    hc K (g * h) = hc K g * hc K h := by
  rw [hc, cm_mul, Matrix.map_mul]
  rfl

theorem hc_one (K : Type) [Field K] [CharP K 2] {n : ℕ} :
    hc K (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  rw [hc, cm_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem two_K (K : Type) [Field K] [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

theorem self_add_self (z : VV n) : z + z = 0 := by
  funext j
  exact (by decide : ∀ t : ZMod 2, t + t = 0) (z j)

theorem parity (K : Type) [Field K] [CharP K 2] {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2))
    (c : Fin n → ZMod 2) :
    ((((univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c)).card : ℕ) : K) =
      ιK K N.det := by
  by_cases hd : N.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
    have hvk : v k = 1 := (zmod2_cases (v k)).resolve_left hk
    have h2 : ∀ x : Fin n → ZMod 2, x + v + v = x := by
      intro x
      rw [add_assoc, self_add_self, add_zero]
    set F := (univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c)
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun x => x k = 0)
    have heq : (F.filter (fun x => x k = 0)).card = (F.filter (fun x => ¬ x k = 0)).card := by
      refine Finset.card_nbij' (fun x => x + v) (fun x => x + v) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [F, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        refine ⟨by rw [Matrix.mulVec_add, hx.1, hv, add_zero], ?_⟩
        rw [Pi.add_apply, hx.2, zero_add]
        exact hk
      · intro x hx
        simp only [F, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        refine ⟨by rw [Matrix.mulVec_add, hx.1, hv, add_zero], ?_⟩
        have : x k = 1 := (zmod2_cases _).resolve_left hx.2
        rw [Pi.add_apply, this, hvk]
        rfl
      · intro x _
        exact h2 x
      · intro x _
        exact h2 x
    rw [hd, map_zero, ← hsplit, heq, ← two_mul, Nat.cast_mul, Nat.cast_ofNat, two_K, zero_mul]
  · have hu : IsUnit N.det := isUnit_iff_ne_zero.2 hd
    have e : (univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c) = {N⁻¹.mulVec c} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      · intro h
        rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have h1 : N.det = 1 := (zmod2_cases _).resolve_left hd
    rw [e, Finset.card_singleton, h1, map_one, Nat.cast_one]

def mat {n : ℕ} (g : VV n ≃ₗ[ZMod 2] VV n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  LinearMap.toMatrix' (g : VV n →ₗ[ZMod 2] VV n)

theorem mat_trans {n : ℕ} (g h : VV n ≃ₗ[ZMod 2] VV n) : mat (h.trans g) = mat g * mat h := by
  rw [mat, LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rfl

theorem det_mat {n : ℕ} (g : VV n ≃ₗ[ZMod 2] VV n) : (mat g).det = 1 := by
  have h : mat g * mat g.symm = 1 := by
    rw [← mat_trans, LinearEquiv.symm_trans_self, mat]
    exact LinearMap.toMatrix'_id
  have : (mat g).det * (mat g.symm).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact (zmod2_cases _).resolve_left (left_ne_zero_of_mul_eq_one this)

def Alg (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    Submodule K (Matrix (Finset (Fin n)) (Finset (Fin n)) K) :=
  Submodule.span K (Set.range fun g : VV n ≃ₗ[ZMod 2] VV n => hc K (mat g))

theorem mem_of_inv (K : Type) [Field K] [CharP K 2] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) (ZMod 2))
    (h1 : M * M' = 1) (h2 : M' * M = 1) : hc K M ∈ Alg K n := by
  apply Submodule.subset_span
  refine ⟨Matrix.toLin'OfInv h2 h1, ?_⟩
  simp only [mat]
  congr 1
  have : ((Matrix.toLin'OfInv h2 h1 : VV n ≃ₗ[ZMod 2] VV n) : VV n →ₗ[ZMod 2] VV n) =
      Matrix.toLin' M := LinearMap.ext fun x => rfl
  rw [this, LinearMap.toMatrix'_toLin']

theorem one_mem_alg (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) K) ∈ Alg K n := by
  rw [← hc_one K]
  exact mem_of_inv K 1 1 (mul_one 1) (mul_one 1)

theorem alg_mul (K : Type) [Field K] [CharP K 2] {n : ℕ}
    {x y : Matrix (Finset (Fin n)) (Finset (Fin n)) K} (hx : x ∈ Alg K n) (hy : y ∈ Alg K n) :
    x * y ∈ Alg K n := by
  have := Submodule.mul_mem_mul hx hy
  rw [Alg, Submodule.span_mul_span] at this
  refine Submodule.span_le.2 ?_ this
  rintro _ ⟨a, ⟨g, rfl⟩, b, ⟨h, rfl⟩, rfl⟩
  apply Submodule.subset_span
  exact ⟨h.trans g, by simp only; rw [mat_trans, hc_mul]⟩

def Nm (K : Type) [Field K] [CharP K 2] {n : ℕ} (i j : Fin n) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K := hc K (tv i j) - 1

theorem Nm_mem (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Nm K i j ∈ Alg K n :=
  Submodule.sub_mem _ (mem_of_inv K _ _ (tv_sq h) (tv_sq h)) (one_mem_alg K n)

theorem Nm_apply (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (h : i ≠ j)
    (U S : Finset (Fin n)) :
    Nm K i j U S = if j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) then 1 else 0 := by
  rw [Nm, Matrix.sub_apply, hc_apply, cm_tv h, map_add, Matrix.one_apply]
  by_cases h1 : U = S <;> by_cases h2 : j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) <;>
    simp [h1, h2]

theorem NN (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Nm K j i * Nm K i j =
      Matrix.diagonal (fun S => if j ∈ S ∧ i ∉ S then (1 : K) else 0) := by
  ext U S
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp_rw [Nm_apply K hij, Nm_apply K (Ne.symm hij)]
  by_cases hS : j ∈ S ∧ i ∉ S
  · rw [Finset.sum_eq_single (insert i (S.erase j))]
    · have h1 : i ∈ insert i (S.erase j) := Finset.mem_insert_self _ _
      have h2 : j ∉ insert i (S.erase j) := by simp [Ne.symm hij]
      have h3 : (insert i (S.erase j)).erase i = S.erase j :=
        Finset.erase_insert (by simp [hS.2])
      rw [h3, Finset.insert_erase hS.1]
      by_cases hU : U = S
      · subst hU
        simp [h1, h2, hS]
      · simp [h1, h2, hS, hU]
    · intro V _ hV
      simp [hV]
    · simp
  · rw [Finset.sum_eq_zero]
    · by_cases hU : U = S
      · subst hU
        simp [hS]
      · simp [hU]
    · intro V _
      have : ¬ (j ∈ S ∧ i ∉ S ∧ V = insert i (S.erase j)) := fun h => hS ⟨h.1, h.2.1⟩
      rw [if_neg this, mul_zero]

theorem diag_prod (K : Type) [Field K] [CharP K 2] {n : ℕ} (Q : Finset (Fin n × Fin n))
    (hQ : ∀ q ∈ Q, q.1 ≠ q.2) :
    Matrix.diagonal (fun S => ∏ q ∈ Q, if q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0) ∈ Alg K n := by
  induction Q using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Matrix.diagonal_one]
    exact one_mem_alg K n
  | @insert q Q hq ih =>
    have hQ' : ∀ q' ∈ Q, q'.1 ≠ q'.2 := fun q' h => hQ q' (Finset.mem_insert_of_mem h)
    simp_rw [Finset.prod_insert hq]
    rw [← Matrix.diagonal_mul_diagonal]
    refine alg_mul K ?_ (ih hQ')
    rw [← NN K (Ne.symm (hQ q (Finset.mem_insert_self _ _)))]
    exact alg_mul K (Nm_mem K (hQ q (Finset.mem_insert_self _ _)))
      (Nm_mem K (Ne.symm (hQ q (Finset.mem_insert_self _ _))))

theorem diag_unit (K : Type) [Field K] [CharP K 2] {n : ℕ} (S0 : Finset (Fin n))
    (h1 : S0.Nonempty) (h2 : S0ᶜ.Nonempty) :
    Matrix.diagonal (fun S => if S = S0 then (1 : K) else 0) ∈ Alg K n := by
  have e : (fun S => if S = S0 then (1 : K) else 0) =
      fun S => ∏ q ∈ S0 ×ˢ S0ᶜ, if q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0 := by
    funext S
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    by_cases hS : S = S0
    · subst hS
      rw [if_pos rfl, if_pos]
      intro q hq
      rw [Finset.mem_product, Finset.mem_compl] at hq
      exact hq
    · rw [if_neg hS, if_neg]
      intro hall
      apply hS
      ext x
      constructor
      · intro hx
        by_contra hx0
        obtain ⟨j, hj⟩ := h1
        exact (hall (j, x) (Finset.mem_product.2 ⟨hj, Finset.mem_compl.2 hx0⟩)).2 hx
      · intro hx
        obtain ⟨i, hi⟩ := h2
        exact (hall (x, i) (Finset.mem_product.2 ⟨hx, hi⟩)).1
  rw [e]
  refine diag_prod K _ (fun q hq => ?_)
  rw [Finset.mem_product, Finset.mem_compl] at hq
  intro h
  exact hq.2 (h ▸ hq.1)

theorem exists_perm_map {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), S.map σ.toEmbedding = T := by
  have hc : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ T} := by
    simp [Fintype.card_coe, h]
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hc
  refine ⟨Equiv.extendSubtype e, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Equiv.extendSubtype_mem e x hx
  · rw [Finset.card_map, h]

theorem unit_mem (K : Type) [Field K] [CharP K 2] {n : ℕ} (S0 T : Finset (Fin n))
    (h1 : S0.Nonempty) (h2 : S0ᶜ.Nonempty) (h : S0.card = T.card) :
    (Matrix.of fun U S => if U = T ∧ S = S0 then (1 : K) else 0) ∈ Alg K n := by
  obtain ⟨σ, hσ⟩ := exists_perm_map S0 T h
  have hp : hc K (pm σ) ∈ Alg K n :=
    mem_of_inv K (pm σ) (pm σ⁻¹) (by rw [pm_mul, mul_inv_cancel, pm_one])
      (by rw [pm_mul, inv_mul_cancel, pm_one])
  have := alg_mul K hp (diag_unit K S0 h1 h2)
  convert this using 1
  ext U S
  rw [Matrix.mul_diagonal, hc_apply, cm_pm, Matrix.of_apply]
  by_cases hS : S = S0
  · subst hS
    rw [hσ]
    by_cases hU : U = T <;> simp [hU]
  · simp [hS]

/- the index set -/

abbrev pr (n : ℕ) (a : Finset (Fin n) × Finset (Fin n)) : Prop :=
  a.1.card = a.2.card ∧ 0 < a.1.card ∧ a.1.card < n

abbrev Ix (n : ℕ) := {a : Finset (Fin n) × Finset (Fin n) // pr n a}

theorem card_Y (n : ℕ) :
    ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
      (fun a => a.1.card = a.2.card)).card = Nat.choose (2 * n) n := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ S : Finset (Fin n),
      (∑ T : Finset (Fin n), if S.card = T.card then 1 else 0) = n.choose S.card := by
    intro S
    rw [← Finset.card_filter]
    have : (univ : Finset (Finset (Fin n))).filter (fun T => S.card = T.card) =
        Finset.powersetCard S.card univ := by
      ext T
      simp [Finset.mem_powersetCard, eq_comm]
    rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp_rw [h]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin,
    ← Nat.sum_range_choose_sq]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_eq_mul, sq]

theorem card_Ix {n : ℕ} (hn : 0 < n) : Fintype.card (Ix n) = Nat.choose (2 * n) n - 2 := by
  rw [Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun a => a.1.card = a.2.card))
    (fun a => 0 < a.1.card ∧ a.1.card < n)
  rw [Finset.filter_filter, card_Y] at hsplit
  have e2 : ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
      (fun a => a.1.card = a.2.card)).filter (fun a => ¬ (0 < a.1.card ∧ a.1.card < n)) =
      {(∅, ∅), (univ, univ)} := by
    ext ⟨S, T⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_and, not_lt]
    constructor
    · rintro ⟨hST, h⟩
      by_cases h0 : S.card = 0
      · left
        have hT : T.card = 0 := hST ▸ h0
        exact ⟨Finset.card_eq_zero.1 h0, Finset.card_eq_zero.1 hT⟩
      · right
        have hle : S.card ≤ n := by simpa using S.card_le_univ
        have hS : S.card = n := le_antisymm hle (h (Nat.pos_of_ne_zero h0))
        have hT : T.card = n := hST ▸ hS
        exact ⟨Finset.eq_univ_of_card S (by simp [hS]), Finset.eq_univ_of_card T (by simp [hT])⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · simp
      · simp
  have hne : ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ≠ (univ, univ) := by
    intro h
    have := congrArg (fun a => a.1.card) h
    simp at this
    omega
  rw [e2, Finset.card_pair hne] at hsplit
  have e3 : ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun x => pr n x)).card =
      ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun a =>
        a.1.card = a.2.card ∧ 0 < a.1.card ∧ a.1.card < n)).card := rfl
  rw [e3]
  omega

theorem split_sum (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (F : Finset (Fin n) → Finset (Fin n) → K)
    (hz : ∀ S T, S.card ≠ T.card → F S T = 0) (h0 : F ∅ ∅ = 1) (h1 : F univ univ = 1) :
    ∑ S, ∑ T, F S T = ∑ a : Ix n, F a.1.1 a.1.2 := by
  rw [← Fintype.sum_prod_type' F, ← Fintype.sum_subtype_add_sum_subtype (pr n) (fun a => F a.1 a.2)]
  have hz2 : ∑ a : {a // ¬ pr n a}, F a.1.1 a.1.2 = 0 := by
    have ha : ¬ pr n (∅, ∅) := by simp [pr]
    have hb : ¬ pr n (univ, univ) := by simp [pr]
    rw [Fintype.sum_eq_add ⟨(∅, ∅), ha⟩ ⟨(univ, univ), hb⟩]
    · simp only
      rw [h0, h1, one_add_one_eq_two, two_K]
    · intro h
      have := congrArg (fun x : {a // ¬ pr n a} => x.1.1.card) h
      simp at this
      omega
    · rintro ⟨⟨S, T⟩, hST⟩ ⟨hna, hnb⟩
      by_cases hc : S.card = T.card
      · exfalso
        simp only [pr, not_and, not_lt] at hST
        by_cases h0' : S.card = 0
        · apply hna
          have hT : T.card = 0 := hc ▸ h0'
          rw [Finset.card_eq_zero] at h0' hT
          subst h0'
          subst hT
          rfl
        · apply hnb
          have hle : S.card ≤ n := by simpa using S.card_le_univ
          have hS : S.card = n := le_antisymm hle (hST hc (Nat.pos_of_ne_zero h0'))
          have hT : T.card = n := hc ▸ hS
          have e1 := Finset.eq_univ_of_card S (by simp [hS])
          have e2 := Finset.eq_univ_of_card T (by simp [hT])
          subst e1
          subst e2
          rfl
      · exact hz S T hc
  rw [hz2, add_zero]

theorem key_iff {n : ℕ} (a b x : VV n) : a + b = x ↔ x + a = b := by
  constructor
  · intro h
    rw [← h, add_comm a b, add_assoc, self_add_self, add_zero]
  · intro h
    rw [← h, add_comm x a, ← add_assoc, self_add_self, zero_add]

theorem fix_formula (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (p r : (VV n ≃ₗ[ZMod 2] VV n) × VV n) :
    ((((univ : Finset (VV n)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card : ℕ) : K) =
      ∑ a : Ix n, hc K (mat p.1) a.1.2 a.1.1 * hc K (mat r.1) a.1.1 a.1.2 := by
  have hfilt : (univ : Finset (VV n)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x) =
      univ.filter (fun x => (1 + mat r.1 * mat p.1).mulVec x = r.1 p.2 + r.2) := by
    apply Finset.filter_congr
    intro x _
    have hm : (mat r.1 * mat p.1).mulVec x = r.1 (p.1 x) := by
      rw [← Matrix.mulVec_mulVec, mat, mat, LinearMap.toMatrix'_mulVec,
        LinearMap.toMatrix'_mulVec]
      rfl
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hm, map_add, add_assoc]
    exact key_iff _ _ _
  rw [hfilt, parity K, ← top_coeff, trace_id, map_sum]
  have : ∀ S : Finset (Fin n), ιK K (cm (mat r.1 * mat p.1) S S) =
      ∑ T, hc K (mat r.1) S T * hc K (mat p.1) T S := by
    intro S
    rw [cm_mul, Matrix.mul_apply, map_sum]
    simp only [map_mul, hc_apply]
  simp_rw [this]
  rw [split_sum K hn (fun S T => hc K (mat r.1) S T * hc K (mat p.1) T S)]
  · exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  · intro S T h
    rw [hc_apply, cm_homog _ _ _ h, map_zero, zero_mul]
  · rw [hc_apply, hc_apply, cm_empty, cm_empty, map_one, mul_one]
  · rw [hc_apply, hc_apply, top_coeff, top_coeff, det_mat, det_mat, map_one, mul_one]

/- the rank argument -/

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

theorem main_iff {K : Type} [Field K] {P : Type} [Fintype P] {ι : Type} [Fintype ι]
    [DecidableEq ι] (d : ℕ) (fx : P → P → K)
    (u w : P → ι → K)
    (hfix : ∀ p r : P, fx p r = ∑ a, u p a * w r a)
    (hu : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0)
    (hw : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * w p β = if β = a then 1 else 0) :
    (∃ (A B : P → Fin d → K), ∀ p r, fx p r = ∑ j : Fin d, A p j * B r j) ↔
      Fintype.card ι ≤ d := by
  constructor
  · rintro ⟨A, B, h⟩
    choose c hc using hu
    choose e he using hw
    have hM : (Matrix.of fun (a : ι) (j : Fin d) => ∑ p, c a p * A p j) *
        (Matrix.of fun (j : Fin d) (β : ι) => ∑ r, e β r * B r j) = 1 := by
      ext a β
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      calc ∑ j, (∑ p, c a p * A p j) * (∑ r, e β r * B r j)
          = ∑ p, ∑ r, c a p * e β r * ∑ j, A p j * B r j := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
        _ = ∑ p, ∑ r, c a p * e β r * ∑ g, u p g * w r g := by
            simp_rw [← h, hfix]
        _ = ∑ g, (∑ p, c a p * u p g) * (∑ r, e β r * w r g) := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            calc ∑ p, ∑ r, ∑ g, c a p * e β r * (u p g * w r g)
                = ∑ p, ∑ g, ∑ r, c a p * e β r * (u p g * w r g) :=
                  Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
              _ = ∑ g, ∑ p, ∑ r, c a p * e β r * (u p g * w r g) := Finset.sum_comm
              _ = _ := by
                  refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun p _ =>
                    Finset.sum_congr rfl (fun r _ => ?_)))
                  ring
        _ = if a = β then 1 else 0 := by
            simp_rw [hc, he]
            simp [eq_comm]
    exact rank_bound d _ _ hM
  · intro hd
    obtain ⟨A, B, hAB⟩ := pad (K := K) d hd u w
    exact ⟨A, B, fun p r => by rw [hfix, hAB]⟩

theorem toFun {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K)
    (a : ι) (h : (Pi.single a 1 : ι → K) ∈ Submodule.span K (Set.range u)) :
    ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 h
  refine ⟨c, fun β => ?_⟩
  have := congrFun hc β
  simpa [Finset.sum_apply, Pi.single_apply] using this

theorem transfer {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K)
    (σ : ι ≃ ι) (h : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0) :
    ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p (σ β) = if β = a then 1 else 0 := by
  intro a
  obtain ⟨c, hc⟩ := h (σ a)
  exact ⟨c, fun β => by rw [hc]; simp [σ.injective.eq_iff]⟩

def piM (K : Type) [Field K] (n : ℕ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K →ₗ[K] (Ix n → K) where
  toFun M a := M a.1.2 a.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem span_u (K : Type) [Field K] [CharP K 2] {n : ℕ} (a : Ix n) :
    (Pi.single a 1 : Ix n → K) ∈ Submodule.span K (Set.range
      (fun p : (VV n ≃ₗ[ZMod 2] VV n) × VV n => fun b : Ix n => hc K (mat p.1) b.1.2 b.1.1)) := by
  obtain ⟨⟨S0, T⟩, hc0, hpos, hlt⟩ := a
  have h1 : S0.Nonempty := Finset.card_pos.1 hpos
  have h2 : S0ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    simp only at hlt
    omega
  have hE := unit_mem K S0 T h1 h2 hc0
  have hpi : piM K n (Matrix.of fun U S => if U = T ∧ S = S0 then (1 : K) else 0) =
      Pi.single ⟨(S0, T), hc0, hpos, hlt⟩ 1 := by
    funext b
    obtain ⟨⟨S', T'⟩, hb⟩ := b
    show (if T' = T ∧ S' = S0 then (1 : K) else 0) = _
    rw [Pi.single_apply]
    by_cases hS : S' = S0 <;> by_cases hT : T' = T
    · subst hS
      subst hT
      simp
    · simp [hT]
    · simp [hS]
    · simp [hS]
  rw [← hpi]
  have hle : Submodule.map (piM K n) (Alg K n) ≤ Submodule.span K (Set.range
      (fun p : (VV n ≃ₗ[ZMod 2] VV n) × VV n => fun b : Ix n => hc K (mat p.1) b.1.2 b.1.1)) := by
    rw [Alg, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g, 0), rfl⟩
  exact hle (Submodule.mem_map_of_mem hE)

def sw (n : ℕ) : Ix n ≃ Ix n where
  toFun a := ⟨(a.1.2, a.1.1), a.2.1.symm, by rw [← a.2.1]; exact a.2.2.1,
    by rw [← a.2.1]; exact a.2.2.2⟩
  invFun a := ⟨(a.1.2, a.1.1), a.2.1.symm, by rw [← a.2.1]; exact a.2.2.1,
    by rw [← a.2.1]; exact a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem main (K : Type) [Field K] [CharP K 2] (n d : ℕ) (hn : 0 < n) :
    (∃ (A B : ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) × (Fin n → ZMod 2) → Fin d → K),
      ∀ p r, ((((Finset.univ : Finset (Fin n → ZMod 2)).filter
        (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card : ℕ) : K) = ∑ j : Fin d, A p j * B r j) ↔
      Nat.choose (2 * n) n - 2 ≤ d := by
  have : Finite ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    Finite.of_injective (fun g => (g : (Fin n → ZMod 2) → (Fin n → ZMod 2)))
      (fun g h e => LinearEquiv.ext (congrFun e))
  let _ := Fintype.ofFinite ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
  rw [← card_Ix hn]
  exact main_iff d _ (fun p a => hc K (mat p.1) a.1.2 a.1.1)
    (fun r a => hc K (mat r.1) a.1.1 a.1.2) (fun p r => fix_formula K hn p r)
    (fun a => toFun _ a (span_u K a)) (transfer _ (sw n) (fun a => toFun _ a (span_u K a)))

end

end PEqualNP.Outside.L_lib_615

open PEqualNP.Outside.L_lib_615 in
theorem PEqualNP.Outside.L_lib_615 : ∀ (K : Type) [Field K] [CharP K 2] (b d : ℕ),
  let w := b + 1
  let V := Fin w → ZMod 2
  let P := (V ≃ₗ[ZMod 2] V) × V
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset V).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    Nat.choose (2 * w) w - 2 ≤ d := by
  intro K _ _ b d
  dsimp only
  exact main K (b + 1) d (Nat.succ_pos b)
