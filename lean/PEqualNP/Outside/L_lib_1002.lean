import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1002_aux

open Classical
noncomputable section

section BasicHelpers

variable {K : Type} [Field K]

lemma finrank_range_add_le {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f g : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (f + g)) ≤
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
  have hle : LinearMap.range (f + g) ≤ LinearMap.range f ⊔ LinearMap.range g := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  have hmono := Submodule.finrank_mono hle
  omega

lemma finrank_range_sum_le {ι V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (s : Finset ι) (f : ι → V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (∑ i ∈ s, f i)) ≤
      ∑ i ∈ s, Module.finrank K (LinearMap.range (f i)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have hbot : LinearMap.range (0 : V →ₗ[K] W) = ⊥ := by ext x; simp
    rw [hbot, finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (finrank_range_add_le (f a) (∑ i ∈ s, f i)).trans (Nat.add_le_add_left ih _)

lemma matrix_rank_sum_le {ι m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (s : Finset ι) (M : ι → Matrix m n K) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  have hlin : (∑ i ∈ s, M i).mulVecLin = ∑ i ∈ s, (M i).mulVecLin := by
    induction s using Finset.induction_on with
    | empty =>
      apply LinearMap.ext; intro x; ext a; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      apply LinearMap.ext; intro x; ext b
      simp
  rw [Matrix.rank]
  exact (congrArg (fun L => Module.finrank K (LinearMap.range L)) hlin).le.trans
    (finrank_range_sum_le s (fun i => (M i).mulVecLin))

lemma matrix_factor_of_rank_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {q : ℕ} (A : Matrix m n K) (hA : A.rank ≤ q) :
    ∃ (U : Matrix m (Fin q) K) (V : Matrix (Fin q) n K), U * V = A := by
  let R := LinearMap.range A.mulVecLin
  let d := Module.finrank K R
  have hd : d ≤ q := hA
  let e : R ≃ₗ[K] (Fin d → K) := (Module.finBasis K R).equivFun
  let pad : (Fin d → K) →ₗ[K] (Fin q → K) :=
    { toFun := fun v j => if hj : j.val < d then v ⟨j.val, hj⟩ else 0
      map_add' := fun u v => by ext j; by_cases hj : j.val < d <;> simp [hj]
      map_smul' := fun c v => by ext j; by_cases hj : j.val < d <;> simp [hj] }
  let proj : (Fin q → K) →ₗ[K] (Fin d → K) :=
    { toFun := fun v j => v ⟨j.val, lt_of_lt_of_le j.isLt hd⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hproj_pad : proj.comp pad = LinearMap.id := by
    ext v j
    simp [proj, pad, j.isLt]
  let Ulin : (Fin q → K) →ₗ[K] (m → K) := R.subtype.comp (e.symm.toLinearMap.comp proj)
  let Vlin : (n → K) →ₗ[K] (Fin q → K) := pad.comp (e.toLinearMap.comp A.mulVecLin.rangeRestrict)
  have hcomp : Ulin.comp Vlin = A.mulVecLin := by
    apply LinearMap.ext
    intro x
    ext a
    change (R.subtype (e.symm (proj (pad (e (A.mulVecLin.rangeRestrict x)))))) a = A.mulVecLin x a
    have hp : proj (pad (e (A.mulVecLin.rangeRestrict x))) = e (A.mulVecLin.rangeRestrict x) :=
      congrFun (congrArg DFunLike.coe hproj_pad) _
    rw [hp, e.symm_apply_apply]
    rfl
  refine ⟨LinearMap.toMatrix' Ulin, LinearMap.toMatrix' Vlin, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  exact hcomp

lemma exists_common_complement {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (X Y : Submodule K V) (hdim : Module.finrank K X = Module.finrank K Y) :
    ∃ B : Submodule K V, IsCompl X B ∧ IsCompl Y B := by
  let I : Submodule K V := X ⊓ Y

  let IX : Submodule K X := I.comap X.subtype
  obtain ⟨X'sub, hX'compl⟩ := Submodule.exists_isCompl IX
  let X' : Submodule K V := X'sub.map X.subtype
  have hIX_disj : Disjoint I X' := by
    rw [Submodule.disjoint_def]
    intro v hvI hvX'
    obtain ⟨x, hxX', rfl⟩ := hvX'
    have hxIX : x ∈ IX := hvI
    have hx0 : x = 0 := Submodule.disjoint_def.mp hX'compl.disjoint x hxIX hxX'
    simp [hx0]
  have hIX_sup : I ⊔ X' = X := by
    apply le_antisymm
    · exact sup_le inf_le_left (by rintro _ ⟨x, _, rfl⟩; exact x.2)
    · intro v hvX
      have htop : (⟨v, hvX⟩ : X) ∈ IX ⊔ X'sub := by rw [hX'compl.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
      have hveq : v = a.1 + b.1 := (congrArg Subtype.val hab).symm
      rw [hveq]
      exact Submodule.add_mem_sup ha ⟨b, hb, rfl⟩
  let IY : Submodule K Y := I.comap Y.subtype
  obtain ⟨Y'sub, hY'compl⟩ := Submodule.exists_isCompl IY
  let Y' : Submodule K V := Y'sub.map Y.subtype
  have hIY_disj : Disjoint I Y' := by
    rw [Submodule.disjoint_def]
    intro v hvI hvY'
    obtain ⟨y, hyY', rfl⟩ := hvY'
    have hyIY : y ∈ IY := hvI
    have hy0 : y = 0 := Submodule.disjoint_def.mp hY'compl.disjoint y hyIY hyY'
    simp [hy0]
  have hIY_sup : I ⊔ Y' = Y := by
    apply le_antisymm
    · exact sup_le inf_le_right (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    · intro v hvY
      have htop : (⟨v, hvY⟩ : Y) ∈ IY ⊔ Y'sub := by rw [hY'compl.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
      have hveq : v = a.1 + b.1 := (congrArg Subtype.val hab).symm
      rw [hveq]
      exact Submodule.add_mem_sup ha ⟨b, hb, rfl⟩
  have hXY'_disj : Disjoint X Y' := by
    rw [Submodule.disjoint_def]
    intro v hvX hvY'
    have hvY : v ∈ Y := by rw [← hIY_sup]; exact Submodule.mem_sup_right hvY'
    exact Submodule.disjoint_def.mp hIY_disj v ⟨hvX, hvY⟩ hvY'
  have hYX'_disj : Disjoint Y X' := by
    rw [Submodule.disjoint_def]
    intro v hvY hvX'
    have hvX : v ∈ X := by rw [← hIX_sup]; exact Submodule.mem_sup_right hvX'
    exact Submodule.disjoint_def.mp hIX_disj v ⟨hvX, hvY⟩ hvX'
  have hfr_eq : Module.finrank K X' = Module.finrank K Y' := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I X'
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq I Y'
    rw [hIX_sup, hIX_disj.eq_bot, finrank_bot, add_zero] at h1
    rw [hIY_sup, hIY_disj.eq_bot, finrank_bot, add_zero] at h2
    omega

  let q := Module.finrank K X'
  let bX := Module.finBasis K X'
  let bY := Module.finBasisOfFinrankEq K Y' hfr_eq.symm
  let φ : X' ≃ₗ[K] Y' := bX.equiv bY (Equiv.refl (Fin q))

  let diagMap : X' →ₗ[K] V := X'.subtype + Y'.subtype.comp φ.toLinearMap
  let D : Submodule K V := LinearMap.range diagMap
  have hdiag_inj : Function.Injective diagMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hsum : (x : V) + (φ x : V) = 0 := hx
    have heq : (x : V) = - (φ x : V) := eq_neg_of_add_eq_zero_left hsum
    have hxX : (x : V) ∈ X := by rw [← hIX_sup]; exact Submodule.mem_sup_right x.2
    have hxY' : (x : V) ∈ Y' := by rw [heq]; exact Y'.neg_mem (φ x).2
    have hx0 : (x : V) = 0 := Submodule.disjoint_def.mp hXY'_disj (x : V) hxX hxY'
    exact Subtype.ext hx0
  have hfrD : Module.finrank K D = q := by
    have h1 := (Submodule.equivMapOfInjective diagMap hdiag_inj ⊤).finrank_eq
    have hrange : (⊤ : Submodule K X').map diagMap = D := Submodule.map_top diagMap
    rw [hrange, finrank_top] at h1
    exact h1.symm

  obtain ⟨Z, hZcompl⟩ := Submodule.exists_isCompl (X ⊔ Y')
  have hXY_eq : X ⊔ Y' = Y ⊔ X' := by
    rw [← hIX_sup, ← hIY_sup]
    ac_rfl
  let B : Submodule K V := D ⊔ Z
  have hD_le : D ≤ X ⊔ Y' := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup (by rw [← hIX_sup]; exact Submodule.mem_sup_right x.2) (φ x).2
  have hDZ_disj : Disjoint D Z := hZcompl.disjoint.mono_left hD_le
  have hXB_disj : Disjoint X B := by
    rw [Submodule.disjoint_def]
    intro v hvX hvB
    obtain ⟨d, hdD, z, hzZ, rfl⟩ := Submodule.mem_sup.mp hvB
    have hz_in : z ∈ X ⊔ Y' := by
      have h1 : d + z ∈ X ⊔ Y' := Submodule.mem_sup_left hvX
      have h2 : d ∈ X ⊔ Y' := hD_le hdD
      have : z = (d + z) - d := by abel
      rw [this]
      exact (X ⊔ Y').sub_mem h1 h2
    have hz0 : z = 0 := Submodule.disjoint_def.mp hZcompl.disjoint z hz_in hzZ
    rw [hz0, add_zero] at hvX ⊢
    obtain ⟨x, rfl⟩ := hdD
    change (x : V) + (φ x : V) ∈ X at hvX
    have hxX : (x : V) ∈ X := by rw [← hIX_sup]; exact Submodule.mem_sup_right x.2
    have hφX : (φ x : V) ∈ X := by
      have : (φ x : V) = ((x : V) + (φ x : V)) - (x : V) := by abel
      rw [this]
      exact X.sub_mem hvX hxX
    have hφ0 : (φ x : V) = 0 := Submodule.disjoint_def.mp hXY'_disj _ hφX (φ x).2
    have hφ0' : φ x = 0 := Subtype.ext hφ0
    have hx0 : x = 0 := φ.injective (hφ0'.trans (map_zero φ).symm)
    simp [diagMap, hx0]
  have hYB_disj : Disjoint Y B := by
    rw [Submodule.disjoint_def]
    intro v hvY hvB
    obtain ⟨d, hdD, z, hzZ, rfl⟩ := Submodule.mem_sup.mp hvB
    have hz_in : z ∈ X ⊔ Y' := by
      have h1 : d + z ∈ X ⊔ Y' := by rw [hXY_eq]; exact Submodule.mem_sup_left hvY
      have h2 : d ∈ X ⊔ Y' := hD_le hdD
      have : z = (d + z) - d := by abel
      rw [this]
      exact (X ⊔ Y').sub_mem h1 h2
    have hz0 : z = 0 := Submodule.disjoint_def.mp hZcompl.disjoint z hz_in hzZ
    rw [hz0, add_zero] at hvY ⊢
    obtain ⟨x, rfl⟩ := hdD
    change (x : V) + (φ x : V) ∈ Y at hvY
    have hφY : (φ x : V) ∈ Y := by rw [← hIY_sup]; exact Submodule.mem_sup_right (φ x).2
    have hxY : (x : V) ∈ Y := by
      have : (x : V) = ((x : V) + (φ x : V)) - (φ x : V) := by abel
      rw [this]
      exact Y.sub_mem hvY hφY
    have hx0 : (x : V) = 0 := Submodule.disjoint_def.mp hYX'_disj _ hxY x.2
    have hx0' : x = 0 := Subtype.ext hx0
    simp [diagMap, hx0']
  have hfrB : Module.finrank K X + Module.finrank K B = Module.finrank K V := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq D Z
    rw [hDZ_disj.eq_bot, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (X ⊔ Y') Z
    rw [hZcompl.sup_eq_top, hZcompl.disjoint.eq_bot, finrank_top, finrank_bot, add_zero] at h2
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq X Y'
    rw [hXY'_disj.eq_bot, finrank_bot, add_zero] at h3
    change Module.finrank K X + Module.finrank K (D ⊔ Z : Submodule K V) = Module.finrank K V
    omega
  have hXB_sup : X ⊔ B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq X B
    rw [hXB_disj.eq_bot, finrank_bot, add_zero] at h1
    omega
  have hYB_sup : Y ⊔ B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y B
    rw [hYB_disj.eq_bot, finrank_bot, add_zero] at h1
    omega
  exact ⟨B, ⟨hXB_disj, codisjoint_iff.mpr hXB_sup⟩, ⟨hYB_disj, codisjoint_iff.mpr hYB_sup⟩⟩

lemma exists_common_complement_containing {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (Fix X Y : Submodule K V) (hFX : Disjoint Fix X) (hFY : Disjoint Fix Y)
    (hdim : Module.finrank K X = Module.finrank K Y) :
    ∃ B : Submodule K V, Fix ≤ B ∧ IsCompl X B ∧ IsCompl Y B := by
  let q := Fix.mkQ
  have hfrX : Module.finrank K (X.map q) = Module.finrank K X := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (q.domRestrict X)
    have hker : LinearMap.ker (q.domRestrict X) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hxF : (x : V) ∈ Fix := (Submodule.Quotient.mk_eq_zero Fix).mp hx
      exact Subtype.ext (Submodule.disjoint_def.mp hFX _ hxF x.2)
    have hrange : LinearMap.range (q.domRestrict X) = X.map q := by
      ext v; simp [Submodule.mem_map]
    rw [hker, finrank_bot, add_zero, hrange] at hrn
    exact hrn
  have hfrY : Module.finrank K (Y.map q) = Module.finrank K Y := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (q.domRestrict Y)
    have hker : LinearMap.ker (q.domRestrict Y) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker] at hy
      have hyF : (y : V) ∈ Fix := (Submodule.Quotient.mk_eq_zero Fix).mp hy
      exact Subtype.ext (Submodule.disjoint_def.mp hFY _ hyF y.2)
    have hrange : LinearMap.range (q.domRestrict Y) = Y.map q := by
      ext v; simp [Submodule.mem_map]
    rw [hker, finrank_bot, add_zero, hrange] at hrn
    exact hrn
  obtain ⟨Bq, hXq, hYq⟩ := exists_common_complement (X.map q) (Y.map q) (by omega)
  let B : Submodule K V := Bq.comap q
  have hFixB : Fix ≤ B := by
    intro v hv
    change q v ∈ Bq
    have : q v = 0 := (Submodule.Quotient.mk_eq_zero Fix).mpr hv
    rw [this]
    exact Bq.zero_mem
  have hlift : ∀ (U : Submodule K V), Disjoint Fix U → IsCompl (U.map q) Bq → IsCompl U B := by
    intro U hFU hUq
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvU hvB
      have hqv0 : q v = 0 := Submodule.disjoint_def.mp hUq.disjoint (q v)
        (Submodule.mem_map_of_mem hvU) hvB
      have hvF : v ∈ Fix := (Submodule.Quotient.mk_eq_zero Fix).mp hqv0
      exact Submodule.disjoint_def.mp hFU v hvF hvU
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have htop : q v ∈ U.map q ⊔ Bq := by rw [hUq.sup_eq_top]; trivial
      obtain ⟨_, ⟨u, huU, rfl⟩, b, hbB, hub⟩ := Submodule.mem_sup.mp htop
      have hvu : v - u ∈ B := by
        change q (v - u) ∈ Bq
        rw [map_sub]
        have : q v - q u = b := by rw [← hub]; abel
        rw [this]
        exact hbB
      have : v = u + (v - u) := by abel
      rw [this]
      exact Submodule.add_mem_sup huU hvu
  exact ⟨B, hFixB, hlift X hFX hXq, hlift Y hFY hYq⟩

lemma proj_of_isCompl {V : Type*} [AddCommGroup V] [Module K V]
    {A B : Submodule K V} (hAB : IsCompl A B) :
    ∃ π : V →ₗ[K] V, (∀ a ∈ A, π a = a) ∧ (∀ b ∈ B, π b = 0) ∧
      LinearMap.range π = A := by
  let p : V →ₗ[K] A := Submodule.projectionOnto A B hAB
  refine ⟨A.subtype.comp p, ?_, ?_, ?_⟩
  · intro a ha
    change (p a : V) = a
    have := Submodule.projectionOnto_apply_left hAB ⟨a, ha⟩
    exact congrArg Subtype.val this
  · intro b hb
    change (p b : V) = 0
    have := Submodule.projectionOnto_apply_right hAB ⟨b, hb⟩
    simp [p, this]
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩; exact (p v).2
    · intro a ha
      refine ⟨a, ?_⟩
      change (p a : V) = a
      exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hAB ⟨a, ha⟩)

end BasicHelpers

section PathConstruction

variable {K : Type} [Field K]

lemma invertible_rank1_path {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V] :
    ∀ (d' : ℕ) (T : V →ₗ[K] V),
      LinearMap.ker T = ⊥ →
      Module.finrank K (LinearMap.range (LinearMap.id - T)) ≤ d' →
      ∃ G : Fin d' → (V →ₗ[K] V),
        (∀ i, Module.finrank K (LinearMap.range (G i)) ≤ 1) ∧
        T + ∑ i : Fin d', G i = LinearMap.id ∧
        (∀ p : ℕ, p ≤ d' →
          LinearMap.ker (T + ∑ i ∈ Finset.univ.filter (fun i : Fin d' => i.val < p), G i) = ⊥) := by
  intro d'
  induction d' with
  | zero =>
    intro T hker hle
    let D : V →ₗ[K] V := LinearMap.id - T
    have hbot : LinearMap.range D = ⊥ :=
      Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
    have hTeq : T = LinearMap.id := by
      ext v
      have h0 : D v = 0 := by
        have hmem : D v ∈ LinearMap.range D := ⟨v, rfl⟩
        rwa [hbot, Submodule.mem_bot] at hmem
      have : v - T v = 0 := h0
      exact (sub_eq_zero.mp this).symm
    refine ⟨Fin.elim0, fun i => i.elim0, by simp [hTeq], fun p _ => by simp [hTeq]⟩
  | succ d'' ih =>
    intro T hker hle
    let D : V →ₗ[K] V := LinearMap.id - T
    by_cases hle' : Module.finrank K (LinearMap.range D) ≤ d''
    · obtain ⟨G', hG1, hGsum, hGinv⟩ := ih T hker hle'
      let G : Fin (d'' + 1) → (V →ₗ[K] V) := fun i =>
        if hi : i.val < d'' then G' ⟨i.val, hi⟩ else 0
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i.val < d''
        · have hGi : G i = G' ⟨i.val, hi⟩ := dite_eq_left hi
          rw [hGi]
          exact hG1 _
        · have hGi : G i = 0 := dite_eq_right hi
          rw [hGi]
          have hbot : LinearMap.range (0 : V →ₗ[K] V) = ⊥ := by ext x; simp
          rw [hbot, finrank_bot]
          omega
      · rw [Fin.sum_univ_castSucc]
        have hlast : G (Fin.last d'') = 0 := dite_eq_right (by simp)
        have hcast : ∀ j : Fin d'', G j.castSucc = G' j := fun j => dite_eq_left j.isLt
        simp only [hlast, hcast, add_zero]
        exact hGsum
      · intro p hp
        by_cases hp' : p ≤ d''
        · have hsum_eq : (∑ i ∈ Finset.univ.filter (fun i : Fin (d'' + 1) => i.val < p), G i) =
              ∑ i ∈ Finset.univ.filter (fun i : Fin d'' => i.val < p), G' i := by
            refine Finset.sum_bij (fun i hi => ⟨i.val, by
              have := (Finset.mem_filter.mp hi).2; omega⟩)
              (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
              (fun i₁ _ i₂ _ h => Fin.ext (congrArg (fun x : Fin d'' => x.val) h))
              (fun j hj => ⟨j.castSucc, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, by ext; rfl⟩)
              (fun i hi => by
                have hlt : i.val < d'' := by have := (Finset.mem_filter.mp hi).2; omega
                exact dite_eq_left hlt)
          rw [hsum_eq]
          exact hGinv p hp'
        · have hpeq : p = d'' + 1 := by omega
          subst hpeq
          have hall : Finset.univ.filter (fun i : Fin (d'' + 1) => i.val < d'' + 1) = Finset.univ := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact i.isLt
          rw [hall, Fin.sum_univ_castSucc]
          have hlast : G (Fin.last d'') = 0 := dite_eq_right (by simp)
          have hcast : ∀ j : Fin d'', G j.castSucc = G' j := fun j => dite_eq_left j.isLt
          simp only [hlast, hcast, add_zero, hGsum, LinearMap.ker_id]
    ·
      have hpos : 0 < Module.finrank K (LinearMap.range D) := by omega
      have hne_bot : LinearMap.range D ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hpos; omega
      have hex_v : ∃ v : V, D v ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne_bot
        rw [Submodule.eq_bot_iff]
        rintro _ ⟨v, rfl⟩
        exact hall v
      obtain ⟨v, hv⟩ := hex_v

      have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
      have hTbij : Function.Bijective T := ⟨hTinj, LinearMap.injective_iff_surjective.mp hTinj⟩
      let eT : V ≃ₗ[K] V := LinearEquiv.ofBijective T hTbij
      let w : V := eT.symm v
      have hTw : T w = v := eT.apply_symm_apply v
      let Fix : Submodule K V := LinearMap.ker D
      have hv_notFix : v ∉ Fix := by
        intro hmem; exact hv hmem
      have hw_notFix : w ∉ Fix := by
        intro hmem
        have h1 : w - T w = 0 := hmem
        have h2 : w = v := by rw [← hTw]; exact sub_eq_zero.mp h1
        exact hv_notFix (h2 ▸ hmem)
      let X : Submodule K V := Submodule.span K {v}
      let Y : Submodule K V := Submodule.span K {w}
      have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
      have hw0 : w ≠ 0 := fun h0 => hv0 (by rw [← hTw, h0, map_zero])
      have hFX : Disjoint Fix X := by
        rw [Submodule.disjoint_def]
        intro x hxF hxX
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxX
        by_cases hc : c = 0
        · simp [hc]
        · exfalso
          have : v ∈ Fix := by
            have := Fix.smul_mem c⁻¹ hxF
            rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
          exact hv_notFix this
      have hFY : Disjoint Fix Y := by
        rw [Submodule.disjoint_def]
        intro x hxF hxY
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxY
        by_cases hc : c = 0
        · simp [hc]
        · exfalso
          have : w ∈ Fix := by
            have := Fix.smul_mem c⁻¹ hxF
            rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
          exact hw_notFix this
      have hdimXY : Module.finrank K X = Module.finrank K Y := by
        rw [finrank_span_singleton hv0, finrank_span_singleton hw0]
      obtain ⟨B, hFixB, hXB, hYB⟩ := exists_common_complement_containing Fix X Y hFX hFY hdimXY
      obtain ⟨π, hπX, hπB, hπrange⟩ := proj_of_isCompl hXB
      let G0 : V →ₗ[K] V := D.comp π
      let T' : V →ₗ[K] V := T + G0
      have hG0_rank : Module.finrank K (LinearMap.range G0) ≤ 1 := by
        have hleG0 : LinearMap.range G0 ≤ Submodule.span K {D v} := by
          rintro _ ⟨u, rfl⟩
          have hmem : π u ∈ X := by rw [← hπrange]; exact ⟨u, rfl⟩
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
          change D (π u) ∈ _
          rw [← hc, map_smul]
          exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
        calc Module.finrank K (LinearMap.range G0)
            ≤ Module.finrank K (Submodule.span K {D v}) :=
              Submodule.finrank_mono hleG0
          _ = 1 := finrank_span_singleton hv
      have hT'_ker : LinearMap.ker T' = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        have hx_split : x ∈ X ⊔ B := by rw [hXB.sup_eq_top]; trivial
        obtain ⟨a, haX, b, hbB, rfl⟩ := Submodule.mem_sup.mp hx_split
        have hTx : T' (a + b) = a + T b := by
          simp only [T', G0, D, LinearMap.add_apply, LinearMap.comp_apply, map_add,
            hπX a haX, hπB b hbB, add_zero, LinearMap.sub_apply, LinearMap.id_apply, map_zero]
          abel
        rw [LinearMap.mem_ker, hTx] at hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp haX
        have hTbw : T (c • w + b) = 0 := by
          rw [map_add, map_smul, hTw]
          exact hx
        have hcb0 : c • w + b = 0 := hTinj (by rw [hTbw, map_zero])
        have hcw_eq : c • w = -b := eq_neg_of_add_eq_zero_left hcb0
        have hcwY : c • w ∈ Y := Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
        have hcwB : c • w ∈ B := by rw [hcw_eq]; exact B.neg_mem hbB
        have hcw0 : c • w = 0 := Submodule.disjoint_def.mp hYB.disjoint _ hcwY hcwB
        have hc0 : c = 0 := by
          rcases smul_eq_zero.mp hcw0 with hc | hwz
          · exact hc
          · exact (hw0 hwz).elim
        rw [hc0, zero_smul, zero_add] at hcb0 ⊢
        exact hcb0
      have hT'_rank : Module.finrank K (LinearMap.range (LinearMap.id - T')) ≤ d'' := by
        have hker_le : Fix ⊔ X ≤ LinearMap.ker (LinearMap.id - T') := by
          refine sup_le ?_ ?_
          · intro x hxF
            rw [LinearMap.mem_ker]
            have hxB : x ∈ B := hFixB hxF
            have hx0 : D x = 0 := hxF
            simp only [T', G0, D, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
              hπB x hxB, map_zero, add_zero] at hx0 ⊢
            exact hx0
          · intro x hxX
            rw [LinearMap.mem_ker]
            simp only [T', G0, D, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
              hπX x hxX, LinearMap.id_apply]
            abel
        have hfr_sup := Submodule.finrank_sup_add_finrank_inf_eq Fix X
        rw [hFX.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0] at hfr_sup
        have hrn1 := LinearMap.finrank_range_add_finrank_ker D
        have hrn2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - T')
        have hmono : Module.finrank K (Fix ⊔ X : Submodule K V) ≤
            Module.finrank K (LinearMap.ker (LinearMap.id - T')) := Submodule.finrank_mono hker_le
        have hFix_eq : Module.finrank K Fix = Module.finrank K (LinearMap.ker D) := rfl
        have hD_eq : Module.finrank K (LinearMap.range D) =
            Module.finrank K (LinearMap.range (LinearMap.id - T)) := rfl
        omega
      obtain ⟨G', hG'1, hG'sum, hG'inv⟩ := ih T' hT'_ker hT'_rank
      let G : Fin (d'' + 1) → (V →ₗ[K] V) := Fin.cons G0 G'
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact hG0_rank
        · intro j; exact hG'1 j
      · rw [Fin.sum_univ_succ]
        simp only [G, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
        exact hG'sum
      · intro p hp
        cases p with
        | zero =>
          have hemp : Finset.univ.filter (fun i : Fin (d'' + 1) => i.val < 0) = ∅ := by ext i; simp
          rw [hemp, Finset.sum_empty, add_zero]
          exact hker
        | succ p' =>
          have hsum_eq : (∑ i ∈ Finset.univ.filter (fun i : Fin (d'' + 1) => i.val < p' + 1), G i) =
              G0 + ∑ j ∈ Finset.univ.filter (fun j : Fin d'' => j.val < p'), G' j := by
            have h0 : (0 : Fin (d'' + 1)) ∈
                Finset.univ.filter (fun i : Fin (d'' + 1) => i.val < p' + 1) := by simp
            rw [← Finset.add_sum_erase _ _ h0]
            congr 1
            refine Finset.sum_bij (fun i hi =>
                ⟨i.val - 1, by
                  have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
                  have hpos' : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
                  have h1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
                  omega⟩)
              (fun i hi => by
                have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
                have h1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
                have hpos' : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩)
              (fun i₁ hi₁ i₂ hi₂ heq => by
                have hne1 : i₁ ≠ 0 := (Finset.mem_erase.mp hi₁).1
                have hne2 : i₂ ≠ 0 := (Finset.mem_erase.mp hi₂).1
                have hp1 : 0 < i₁.val := Nat.pos_of_ne_zero (fun h0 => hne1 (Fin.ext h0))
                have hp2 : 0 < i₂.val := Nat.pos_of_ne_zero (fun h0 => hne2 (Fin.ext h0))
                have hv := congrArg (fun x : Fin d'' => x.val) heq
                dsimp only at hv
                exact Fin.ext (by omega))
              (fun j hj => ⟨j.succ, Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  have := (Finset.mem_filter.mp hj).2; simp only [Fin.val_succ]; omega⟩⟩, by ext; simp⟩)
              (fun i hi => by
                have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
                have hp1 : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
                have h1 := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
                have hi_eq : i = (⟨i.val - 1, by omega⟩ : Fin d'').succ := Fin.ext (by simp; omega)
                conv_lhs => rw [hi_eq]
                simp only [G, Fin.cons_succ])
          rw [hsum_eq, ← add_assoc]
          exact hG'inv p' (by omega)

lemma rank_path_invertible {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (T : V →ₗ[K] V) :
    let m := Module.finrank K (LinearMap.ker T)
    let d := Module.finrank K (LinearMap.range (LinearMap.id - T))
    m ≤ d ∧
    ∃ E : Fin d → (V →ₗ[K] V),
      (∀ i, Module.finrank K (LinearMap.range (E i)) ≤ 1) ∧
      T + ∑ i : Fin d, E i = LinearMap.id ∧
      (∀ p : ℕ, m ≤ p → p ≤ d →
        LinearMap.ker (T + ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < p), E i) = ⊥) := by
  intro m d
  have hker_le_range : LinearMap.ker T ≤ LinearMap.range (LinearMap.id - T) := by
    intro x hx
    refine ⟨x, ?_⟩
    simp [LinearMap.mem_ker.mp hx]
  have hm_le_d : m ≤ d := Submodule.finrank_mono hker_le_range
  refine ⟨hm_le_d, ?_⟩
  let Fix : Submodule K V := LinearMap.ker (LinearMap.id - T)

  obtain ⟨A, hRA⟩ := Submodule.exists_isCompl (LinearMap.range T)
  have hfrA : Module.finrank K A = m := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range T) A
    rw [hRA.sup_eq_top, hRA.disjoint.eq_bot, finrank_top, finrank_bot, add_zero] at h1
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    omega
  have hFix_le_R : Fix ≤ LinearMap.range T := by
    intro x hx
    refine ⟨x, ?_⟩
    have : x - T x = 0 := hx
    exact (sub_eq_zero.mp this).symm
  have hFA : Disjoint Fix A := hRA.disjoint.mono_left hFix_le_R
  have hFK : Disjoint Fix (LinearMap.ker T) := by
    rw [Submodule.disjoint_def]
    intro x hxF hxK
    have h1 : x - T x = 0 := hxF
    rw [LinearMap.mem_ker.mp hxK, sub_zero] at h1
    exact h1
  obtain ⟨B, hFixB, hAB, hKB⟩ :=
    exists_common_complement_containing Fix A (LinearMap.ker T) hFA hFK hfrA
  obtain ⟨π, hπA, hπB, hπrange⟩ := proj_of_isCompl hAB
  let F : V →ₗ[K] V := (LinearMap.id - T).comp π
  let Tm : V →ₗ[K] V := T + F
  have hTm_ker : LinearMap.ker Tm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx_split : x ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
    obtain ⟨a, haA, b, hbB, rfl⟩ := Submodule.mem_sup.mp hx_split
    have hTmx : Tm (a + b) = a + T b := by
      simp only [Tm, F, LinearMap.add_apply, LinearMap.comp_apply, map_add,
        hπA a haA, hπB b hbB, add_zero, LinearMap.sub_apply, LinearMap.id_apply, map_zero]
      abel
    rw [LinearMap.mem_ker, hTmx] at hx
    have ha_eq : a = -T b := eq_neg_of_add_eq_zero_left hx
    have haR : a ∈ LinearMap.range T := by rw [ha_eq]; exact (LinearMap.range T).neg_mem ⟨b, rfl⟩
    have ha0 : a = 0 := Submodule.disjoint_def.mp hRA.disjoint a haR haA
    rw [ha0, zero_add] at hx ⊢
    exact Submodule.disjoint_def.mp hKB.disjoint b hx hbB
  have hTm_rank : Module.finrank K (LinearMap.range (LinearMap.id - Tm)) ≤ d - m := by
    have hker_le : Fix ⊔ A ≤ LinearMap.ker (LinearMap.id - Tm) := by
      refine sup_le ?_ ?_
      · intro x hxF
        rw [LinearMap.mem_ker]
        have hxB : x ∈ B := hFixB hxF
        simp only [Tm, F, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          hπB x hxB, map_zero, add_zero]
        exact hxF
      · intro x hxA
        rw [LinearMap.mem_ker]
        simp only [Tm, F, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          hπA x hxA, LinearMap.id_apply]
        abel
    have hfr_sup := Submodule.finrank_sup_add_finrank_inf_eq Fix A
    rw [hFA.eq_bot, finrank_bot, add_zero, hfrA] at hfr_sup
    have hrn1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - T)
    have hrn2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - Tm)
    have hmono : Module.finrank K (Fix ⊔ A : Submodule K V) ≤
        Module.finrank K (LinearMap.ker (LinearMap.id - Tm)) := Submodule.finrank_mono hker_le
    have hFix_eq : Module.finrank K Fix = Module.finrank K (LinearMap.ker (LinearMap.id - T)) := rfl
    omega

  let D : V →ₗ[K] V := LinearMap.id - T
  let bA := Module.finBasisOfFinrankEq K A hfrA
  let pA : V →ₗ[K] A := Submodule.projectionOnto A B hAB
  let Fpart (i : Fin m) : V →ₗ[K] V :=
    D.comp (LinearMap.smulRight ((bA.coord i).comp pA) (bA i : V))
  have hFpart_rank : ∀ i : Fin m, Module.finrank K (LinearMap.range (Fpart i)) ≤ 1 := by
    intro i
    have hle : LinearMap.range (Fpart i) ≤ Submodule.span K {D (bA i : V)} := by
      rintro _ ⟨v, rfl⟩
      simp only [Fpart, LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    calc Module.finrank K (LinearMap.range (Fpart i))
        ≤ Module.finrank K (Submodule.span K {D (bA i : V)}) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := by
          by_cases h0 : D (bA i : V) = 0
          · rw [h0, Submodule.span_zero_singleton, finrank_bot]; omega
          · rw [finrank_span_singleton h0]
  have hFpart_sum : ∑ i : Fin m, Fpart i = F := by
    ext v
    simp only [LinearMap.sum_apply, Fpart, F, D, LinearMap.comp_apply, LinearMap.smulRight_apply,
      ← map_sum]
    congr 1
    have hdecomp : ∑ i : Fin m, bA.coord i (pA v) • (bA i : V) = (pA v : V) := by
      have h1 := bA.sum_repr (pA v)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.coord_apply] using
        congrArg Subtype.val h1
    rw [hdecomp]

    have hv_split : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
    obtain ⟨a, haA, b, hbB, rfl⟩ := Submodule.mem_sup.mp hv_split
    rw [map_add, map_add, hπA a haA, hπB b hbB, add_zero]
    have h1 := Submodule.projectionOnto_apply_left hAB ⟨a, haA⟩
    have h2 := Submodule.projectionOnto_apply_right hAB ⟨b, hbB⟩
    simp [pA, h1, h2]

  obtain ⟨G, hG1, hGsum, hGinv⟩ := invertible_rank1_path (d - m) Tm hTm_ker hTm_rank
  let E : Fin d → (V →ₗ[K] V) := fun i =>
    if hi : i.val < m then Fpart ⟨i.val, hi⟩
    else G ⟨i.val - m, by omega⟩
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < m
    · have hEi : E i = Fpart ⟨i.val, hi⟩ := dite_eq_left hi
      rw [hEi]
      exact hFpart_rank _
    · have hEi : E i = G ⟨i.val - m, by have := i.isLt; omega⟩ := dite_eq_right hi
      rw [hEi]
      exact hG1 _
  · have hsplit : (∑ i : Fin d, E i) = (∑ i : Fin m, Fpart i) + ∑ j : Fin (d - m), G j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => i.val < m)]
      congr 1
      · refine Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (fun x : Fin m => x.val) h))
          (fun j _ => ⟨⟨j.val, by have := j.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩)
          (fun i hi => by
            have hlt : i.val < m := (Finset.mem_filter.mp hi).2
            exact dite_eq_left hlt)
      · refine Finset.sum_bij (fun i hi => ⟨i.val - m, by
            have hge : ¬ i.val < m := (Finset.mem_filter.mp hi).2
            have := i.isLt; omega⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun i₁ hi₁ i₂ hi₂ h => by
            have h1 : ¬ i₁.val < m := (Finset.mem_filter.mp hi₁).2
            have h2 : ¬ i₂.val < m := (Finset.mem_filter.mp hi₂).2
            have hv := congrArg (fun x : Fin (d - m) => x.val) h
            dsimp only at hv
            exact Fin.ext (by omega))
          (fun j _ => ⟨⟨m + j.val, by have := j.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by ext; simp⟩)
          (fun i hi => by
            have hge : ¬ i.val < m := (Finset.mem_filter.mp hi).2
            exact dite_eq_right hge)
    rw [hsplit, hFpart_sum, ← add_assoc]
    exact hGsum
  · intro p hmp hpd
    have hsplit : (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < p), E i) =
        (∑ i : Fin m, Fpart i) +
        ∑ j ∈ Finset.univ.filter (fun j : Fin (d - m) => j.val < p - m), G j := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun i : Fin d => i.val < p)) (fun i : Fin d => i.val < m)]
      congr 1
      · refine Finset.sum_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (fun x : Fin m => x.val) h))
          (fun j _ => ⟨⟨j.val, by have := j.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have := j.isLt; dsimp only; omega⟩, j.isLt⟩, rfl⟩)
          (fun i hi => by
            have hlt : i.val < m := (Finset.mem_filter.mp hi).2
            exact dite_eq_left hlt)
      · refine Finset.sum_bij (fun i hi => ⟨i.val - m, by
            have hge : ¬ i.val < m := (Finset.mem_filter.mp hi).2
            have := i.isLt; omega⟩)
          (fun i hi => by
            have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
            have h2 : ¬ i.val < m := (Finset.mem_filter.mp hi).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩)
          (fun i₁ hi₁ i₂ hi₂ h => by
            have h1 : ¬ i₁.val < m := (Finset.mem_filter.mp hi₁).2
            have h2 : ¬ i₂.val < m := (Finset.mem_filter.mp hi₂).2
            have hv := congrArg (fun x : Fin (d - m) => x.val) h
            dsimp only at hv
            exact Fin.ext (by omega))
          (fun j hj => ⟨⟨m + j.val, by have := j.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have := (Finset.mem_filter.mp hj).2; dsimp only; omega⟩,
              by dsimp only; omega⟩, by ext; simp⟩)
          (fun i hi => by
            have hge : ¬ i.val < m := (Finset.mem_filter.mp hi).2
            exact dite_eq_right hge)
    rw [hsplit, hFpart_sum, ← add_assoc]
    exact hGinv (p - m) (by omega)

end PathConstruction

section MainTheorem

variable {K : Type} [Field K]

lemma necessity (k r s : ℕ) (H : Matrix (Fin r) (Fin r) K)
    (A : Matrix (Fin (k + 2) × Fin r) (Fin (k + 2) × Fin r) K)
    (hArank : A.rank ≤ r + s)
    (hdiag : ∀ i : Fin (k + 2), A.submatrix (fun a => (i, a)) (fun b => (i, b)) = 1)
    (hsup : ∀ j : Fin (k + 1), A.submatrix (fun a => (j.castSucc, a)) (fun b => (j.succ, b)) = 1)
    (hclose : A.submatrix (fun a => (Fin.last (k + 1), a)) (fun b => (0, b)) = H) :
    r ≤ H.rank + s ∧ (1 - H).rank ≤ (k + 1) * s := by
  obtain ⟨Ubig, Vbig, hUV⟩ := matrix_factor_of_rank_le A hArank
  let U (i : Fin (k + 2)) : Matrix (Fin r) (Fin (r + s)) K :=
    Ubig.submatrix (fun a => (i, a)) id
  let V (j : Fin (k + 2)) : Matrix (Fin (r + s)) (Fin r) K :=
    Vbig.submatrix id (fun b => (j, b))
  have hblock : ∀ i j : Fin (k + 2), U i * V j = A.submatrix (fun a => (i, a)) (fun b => (j, b)) := by
    intro i j
    ext a b
    have h1 := congrFun (congrFun hUV (i, a)) (j, b)
    simpa [U, V, Matrix.mul_apply] using h1
  have hUVdiag : ∀ i : Fin (k + 2), U i * V i = 1 := fun i => (hblock i i).trans (hdiag i)
  have hUVsup : ∀ j : Fin (k + 1), U j.castSucc * V j.succ = 1 :=
    fun j => (hblock j.castSucc j.succ).trans (hsup j)
  have hUVclose : U (Fin.last (k + 1)) * V 0 = H :=
    (hblock (Fin.last (k + 1)) 0).trans hclose
  have hUrank : ∀ i : Fin (k + 2), (U i).rank = r := by
    intro i
    apply le_antisymm
    · calc (U i).rank ≤ Module.finrank K (Fin r → K) := Submodule.finrank_le _
        _ = r := by rw [Module.finrank_pi, Fintype.card_fin]
    · have h1 := Matrix.rank_mul_le_left (U i) (V i)
      rw [hUVdiag i, Matrix.rank_one, Fintype.card_fin] at h1
      exact h1
  have hVrank : ∀ i : Fin (k + 2), (V i).rank = r := by
    intro i
    apply le_antisymm (Matrix.rank_le_width (V i))
    have h1 := Matrix.rank_mul_le_right (U i) (V i)
    rw [hUVdiag i, Matrix.rank_one, Fintype.card_fin] at h1
    exact h1
  constructor
  · have hsyl := Matrix.rank_mul_ge (U (Fin.last (k + 1))) (V 0)
    rw [hUrank, hVrank, hUVclose, Fintype.card_fin] at hsyl
    omega
  · have hkerU : ∀ i : Fin (k + 2), Module.finrank K (LinearMap.ker (U i).mulVecLin) = s := by
      intro i
      have hrn := LinearMap.finrank_range_add_finrank_ker (U i).mulVecLin
      rw [Module.finrank_pi, Fintype.card_fin] at hrn
      have hr : Module.finrank K (LinearMap.range (U i).mulVecLin) = r := hUrank i
      omega
    have hdiff_le : ∀ j : Fin (k + 1), (V j.succ - V j.castSucc).rank ≤ s := by
      intro j
      have hzero : U j.castSucc * (V j.succ - V j.castSucc) = 0 := by
        rw [Matrix.mul_sub, hUVsup j, hUVdiag j.castSucc, sub_self]
      have hsub : LinearMap.range (V j.succ - V j.castSucc).mulVecLin ≤
          LinearMap.ker (U j.castSucc).mulVecLin := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker]
        have h1 : ((U j.castSucc).mulVecLin.comp (V j.succ - V j.castSucc).mulVecLin) x = 0 := by
          rw [← Matrix.mulVecLin_mul, hzero]; simp
        exact h1
      calc (V j.succ - V j.castSucc).rank
          ≤ Module.finrank K (LinearMap.ker (U j.castSucc).mulVecLin) := Submodule.finrank_mono hsub
        _ = s := hkerU j.castSucc
    have htele : V (Fin.last (k + 1)) - V 0 =
        ∑ j : Fin (k + 1), (V j.succ - V j.castSucc) := by
      have hgen : ∀ m : ℕ, (hm : m ≤ k + 1) →
          V ⟨m, by omega⟩ - V 0 =
            ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val < m), (V j.succ - V j.castSucc) := by
        intro m
        induction m with
        | zero =>
          intro _
          have hemp : Finset.univ.filter (fun j : Fin (k + 1) => j.val < 0) = ∅ := by ext j; simp
          have h0 : (⟨0, by omega⟩ : Fin (k + 2)) = 0 := rfl
          rw [hemp, Finset.sum_empty, h0, sub_self]
        | succ m ih =>
          intro hm
          let jm : Fin (k + 1) := ⟨m, by omega⟩
          have hjm_mem : jm ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val < m + 1) := by
            simp [jm]
          have herase : (Finset.univ.filter (fun j : Fin (k + 1) => j.val < m + 1)).erase jm =
              Finset.univ.filter (fun j : Fin (k + 1) => j.val < m) := by
            ext j
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, jm]
            constructor
            · rintro ⟨hne, hlt⟩
              have : j.val ≠ m := fun h => hne (Fin.ext h)
              omega
            · intro hlt
              exact ⟨fun h => by
                have := congrArg (fun x : Fin (k + 1) => x.val) h
                dsimp only at this
                omega, by omega⟩
          rw [← Finset.add_sum_erase _ _ hjm_mem, herase, ← ih (by omega)]
          have h1 : jm.castSucc = ⟨m, by omega⟩ := rfl
          have h2 : jm.succ = ⟨m + 1, by omega⟩ := rfl
          rw [h1, h2]
          abel
      have hlast := hgen (k + 1) le_rfl
      have hall : Finset.univ.filter (fun j : Fin (k + 1) => j.val < k + 1) = Finset.univ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact j.isLt
      rw [hall] at hlast
      exact hlast
    have h1H : 1 - H = U (Fin.last (k + 1)) * (V (Fin.last (k + 1)) - V 0) := by
      rw [Matrix.mul_sub, hUVdiag, hUVclose]
    calc (1 - H).rank
        = (U (Fin.last (k + 1)) * (V (Fin.last (k + 1)) - V 0)).rank := by rw [h1H]
      _ ≤ (V (Fin.last (k + 1)) - V 0).rank := Matrix.rank_mul_le_right _ _
      _ = (∑ j : Fin (k + 1), (V j.succ - V j.castSucc)).rank := by rw [htele]
      _ ≤ ∑ j : Fin (k + 1), (V j.succ - V j.castSucc).rank := matrix_rank_sum_le _ _
      _ ≤ ∑ _j : Fin (k + 1), s := Finset.sum_le_sum fun j _ => hdiff_le j
      _ = (k + 1) * s := by simp

def hstack {r s : ℕ} (L : Matrix (Fin r) (Fin r) K) (R : Matrix (Fin r) (Fin s) K) :
    Matrix (Fin r) (Fin (r + s)) K :=
  fun a j => if hj : j.val < r then L a ⟨j.val, hj⟩ else R a ⟨j.val - r, by omega⟩

def vstack {r s : ℕ} (T : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin s) (Fin r) K) :
    Matrix (Fin (r + s)) (Fin r) K :=
  fun j b => if hj : j.val < r then T ⟨j.val, hj⟩ b else B ⟨j.val - r, by omega⟩ b

lemma hstack_mul_vstack {r s : ℕ} (L T : Matrix (Fin r) (Fin r) K)
    (R : Matrix (Fin r) (Fin s) K) (B : Matrix (Fin s) (Fin r) K) :
    hstack L R * vstack T B = L * T + R * B := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.add_apply, hstack, vstack]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (r + s) => j.val < r)]
  congr 1
  · refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.ext (congrArg (fun x : Fin r => x.val) h))
      (fun i _ => ⟨⟨i.val, by have := i.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩)
      (fun j hj => by
        have hlt : j.val < r := (Finset.mem_filter.mp hj).2
        simp [hlt])
  · refine Finset.sum_bij (fun j hj => ⟨j.val - r, by
        have hge : ¬ j.val < r := (Finset.mem_filter.mp hj).2
        have := j.isLt; omega⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun j₁ hj₁ j₂ hj₂ h => by
        have h1 : ¬ j₁.val < r := (Finset.mem_filter.mp hj₁).2
        have h2 : ¬ j₂.val < r := (Finset.mem_filter.mp hj₂).2
        have hv := congrArg (fun x : Fin s => x.val) h
        dsimp only at hv
        exact Fin.ext (by omega))
      (fun i _ => ⟨⟨r + i.val, by have := i.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by ext; simp⟩)
      (fun j hj => by
        have hge : ¬ j.val < r := (Finset.mem_filter.mp hj).2
        simp [hge])

lemma matrix_inv_of_ker_eq_bot {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (hker : LinearMap.ker M.mulVecLin = ⊥) :
    ∃ Minv : Matrix (Fin r) (Fin r) K, Minv * M = 1 ∧ M * Minv = 1 := by
  have hinj : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective M.mulVecLin := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := LinearEquiv.ofBijective M.mulVecLin hbij
  let Minv : Matrix (Fin r) (Fin r) K := LinearMap.toMatrix' e.symm.toLinearMap
  refine ⟨Minv, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    ext a
    exact congrFun (e.symm_apply_apply x) a
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    ext a
    exact congrFun (e.apply_symm_apply x) a

lemma lift_step {r s : ℕ} (Mcur Mnext Minv : Matrix (Fin r) (Fin r) K)
    (hMinv : Minv * Mnext = 1) (Bnext : Matrix (Fin s) (Fin r) K)
    (hdiff : (Mnext - Mcur).rank ≤ s) :
    ∃ (Ucur : Matrix (Fin r) (Fin (r + s)) K) (Bcur : Matrix (Fin s) (Fin r) K),
      Ucur * vstack Mnext Bnext = 1 ∧ Ucur * vstack Mcur Bcur = 1 := by
  let Δ : Matrix (Fin r) (Fin r) K := Minv * (Mnext - Mcur)
  have hΔrank : Δ.rank ≤ s := (Matrix.rank_mul_le_right Minv (Mnext - Mcur)).trans hdiff
  obtain ⟨C, D, hCD⟩ := matrix_factor_of_rank_le Δ hΔrank
  let Ucur := hstack (Minv - C * Bnext * Minv) C
  let Bcur := D + Bnext * Minv * Mcur
  refine ⟨Ucur, Bcur, ?_, ?_⟩
  · simp only [Ucur, hstack_mul_vstack, Matrix.sub_mul, hMinv]
    rw [Matrix.mul_assoc C Bnext Minv, Matrix.mul_assoc C (Bnext * Minv) Mnext,
      Matrix.mul_assoc Bnext Minv Mnext, hMinv, Matrix.mul_one]
    abel
  · simp only [Ucur, Bcur, hstack_mul_vstack, Matrix.sub_mul, Matrix.mul_add]
    have h1 : C * Bnext * Minv * Mcur = C * (Bnext * Minv * Mcur) := by
      simp [Matrix.mul_assoc]
    have h2 : Minv * Mcur + C * D = 1 := by
      rw [hCD]
      simp only [Δ, Matrix.mul_sub, hMinv]
      abel
    rw [h1]
    have h3 : Minv * Mcur - C * (Bnext * Minv * Mcur) + (C * D + C * (Bnext * Minv * Mcur)) =
        Minv * Mcur + C * D := by abel
    rw [h3, h2]

lemma sufficiency (k r s : ℕ) (H : Matrix (Fin r) (Fin r) K)
    (h1 : r ≤ H.rank + s) (h2 : (1 - H).rank ≤ (k + 1) * s) :
    ∃ A : Matrix (Fin (k + 2) × Fin r) (Fin (k + 2) × Fin r) K,
      A.rank ≤ r + s ∧
      (∀ i : Fin (k + 2), A.submatrix (fun a => (i, a)) (fun b => (i, b)) = 1) ∧
      (∀ j : Fin (k + 1), A.submatrix (fun a => (j.castSucc, a)) (fun b => (j.succ, b)) = 1) ∧
      A.submatrix (fun a => (Fin.last (k + 1), a)) (fun b => (0, b)) = H := by
  let T : (Fin r → K) →ₗ[K] (Fin r → K) := H.mulVecLin
  have hm_le_s : Module.finrank K (LinearMap.ker T) ≤ s := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    rw [Module.finrank_pi, Fintype.card_fin] at hrn
    have hr : Module.finrank K (LinearMap.range T) = H.rank := rfl
    omega
  have hd_eq : Module.finrank K (LinearMap.range (LinearMap.id - T)) = (1 - H).rank := by
    have hlin : (1 - H).mulVecLin = LinearMap.id - T := by
      apply LinearMap.ext; intro x; ext a
      simp [T]
    rw [Matrix.rank]
    exact congrArg (fun L => Module.finrank K (LinearMap.range L)) hlin.symm
  obtain ⟨hm_le_d, E, hE1, hEsum, hEinv⟩ := rank_path_invertible T
  let d := Module.finrank K (LinearMap.range (LinearMap.id - T))
  have hd_le : d ≤ (k + 1) * s := hd_eq.le.trans h2

  let c (i : ℕ) : ℕ := min d (i * s)
  let Mlin (i : ℕ) : (Fin r → K) →ₗ[K] (Fin r → K) :=
    T + ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < c i), E t
  let M (i : Fin (k + 2)) : Matrix (Fin r) (Fin r) K := LinearMap.toMatrix' (Mlin i.val)
  have hM0 : M 0 = H := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix']
    simp only [Mlin, c, Fin.val_zero, zero_mul, Nat.min_zero]
    have hemp : Finset.univ.filter (fun t : Fin d => t.val < 0) = ∅ := by ext t; simp
    rw [hemp, Finset.sum_empty, add_zero]
    rfl
  have hMlast : M (Fin.last (k + 1)) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    have hc : c (k + 1) = d := Nat.min_eq_left hd_le
    simp only [Mlin, Fin.val_last, hc]
    have hall : Finset.univ.filter (fun t : Fin d => t.val < d) = Finset.univ := by
      ext t; simp
    rw [hall]
    exact hEsum
  have hMdiff : ∀ j : Fin (k + 1), (M j.succ - M j.castSucc).rank ≤ s := by
    intro j
    have hsub_lin : (M j.succ - M j.castSucc).mulVecLin =
        ∑ t ∈ Finset.univ.filter (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1)), E t := by
      have h1 : (M j.succ - M j.castSucc).mulVecLin = Mlin (j.val + 1) - Mlin j.val := by
        change Matrix.toLin' (M j.succ - M j.castSucc) = Mlin (j.val + 1) - Mlin j.val
        rw [map_sub, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
        rfl
      rw [h1]
      simp only [Mlin, add_sub_add_left_eq_sub]
      have hsub_filt : Finset.univ.filter (fun t : Fin d => t.val < c j.val) ⊆
          Finset.univ.filter (fun t : Fin d => t.val < c (j.val + 1)) := by
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hc_le : c j.val ≤ c (j.val + 1) := by
          simp only [c]
          exact min_le_min_left d (Nat.mul_le_mul_right s (Nat.le_succ _))
        omega
      rw [← Finset.sum_sdiff hsub_filt, add_sub_cancel_right]
      congr 1
      ext t
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [Matrix.rank, hsub_lin]
    calc Module.finrank K
            (LinearMap.range (∑ t ∈ Finset.univ.filter
              (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1)), E t))
        ≤ ∑ t ∈ Finset.univ.filter
            (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1)),
              Module.finrank K (LinearMap.range (E t)) := finrank_range_sum_le _ _
      _ ≤ ∑ _t ∈ Finset.univ.filter
            (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1)), 1 :=
          Finset.sum_le_sum fun t _ => hE1 t
      _ = (Finset.univ.filter (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1))).card := by
          simp
      _ ≤ c (j.val + 1) - c j.val := by
          have hinj : (Finset.univ.filter (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1))).card ≤
              (Finset.Ico (c j.val) (c (j.val + 1))).card := by
            have hsub : (Finset.univ.filter (fun t : Fin d => c j.val ≤ t.val ∧ t.val < c (j.val + 1))).image
                Fin.val ⊆ Finset.Ico (c j.val) (c (j.val + 1)) := by
              intro x hx
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
              exact Finset.mem_Ico.mpr (Finset.mem_filter.mp ht).2
            calc _ = ((Finset.univ.filter _).image Fin.val).card :=
                  (Finset.card_image_of_injective _ Fin.val_injective).symm
              _ ≤ (Finset.Ico (c j.val) (c (j.val + 1))).card := Finset.card_le_card hsub
          simpa [Nat.card_Ico] using hinj
      _ ≤ s := by
          simp only [c]
          have hadd : (j.val + 1) * s = j.val * s + s := by ring
          rw [hadd]
          omega
  have hMinv : ∀ j : Fin (k + 1), ∃ Minv : Matrix (Fin r) (Fin r) K,
      Minv * M j.succ = 1 ∧ M j.succ * Minv = 1 := by
    intro j
    apply matrix_inv_of_ker_eq_bot
    have hmul : (M j.succ).mulVecLin = Mlin (j.val + 1) := by
      change Matrix.toLin' (M j.succ) = Mlin (j.val + 1)
      rw [Matrix.toLin'_toMatrix']
      rfl
    rw [hmul]
    have hcm : Module.finrank K (LinearMap.ker T) ≤ c (j.val + 1) := by
      simp only [c]
      refine le_min hm_le_d ?_
      calc Module.finrank K (LinearMap.ker T) ≤ s := hm_le_s
        _ = 1 * s := (one_mul s).symm
        _ ≤ (j.val + 1) * s := Nat.mul_le_mul_right s (by omega)
    exact hEinv (c (j.val + 1)) hcm (Nat.min_le_left _ _)

  have hlift_all : ∀ n : ℕ, (hn : n ≤ k + 1) →
      ∃ (B : (i : Fin (k + 2)) → k + 1 - n ≤ i.val → Matrix (Fin s) (Fin r) K)
        (U : (i : Fin (k + 2)) → k + 1 - n ≤ i.val → Matrix (Fin r) (Fin (r + s)) K),
        (∀ hlast, B (Fin.last (k + 1)) hlast = 0 ∧ U (Fin.last (k + 1)) hlast = hstack 1 0) ∧
        (∀ i hi, U i hi * vstack (M i) (B i hi) = 1) ∧
        (∀ (j : Fin (k + 1)) (hj : k + 1 - n ≤ j.castSucc.val),
          U j.castSucc hj * vstack (M j.succ) (B j.succ (by simp at hj ⊢; omega)) = 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ _ => 0, fun _ _ => hstack 1 0, fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩
      · intro i hi
        have hieq : i = Fin.last (k + 1) := Fin.ext (by simp; omega)
        subst hieq
        rw [hMlast, hstack_mul_vstack]
        simp
      · intro j hj
        simp at hj
        omega
    | succ n ih =>
      intro hn
      obtain ⟨Bprev, Uprev, hlast_prev, hdiag_prev, hsup_prev⟩ := ih (by omega)
      let j₀ : Fin (k + 1) := ⟨k - n, by omega⟩
      have hj₀_succ : k + 1 - n ≤ j₀.succ.val := by simp [j₀]; omega
      obtain ⟨Minv, hMinvL, _⟩ := hMinv j₀
      obtain ⟨Uj₀, Bj₀, hUsup, hUdiag⟩ :=
        lift_step (M j₀.castSucc) (M j₀.succ) Minv hMinvL (Bprev j₀.succ hj₀_succ) (hMdiff j₀)
      let B : (i : Fin (k + 2)) → k + 1 - (n + 1) ≤ i.val → Matrix (Fin s) (Fin r) K :=
        fun i hi => if h : k + 1 - n ≤ i.val then Bprev i h else Bj₀
      let U : (i : Fin (k + 2)) → k + 1 - (n + 1) ≤ i.val → Matrix (Fin r) (Fin (r + s)) K :=
        fun i hi => if h : k + 1 - n ≤ i.val then Uprev i h else Uj₀
      refine ⟨B, U, ?_, ?_, ?_⟩
      · intro hlast
        have h : k + 1 - n ≤ (Fin.last (k + 1)).val := by simp
        simp only [B, U, h, ↓reduceDIte]
        exact hlast_prev h
      · intro i hi
        by_cases h : k + 1 - n ≤ i.val
        · simp only [B, U, h, ↓reduceDIte]
          exact hdiag_prev i h
        · simp only [B, U, h, ↓reduceDIte]
          have hieq : i = j₀.castSucc := Fin.ext (by simp [j₀]; omega)
          rw [hieq]
          exact hUdiag
      · intro j hj
        by_cases h : k + 1 - n ≤ j.castSucc.val
        · have hs : k + 1 - n ≤ j.succ.val := by simp at h ⊢; omega
          simp only [B, U, h, hs, ↓reduceDIte]
          exact hsup_prev j h
        · have hj_eq : j = j₀ := Fin.ext (by simp [j₀] at h hj ⊢; omega)
          subst hj_eq
          have hs : k + 1 - n ≤ j₀.succ.val := hj₀_succ
          simp only [B, U, h, hs, ↓reduceDIte]
          exact hUsup
  obtain ⟨B, U, hlastBU, hdiagBU, hsupBU⟩ := hlift_all (k + 1) le_rfl
  have h0le : ∀ i : Fin (k + 2), k + 1 - (k + 1) ≤ i.val := fun _ => by simp
  let Uf (i : Fin (k + 2)) : Matrix (Fin r) (Fin (r + s)) K := U i (h0le i)
  let Vf (i : Fin (k + 2)) : Matrix (Fin (r + s)) (Fin r) K := vstack (M i) (B i (h0le i))
  let Ubig : Matrix (Fin (k + 2) × Fin r) (Fin (r + s)) K := fun p t => Uf p.1 p.2 t
  let Vbig : Matrix (Fin (r + s)) (Fin (k + 2) × Fin r) K := fun t q => Vf q.1 t q.2
  let A : Matrix (Fin (k + 2) × Fin r) (Fin (k + 2) × Fin r) K := Ubig * Vbig
  have hsubA : ∀ i j : Fin (k + 2),
      A.submatrix (fun a => (i, a)) (fun b => (j, b)) = Uf i * Vf j := by
    intro i j; ext a b; rfl
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · exact (Matrix.rank_mul_le_left Ubig Vbig).trans
      (by simpa [Fintype.card_fin] using Matrix.rank_le_card_width Ubig)
  · intro i
    rw [hsubA i i]
    exact hdiagBU i (h0le i)
  · intro j
    rw [hsubA j.castSucc j.succ]
    exact hsupBU j (h0le j.castSucc)
  · rw [hsubA (Fin.last (k + 1)) 0]
    have hUlast : Uf (Fin.last (k + 1)) = hstack 1 0 := (hlastBU (h0le _)).2
    rw [hUlast]
    simp only [Vf, hstack_mul_vstack, Matrix.one_mul, Matrix.zero_mul, add_zero, hM0]

end MainTheorem

end

end PEqualNP.Outside.L_lib_1002_aux

theorem PEqualNP.Outside.L_lib_1002 : (∀ (K : Type) [Field K] (k r s : ℕ) (H : Matrix (Fin r) (Fin r) K),
  let I := Fin (k+2)
  let last : I := Fin.last (k+1)
  (∃ A : Matrix (I × Fin r) (I × Fin r) K,
    Matrix.rank A ≤ r+s ∧
    (∀ i : I, A.submatrix (fun a => (i,a)) (fun b => (i,b)) = 1) ∧
    (∀ j : Fin (k+1), A.submatrix (fun a => (j.castSucc,a)) (fun b => (j.succ,b)) = 1) ∧
    A.submatrix (fun a => (last,a)) (fun b => (0,b)) = H) ↔
  r ≤ Matrix.rank H + s ∧ Matrix.rank (1-H) ≤ (k+1)*s) := by
  intro K _ k r s H
  constructor
  · rintro ⟨A, h1, h2, h3, h4⟩
    exact PEqualNP.Outside.L_lib_1002_aux.necessity k r s H A h1 h2 h3 h4
  · rintro ⟨h1, h2⟩
    exact PEqualNP.Outside.L_lib_1002_aux.sufficiency k r s H h1 h2
