import PEqualNP.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_873.JointRecovery

theorem finrank_joint_recovery {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (U V B : Submodule F W) :
    Module.finrank F ↥((U ⊔ V) ⊓ B) =
      Module.finrank F ↥((U ⊓ B) ⊔ (V ⊓ B)) +
      (Module.finrank F ↥((U ⊔ B) ⊓ (V ⊔ B)) -
        Module.finrank F ↥((U ⊓ V) ⊔ B)) := by
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq U V
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ V) B
  have h₃ := Submodule.finrank_sup_add_finrank_inf_eq U B
  have h₄ := Submodule.finrank_sup_add_finrank_inf_eq V B
  have h₅ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ B) (V ⊔ B)
  have h₆ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ V) B
  have h₇ := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ B) (V ⊓ B)
  have he₁ : (U ⊔ B) ⊔ (V ⊔ B) = (U ⊔ V) ⊔ B := by
    simp only [sup_assoc, sup_left_comm, sup_idem]
  have he₂ : (U ⊓ B) ⊓ (V ⊓ B) = (U ⊓ V) ⊓ B := by
    simp only [inf_assoc, inf_left_comm, inf_idem]
  rw [he₁] at h₅
  rw [he₂] at h₇
  have hle : (U ⊓ V) ⊔ B ≤ (U ⊔ B) ⊓ (V ⊔ B) := by
    exact sup_le (le_inf (inf_le_left.trans le_sup_left)
      (inf_le_right.trans le_sup_left)) (le_inf le_sup_right le_sup_right)
  have hdim := Submodule.finrank_mono hle
  omega

theorem uniform_coeff_iff {F E I J K L : Type*} [Field F]
    [Fintype K] [Fintype L] [Nonempty I] [Nonempty J]
    (a : I → K → E → F) (b : J → L → E → F) (w : E → F) :
    (∃ (c : I → K → F) (t : J → L → F), ∀ i j e,
      (∑ k, c i k * a i k e) + (∑ l, t j l * b j l e) = w e) ↔
    w ∈ (⨅ i, Submodule.span F (Set.range (a i))) ⊔
      (⨅ j, Submodule.span F (Set.range (b j))) := by
  classical
  constructor
  · rintro ⟨c, t, ht⟩
    let i₀ : I := Classical.choice inferInstance
    let j₀ : J := Classical.choice inferInstance
    let x : E → F := ∑ k, c i₀ k • a i₀ k
    let y : E → F := ∑ l, t j₀ l • b j₀ l
    have hx (i : I) : x = ∑ k, c i k • a i k := by
      ext e
      have h₁ := ht i₀ j₀ e
      have h₂ := ht i j₀ e
      simpa [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using add_right_cancel (h₁.trans h₂.symm)
    have hy (j : J) : y = ∑ l, t j l • b j l := by
      ext e
      have h₁ := ht i₀ j₀ e
      have h₂ := ht i₀ j e
      simpa [y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using add_left_cancel (h₁.trans h₂.symm)
    apply Submodule.mem_sup.mpr
    refine ⟨x, ?_, y, ?_, ?_⟩
    · rw [Submodule.mem_iInf]
      intro i
      rw [hx i]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self k)))
    · rw [Submodule.mem_iInf]
      intro j
      rw [hy j]
      exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self l)))
    · ext e
      simpa [x, y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ht i₀ j₀ e
  · intro hw
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hw
    simp only [Submodule.mem_iInf] at hx hy
    have hcx : ∀ i, ∃ c : K → F, ∑ k, c k • a i k = x := by
      intro i
      exact (Submodule.mem_span_range_iff_exists_fun F).mp (hx i)
    have hty : ∀ j, ∃ t : L → F, ∑ l, t l • b j l = y := by
      intro j
      exact (Submodule.mem_span_range_iff_exists_fun F).mp (hy j)
    choose c hc using hcx
    choose t ht using hty
    refine ⟨c, t, ?_⟩
    intro i j e
    have he := congrFun hxy e
    rw [← hc i, ← ht j] at he
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

theorem natCard_linear_preimage {F P W : Type*} [Field F]
    [AddCommGroup P] [Module F P] [FiniteDimensional F P]
    [AddCommGroup W] [Module F W]
    (L : P →ₗ[F] W) (hinj : Function.Injective L) (T : Submodule F W) :
    Nat.card {p : P // L p ∈ T} =
      Nat.card F ^ Module.finrank F ↥(T ⊓ LinearMap.range L) := by
  change Nat.card ↥(T.comap L) = _
  rw [Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  have he := (Submodule.equivMapOfInjective L hinj (T.comap L)).finrank_eq
  rw [Submodule.map_comap_eq L T] at he
  exact he.trans (congrArg (fun S : Submodule F W => Module.finrank F S)
    (inf_comm (LinearMap.range L) T))

def parityMap (f s : ℕ) : (Fin s → ZMod 2) →ₗ[ZMod 2]
    ((Fin f × (Fin s → ZMod 2)) → ZMod 2) where
  toFun mask e := ∑ h, mask h * e.2 h
  map_add' x y := by
    ext e
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem parityMap_injective (f s : ℕ) (hf : 0 < f) :
    Function.Injective (parityMap f s) := by
  classical
  intro x y h
  ext i
  have he := congrFun h ((⟨0, hf⟩ : Fin f), Pi.single i 1)
  simpa [parityMap, Pi.single_apply] using he

theorem range_parityMap (f s : ℕ) :
    LinearMap.range (parityMap f s) =
      Submodule.span (ZMod 2) (Set.range (fun j : Fin s =>
        fun e : Fin f × (Fin s → ZMod 2) => e.2 j)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨mask, rfl⟩
    have he : parityMap f s mask = ∑ j : Fin s,
        mask j • (fun e : Fin f × (Fin s → ZMod 2) => e.2 j) := by
      ext e
      simp [parityMap]
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    ext e
    simp [parityMap, Pi.single_apply]

theorem uniform_recovery_card (f s u v m n : ℕ) (hf : 0 < f) (hu : 0 < u) (hv : 0 < v)
    (a : Fin u → Fin m → (Fin f × (Fin s → ZMod 2)) → ZMod 2)
    (b : Fin v → Fin n → (Fin f × (Fin s → ZMod 2)) → ZMod 2) :
    let F := ZMod 2
    let W := (Fin f × (Fin s → F)) → F
    let U : Submodule F W := ⨅ i, Submodule.span F (Set.range (a i))
    let V : Submodule F W := ⨅ j, Submodule.span F (Set.range (b j))
    let B : Submodule F W := Submodule.span F (Set.range (fun j : Fin s =>
      fun e : Fin f × (Fin s → F) => e.2 j))
    Nat.card {mask : Fin s → F //
      ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F), ∀ i j e,
        (∑ k, c i k * a i k e) + (∑ l, t j l * b j l e) = ∑ h, mask h * e.2 h} =
    2 ^ (Module.finrank F ↥((U ⊓ B) ⊔ (V ⊓ B)) +
      (Module.finrank F ↥((U ⊔ B) ⊓ (V ⊔ B)) - Module.finrank F ↥((U ⊓ V) ⊔ B))) := by
  classical
  letI : Nonempty (Fin u) := ⟨⟨0, hu⟩⟩
  letI : Nonempty (Fin v) := ⟨⟨0, hv⟩⟩
  dsimp only
  let U := ⨅ i, Submodule.span (ZMod 2) (Set.range (a i))
  let V := ⨅ j, Submodule.span (ZMod 2) (Set.range (b j))
  let B := Submodule.span (ZMod 2) (Set.range (fun j : Fin s =>
    fun e : Fin f × (Fin s → ZMod 2) => e.2 j))
  have hc := Nat.card_congr (Equiv.subtypeEquivRight (fun mask =>
    uniform_coeff_iff a b (parityMap f s mask)))
  change Nat.card {mask : Fin s → ZMod 2 //
    ∃ (c : Fin u → Fin m → ZMod 2) (t : Fin v → Fin n → ZMod 2), ∀ i j e,
      (∑ k, c i k * a i k e) + (∑ l, t j l * b j l e) = ∑ h, mask h * e.2 h} =
    Nat.card {mask : Fin s → ZMod 2 // parityMap f s mask ∈ U ⊔ V} at hc
  rw [hc, natCard_linear_preimage (parityMap f s) (parityMap_injective f s hf) (U ⊔ V),
    Nat.card_zmod, range_parityMap]
  congr 1
  exact finrank_joint_recovery U V B

end PEqualNP.Outside.L_lib_873.JointRecovery

theorem PEqualNP.Outside.L_lib_873 :
∀ (f s u v m n : ℕ), 0 < f → 0 < u → 0 < v →
  let F := ZMod 2
  let P := Fin s → F
  let E := Fin f × P
  let W := E → F
  ∀ (row : Fin u → Fin f → P → Fin m → F)
    (col : Fin v → Fin f → P → Fin n → F),
    let a := fun (i : Fin u) (j : Fin m) (e : E) =>
      row i e.1 e.2 j - row i e.1 0 j
    let b := fun (i : Fin v) (j : Fin n) (e : E) =>
      col i e.1 e.2 j - col i e.1 0 j
    let U : Submodule F W := ⨅ i : Fin u, Submodule.span F (Set.range (a i))
    let V : Submodule F W := ⨅ i : Fin v, Submodule.span F (Set.range (b i))
    let B : Submodule F W := Submodule.span F (Set.range (fun j : Fin s => fun e : E => e.2 j))
    let solo := Module.finrank F (((U ⊓ B) ⊔ (V ⊓ B)) : Submodule F W)
    let extra := Module.finrank F (((U ⊔ B) ⊓ (V ⊔ B)) : Submodule F W) -
      Module.finrank F (((U ⊓ V) ⊔ B) : Submodule F W)
    Nat.card {mask : P //
      ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
        ∀ (i : Fin u) (j : Fin v) (e : E),
          (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
            ∑ h : Fin s, mask h * e.2 h} = 2 ^ (solo + extra) := by
  intro f s u v m n hf hu hv
  dsimp only
  intro row col
  exact PEqualNP.Outside.L_lib_873.JointRecovery.uniform_recovery_card f s u v m n hf hu hv _ _
