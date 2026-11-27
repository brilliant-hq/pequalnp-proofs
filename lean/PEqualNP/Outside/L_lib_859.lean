import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_859

open Finset

theorem zmod2_eq_one {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

theorem add_self_zero {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) : y + y = 0 := by
  have h2 : (2 : K) = 0 := by
    have : (algebraMap (ZMod 2) K) 2 = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, map_zero]
    rwa [map_ofNat] at this
  rw [← two_mul, h2, zero_mul]

theorem nsmul_even {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) {n : ℕ} (h : Even n) :
    n • y = 0 := by
  obtain ⟨m, rfl⟩ := h
  rw [add_nsmul, add_self_zero]

theorem nsmul_odd {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) {n : ℕ} (h : ¬ Even n) :
    n • y = y := by
  obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp h
  rw [add_nsmul, two_mul, add_nsmul, add_self_zero, zero_add, one_nsmul]

theorem rank_full {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (f : K →ₗ[ZMod 2] K) (c : K) (hc : c ≠ 0) (hf : ∀ x, f x = c * x) :
    Module.finrank (ZMod 2) (LinearMap.range f) = Module.finrank (ZMod 2) K := by
  have : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨c⁻¹ * y, by rw [hf, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [this, finrank_top]

theorem sets_eq {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module (ZMod 2) V]
    (v : ι → V) (hv : LinearIndependent (ZMod 2) v) (S S' : Finset ι)
    (h : ∑ i ∈ S, v i = ∑ i ∈ S', v i) : S = S' := by
  have key : ∀ T : Finset ι, ∑ i, (if i ∈ T then (1 : ZMod 2) else 0) • v i = ∑ i ∈ T, v i := by
    intro T
    simp [ite_smul]
  have hz := Fintype.linearIndependent_iff.mp hv
    (fun i => (if i ∈ S then (1 : ZMod 2) else 0) - (if i ∈ S' then (1 : ZMod 2) else 0))
    (by simp only [sub_smul, Finset.sum_sub_distrib, key, h, sub_self])
  ext i
  have := hz i
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all

theorem sumform {K : Type} [Field K] [Algebra (ZMod 2) K] {k : ℕ}
    (D : Fin (k+1) → (K →ₗ[ZMod 2] K)) (a : Fin k → K)
    (ha : ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i * x) (S : Finset (Fin (k+1))) (x : K) :
    ∑ j ∈ S, D j x = S.card • D 0 x + (∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j) * x := by
  have hj : ∀ j : Fin (k+1), D j x = D 0 x + (Fin.cons 0 a : Fin (k+1) → K) j * x := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [ha]
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_mul]

theorem struct {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (k : ℕ) (hk : 0 < k) (hK : Module.finrank (ZMod 2) K = k)
    (D : Fin (k+1) → (K →ₗ[ZMod 2] K))
    (hD : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (D i)) < k)
    (hc : ∀ z : K, ∃ S : Finset (Fin (k+1)), ∀ x : K, ∑ i ∈ S, D i x = z * x) :
    LinearIndependent (ZMod 2) D ∧ ∃ a : Fin k → K, LinearIndependent (ZMod 2) a ∧
          ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i * x := by
  classical
  set μ := LinearMap.mul (ZMod 2) K with hμ
  set M := LinearMap.range μ with hM
  set V := Submodule.span (ZMod 2) (Set.range D) with hV
  have hμinj : Function.Injective μ := by
    intro c d h
    have := LinearMap.congr_fun h 1
    simpa [hμ] using this
  have hMr : Module.finrank (ZMod 2) M = k := by
    rw [hM, LinearMap.finrank_range_of_inj hμinj, hK]
  have hsing : ∀ f ∈ M, Module.finrank (ZMod 2) (LinearMap.range f) < k → f = 0 := by
    rintro f ⟨c, rfl⟩ hf
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exfalso
      have := rank_full (μ c) c h0 (fun x => by simp [hμ])
      omega
  have hMV : M ≤ V := by
    rintro f ⟨c, rfl⟩
    obtain ⟨S, hS⟩ := hc c
    have : μ c = ∑ i ∈ S, D i := by
      ext x
      rw [LinearMap.sum_apply, hS]
      simp [hμ]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  have eV : Set.finrank (ZMod 2) (Set.range D) = Module.finrank (ZMod 2) V := rfl
  have hVle : Module.finrank (ZMod 2) V ≤ k + 1 := by
    have := finrank_range_le_card (R := ZMod 2) D
    rw [eV, Fintype.card_fin] at this
    exact this
  have hli : LinearIndependent (ZMod 2) D := by
    by_contra hn
    have h1 : Module.finrank (ZMod 2) V ≤ k := by
      have : Fintype.card (Fin (k+1)) ≠ Module.finrank (ZMod 2) V :=
        fun h => hn (linearIndependent_iff_card_eq_finrank_span.mpr (h.trans eV.symm))
      rw [Fintype.card_fin] at this
      omega
    have hMeq : M = V := Submodule.eq_of_le_of_finrank_le hMV (by omega)
    have hz : ∀ i, D i = 0 := fun i =>
      hsing _ (hMeq ▸ Submodule.subset_span ⟨i, rfl⟩) (hD i)
    have hbot : V = ⊥ := by
      rw [hV, Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact hz i
    rw [hMeq, hbot, finrank_bot] at hMr
    omega
  have hVr : Module.finrank (ZMod 2) V = k + 1 := by
    have := linearIndependent_iff_card_eq_finrank_span.mp hli
    rw [eV, Fintype.card_fin] at this
    exact this.symm
  have hnotM : ∀ i, D i ∉ M := fun i h => hli.ne_zero i (hsing _ h (hD i))
  set W := M ⊔ Submodule.span (ZMod 2) {D 0} with hW
  have hD0W : D 0 ∈ W := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hMW : M < W := IsConcreteLE.lt_iff_le_and_exists.mpr ⟨le_sup_left, D 0, hD0W, hnotM 0⟩
  have hWV : W ≤ V := sup_le hMV (Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (Submodule.subset_span ⟨0, rfl⟩)))
  have hWr := Submodule.finrank_lt_finrank_of_lt hMW
  have hWeq : W = V := Submodule.eq_of_le_of_finrank_le hWV (by omega)
  have hdiff : ∀ i, ∃ a : K, ∀ x, D i x = D 0 x + a * x := by
    intro i
    have hi : D i ∈ W := hWeq ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hi
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    by_cases hc0 : c = 0
    · exfalso
      apply hnotM i
      rw [← hyz, hc0, zero_smul, add_zero]
      exact hy
    · rw [zmod2_eq_one hc0, one_smul] at hyz
      obtain ⟨a, rfl⟩ := hy
      refine ⟨a, fun x => ?_⟩
      rw [← hyz, LinearMap.add_apply, add_comm]
      simp [hμ]
  choose a ha using hdiff
  refine ⟨hli, fun i => a i.succ, ?_, fun i x => ha i.succ x⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := Fintype.linearIndependent_iff.mp hli
    (Fin.cons (-(∑ j, g j)) g : Fin (k+1) → ZMod 2) (by
      ext x
      rw [LinearMap.sum_apply, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.smul_apply, LinearMap.zero_apply]
      have e : ∀ j : Fin k, g j • D j.succ x = g j • D 0 x + (g j • a j.succ) * x := by
        intro j
        rw [ha j.succ x, smul_add, smul_mul_assoc]
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.sum_mul, hg,
        zero_mul, add_zero, ← Finset.sum_smul, neg_smul, neg_add_cancel])
  have := h0 i.succ
  simpa using this

theorem l858 :
let F := ZMod 2
∀ (k : ℕ), 0 < k →
  ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
    Module.finrank F K = k →
    ∀ (D : Fin (k+1) → (K →ₗ[F] K)),
      (∀ i, Module.finrank F (LinearMap.range (D i)) < k) →
      let hit := fun (S : Finset (Fin (k+1))) (z : K) =>
        ∀ x : K, ∑ i ∈ S, D i x = z*x
      ((∀ z : K, ∃ S, hit S z) ↔
        ∃ a : Fin k → K, LinearIndependent F a ∧
          ∀ (i : Fin k) (x : K), D i.succ x = D 0 x + a i*x) ∧
      ((∀ z : K, ∃ S, hit S z) →
        (∀ S, (∃ z : K, hit S z) ↔ Even S.card) ∧
        (∀ z : K, ∃! S, hit S z)) := by
  intro F k hk K _ _ _ hK D hD hit
  classical
  refine ⟨⟨fun hc => (struct k hk hK D hD hc).2, ?_⟩, ?_⟩
  · rintro ⟨a, hai, ha⟩ z
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have hspan := hai.span_eq_top_of_card_eq_finrank (by simpa using hK.symm)
    have hz : z ∈ Submodule.span (ZMod 2) (Set.range a) := by rw [hspan]; trivial
    obtain ⟨c, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hz
    set T := Finset.univ.filter (fun i => c i = 1) with hT
    have hTs : ∑ i ∈ T, a i = z := by
      rw [← hcz, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : c i = 1
      · rw [if_pos h, h, one_smul]
      · have h0 : c i = 0 := by
          by_contra h0
          exact h (zmod2_eq_one h0)
        rw [if_neg h, h0, zero_smul]
    set S0 := T.map (Fin.succEmb k) with hS0
    have hS0s : ∑ j ∈ S0, (Fin.cons 0 a : Fin (k+1) → K) j = z := by
      rw [hS0, Finset.sum_map]
      simpa using hTs
    have h0n : (0 : Fin (k+1)) ∉ S0 := by
      rw [hS0, Finset.mem_map]
      rintro ⟨i, _, hi⟩
      exact Fin.succ_ne_zero i hi
    by_cases hev : Even S0.card
    · refine ⟨S0, fun x => ?_⟩
      rw [sumform D a ha, nsmul_even _ hev, zero_add, hS0s]
    · refine ⟨insert 0 S0, fun x => ?_⟩
      have hev' : Even (insert 0 S0).card := by
        rw [Finset.card_insert_of_notMem h0n]
        exact (Nat.even_add_one).mpr hev
      rw [sumform D a ha, nsmul_even _ hev', zero_add, Finset.sum_insert h0n, hS0s]
      simp
  · intro hc
    obtain ⟨hli, a, hai, ha⟩ := struct k hk hK D hD hc
    refine ⟨fun S => ⟨?_, ?_⟩, fun z => ?_⟩
    · rintro ⟨z, hz⟩
      by_contra hev
      have hD0 : ∀ x, D 0 x = (z - ∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j) * x := by
        intro x
        have := hz x
        rw [sumform D a ha, nsmul_odd _ hev] at this
        rw [sub_mul, ← this, add_sub_cancel_right]
      by_cases h0 : z - ∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j = 0
      · have i0 : Fin k := ⟨0, hk⟩
        have hr := rank_full (D i0.succ) (a i0) (hai.ne_zero i0)
          (fun x => by rw [ha, hD0, h0, zero_mul, zero_add])
        have h2 : Module.finrank (ZMod 2) (LinearMap.range (D i0.succ)) < k := hD i0.succ
        have hK' : Module.finrank (ZMod 2) K = k := hK
        omega
      · have hr := rank_full (D 0) _ h0 hD0
        have h2 : Module.finrank (ZMod 2) (LinearMap.range (D 0)) < k := hD 0
        have hK' : Module.finrank (ZMod 2) K = k := hK
        omega
    · intro hev
      exact ⟨∑ j ∈ S, (Fin.cons 0 a : Fin (k+1) → K) j, fun x => by
        rw [sumform D a ha, nsmul_even _ hev, zero_add]⟩
    · obtain ⟨S, hS⟩ := hc z
      refine ⟨S, hS, fun S' hS' => ?_⟩
      apply sets_eq D hli
      ext x
      rw [LinearMap.sum_apply, LinearMap.sum_apply, hS, hS']

theorem charTwo {K : Type} [Field K] [Algebra (ZMod 2) K] : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem frob_add {K : Type} [Field K] [Algebra (ZMod 2) K] (d : ℕ) (x y : K) :
    (x + y) ^ (2 ^ d) = x ^ (2 ^ d) + y ^ (2 ^ d) := by
  have := charTwo (K := K)
  exact add_pow_char_pow x y 2 d

theorem neg_two {K : Type} [Field K] [Algebra (ZMod 2) K] (y : K) : -y = y := by
  have := add_self_zero y
  rw [neg_eq_iff_add_eq_zero]
  exact this

noncomputable def fr (K : Type) [Field K] [Algebra (ZMod 2) K] (d : ℕ) : K →ₗ[ZMod 2] K where
  toFun x := x ^ (2 ^ d)
  map_add' x y := frob_add d x y
  map_smul' c x := by
    by_cases hc : c = 0
    · rw [hc]
      simp [zero_pow (pow_ne_zero d two_ne_zero)]
    · rw [zmod2_eq_one hc]
      simp

theorem roots_le {K : Type} [Field K] [Fintype K] [DecidableEq K] (m j : ℕ) (hj : j < m)
    (c : K) : (univ.filter (fun x : K => x ^ m = c * x ^ j)).card ≤ m := by
  set P : Polynomial K := Polynomial.X ^ m - Polynomial.C c * Polynomial.X ^ j with hPd
  have hdeg : P.natDegree = m := by
    rw [hPd, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le c j) hj
  have hP : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  calc (univ.filter (fun x : K => x ^ m = c * x ^ j)).card ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
        have := (mem_filter.mp hx).2
        simp [hPd, this]
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = m := hdeg

theorem dim_le {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K] (d : ℕ) (hd : 0 < d)
    (U : Submodule (ZMod 2) K) (b : K) (h : ∀ x ∈ U, x ^ (2 ^ d) = b * x) :
    Module.finrank (ZMod 2) U ≤ d := by
  classical
  have h1 : Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]
  have h2 : Fintype.card U ≤ 2 ^ d := by
    calc Fintype.card U = (univ.filter (fun x : K => x ∈ U)).card := Fintype.card_subtype _
      _ ≤ (univ.filter (fun x : K => x ^ (2 ^ d) = b * x ^ 1)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_filter] at hx ⊢
          rw [pow_one]
          exact ⟨hx.1, h x hx.2⟩
      _ ≤ 2 ^ d := roots_le _ _ (Nat.one_lt_two_pow (by omega)) b
  rw [h1] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem rank_eq {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K]
    (d : ℕ) (hd : 0 < d) (hK : Module.finrank (ZMod 2) K = 2 * d)
    (a : K) (ha : a ^ (2 ^ d + 1) = 1) (D : K →ₗ[ZMod 2] K) (hD : ∀ x, D x = x ^ (2 ^ d) + a * x) :
    Module.finrank (ZMod 2) (LinearMap.range D) = d := by
  classical
  have hcard : Fintype.card K = 2 ^ d * 2 ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), ZMod.card, hK, ← pow_add, two_mul]
  have hqq : ∀ x : K, (x ^ (2 ^ d)) ^ (2 ^ d) = x := by
    intro x
    rw [← pow_mul, ← hcard, FiniteField.pow_card]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at ha
    exact zero_ne_one ha
  have haq : a ^ (2 ^ d) = a⁻¹ := by
    rw [pow_succ] at ha
    exact eq_inv_of_mul_eq_one_left ha
  have hker := dim_le d hd (LinearMap.ker D) a (by
    intro x hx
    rw [LinearMap.mem_ker, hD] at hx
    have := eq_neg_of_add_eq_zero_left hx
    rw [this, neg_two])
  have hran := dim_le d hd (LinearMap.range D) a⁻¹ (by
    rintro y ⟨x, rfl⟩
    rw [hD, frob_add, mul_pow, hqq, haq, mul_add, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul,
      add_comm])
  have := LinearMap.finrank_range_add_finrank_ker D
  omega

theorem card_K {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K]
    (d : ℕ) (hK : Module.finrank (ZMod 2) K = 2 * d) : Fintype.card K = 2 ^ d * 2 ^ d := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), ZMod.card, hK, ← pow_add, two_mul]

theorem normone {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (d : ℕ) (hd : 0 < d) (hK : Module.finrank (ZMod 2) K = 2 * d) :
    (univ.filter (fun a : K => a ^ (2 ^ d + 1) = 1)).card = 2 ^ d + 1 := by
  have hcard := card_K d hK
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ d = r + 2 := ⟨2 ^ d - 2, by
    have := Nat.one_lt_two_pow (n := d) (by omega)
    omega⟩
  rw [hr] at hcard ⊢
  have e1 : (r + 2) * (r + 2) - 1 = (r + 1) * (r + 3) := by
    ring_nf
    omega
  apply le_antisymm
  · have := roots_le (K := K) (r + 2 + 1) 0 (by omega) 1
    simpa using this
  · set s := univ.filter (fun x : K => x ≠ 0) with hs
    have hsc : s.card = (r + 1) * (r + 3) := by
      rw [hs, Finset.filter_ne', card_erase_of_mem (mem_univ _), card_univ, hcard, e1]
    have him : s.image (fun x => x ^ (r + 1)) ⊆ univ.filter (fun a : K => a ^ (r + 2 + 1) = 1) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hx0 : x ≠ 0 := (mem_filter.mp hx).2
      have := FiniteField.pow_card_sub_one_eq_one x hx0
      rw [hcard, e1] at this
      rw [← pow_mul]
      exact this
    have hfib := card_le_mul_card_image s (r + 1) (by
      intro y _
      calc (s.filter (fun x => x ^ (r + 1) = y)).card
          ≤ (univ.filter (fun x : K => x ^ (r + 1) = y * x ^ 0)).card := by
            apply card_le_card
            intro x hx
            rw [mem_filter] at hx ⊢
            rw [pow_zero, mul_one]
            exact ⟨mem_univ _, hx.2⟩
        _ ≤ r + 1 := roots_le _ _ (by omega) y)
    have h3 := card_le_card him
    rw [hsc] at hfib
    have h4 : (r + 1) * (r + 3) ≤ (r + 1) * (univ.filter (fun a : K => a ^ (r + 2 + 1) = 1)).card :=
      hfib.trans (Nat.mul_le_mul_left _ h3)
    have := Nat.le_of_mul_le_mul_left h4 (by omega)
    omega

theorem sum_norm {K : Type} [Field K] [Fintype K] [DecidableEq K] (m : ℕ) (hm : 0 < m)
    (b : K) (hb : b ^ m = 1) (hb1 : b ≠ 1) :
    ∑ a ∈ univ.filter (fun a : K => a ^ m = 1), a = 0 := by
  set N := univ.filter (fun a : K => a ^ m = 1) with hN
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hb
    exact zero_ne_one hb
  have key : ∑ a ∈ N, b * a = ∑ a ∈ N, a := by
    refine Finset.sum_nbij' (fun a => b * a) (fun a => b⁻¹ * a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [hN, mem_filter] at ha ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [mul_pow, hb, ha.2, one_mul]
    · intro a ha
      rw [hN, mem_filter] at ha ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [mul_pow, inv_pow, hb, ha.2, inv_one, one_mul]
    · intro a _
      rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
    · intro a _
      rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
    · intro a _
      rfl
  rw [← Finset.mul_sum] at key
  have h2 : (b - 1) * ∑ a ∈ N, a = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hb1
  · exact h

theorem span_top {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K] [DecidableEq K]
    (d : ℕ) (hd : 0 < d) (hK : Module.finrank (ZMod 2) K = 2 * d) :
    Submodule.span (ZMod 2) ((univ.filter (fun a : K => a ^ (2 ^ d + 1) = 1) : Finset K) : Set K)
      = ⊤ := by
  classical
  set N := univ.filter (fun a : K => a ^ (2 ^ d + 1) = 1) with hN
  set V := Submodule.span (ZMod 2) (N : Set K) with hV
  have hcard := card_K d hK
  have hNc := normone d hd hK
  have memN : ∀ x : K, x ∈ N ↔ x ^ (2 ^ d + 1) = 1 := by
    intro x
    rw [hN, mem_filter]
    simp
  have hVV : V * V ≤ V := by
    rw [hV, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply Submodule.subset_span
    rw [Finset.mem_coe, memN] at hx hy ⊢
    rw [mul_pow, hx, hy, one_mul]
  have hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V := fun x hx y hy =>
    hVV (Submodule.mul_mem_mul hx hy)
  have h1 : (1 : K) ∈ V := Submodule.subset_span (by rw [Finset.mem_coe, memN, one_pow])
  have hpow : ∀ v ∈ V, ∀ n : ℕ, v ^ n ∈ V := by
    intro v hv n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hv
  have hinv : ∀ v ∈ V, v⁻¹ ∈ V := by
    intro v hv
    by_cases h0 : v = 0
    · rw [h0, inv_zero]
      exact V.zero_mem
    · have hc2 : 2 ≤ Fintype.card K := by
        rw [hcard]
        have := Nat.one_lt_two_pow (n := d) (by omega)
        nlinarith
      have e : v ^ (Fintype.card K - 2) = v⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega]
        exact FiniteField.pow_card_sub_one_eq_one v h0
      rw [← e]
      exact hpow v hv _
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t, t ∉ V := by
    by_contra hall
    push_neg at hall
    exact hne (Submodule.eq_top_iff'.mpr hall)
  have hinj : Function.Injective (fun p : V × V => (p.1 : K) + (p.2 : K) * t) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    simp only at h
    by_cases hyy : y = y'
    · subst hyy
      have : x = x' := add_right_cancel h
      subst this
      rfl
    · exfalso
      apply ht
      have hy0 : y - y' ≠ 0 := sub_ne_zero.mpr hyy
      have e : t = (x' - x) * (y - y')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hy0]
        linear_combination h
      rw [e]
      exact hmul _ (V.sub_mem hx' hx) _ (hinv _ (V.sub_mem hy hy'))
  have hle := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_prod, hcard] at hle
  have hVc : N.card ≤ Fintype.card V := by
    rw [Fintype.card_subtype]
    apply card_le_card
    intro x hx
    rw [mem_filter]
    exact ⟨mem_univ _, Submodule.subset_span hx⟩
  rw [hNc] at hVc
  have := Nat.mul_self_le_mul_self_iff.mp hle
  omega

theorem diff_basis {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K]
    (d : ℕ) (hd : 0 < d) (hK : Module.finrank (ZMod 2) K = 2 * d) :
    ∃ g : Fin (2 * d) → K, (∀ i, g i ^ (2 ^ d + 1) = 1) ∧
      LinearIndependent (ZMod 2) (fun i => g i - 1) := by
  classical
  set N := univ.filter (fun a : K => a ^ (2 ^ d + 1) = 1) with hN
  have memN : ∀ x : K, x ∈ N ↔ x ^ (2 ^ d + 1) = 1 := by
    intro x
    rw [hN, mem_filter]
    simp
  set T : Set K := (fun a => a - 1) '' (N : Set K) with hT
  set W := Submodule.span (ZMod 2) T with hW
  have hsum : ∑ a ∈ N, (a - 1) = -1 := by
    obtain ⟨b, hb, hb1⟩ : ∃ b ∈ N, b ≠ 1 := by
      by_contra hall
      push_neg at hall
      have : N ⊆ {1} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
      have := card_le_card this
      rw [normone d hd hK, card_singleton] at this
      have := Nat.one_lt_two_pow (n := d) (by omega)
      omega
    rw [Finset.sum_sub_distrib, sum_norm (2 ^ d + 1) (Nat.succ_pos _) b ((memN b).mp hb) hb1, sum_const,
      normone d hd hK, nsmul_odd, zero_sub]
    rw [Nat.even_add_one, not_not]
    exact (Nat.even_pow' hd.ne').mpr even_two
  have h1 : (1 : K) ∈ W := by
    have : ∑ a ∈ N, (a - 1) ∈ W :=
      W.sum_mem (fun a ha => Submodule.subset_span ⟨a, ha, rfl⟩)
    rw [hsum, neg_two] at this
    exact this
  have hWt : W = ⊤ := by
    rw [eq_top_iff, ← span_top d hd hK]
    apply Submodule.span_le.mpr
    intro a ha
    have : a - 1 ∈ W := Submodule.subset_span ⟨a, ha, rfl⟩
    have := W.add_mem this h1
    rw [sub_add_cancel] at this
    exact this
  obtain ⟨b, hbT, hbs, hbli⟩ := exists_linearIndependent (ZMod 2) T
  have hcb : Fintype.card b = 2 * d := by
    have := linearIndependent_iff_card_eq_finrank_span.mp hbli
    rw [this, Subtype.range_coe_subtype, Set.setOf_mem_eq]
    show Module.finrank (ZMod 2) (Submodule.span (ZMod 2) b) = 2 * d
    rw [hbs, ← hW, hWt, finrank_top, hK]
  let e := Fintype.equivFinOfCardEq hcb
  have hmem : ∀ i, ∃ a, a ^ (2 ^ d + 1) = 1 ∧ a - 1 = (e.symm i : K) := by
    intro i
    obtain ⟨a, ha, he⟩ := hbT (e.symm i).2
    exact ⟨a, (memN a).mp ha, he⟩
  choose g hg1 hg2 using hmem
  refine ⟨g, hg1, ?_⟩
  have : (fun i => g i - 1) = ((↑) : b → K) ∘ e.symm := funext hg2
  rw [this]
  exact hbli.comp _ e.symm.injective

theorem minimal {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (k : ℕ) (hk : 0 < k) (hK : Module.finrank (ZMod 2) K = k) (s : ℕ)
    (A : Fin s → (K →ₗ[ZMod 2] K))
    (hA : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (A i)) < k)
    (hc : ∀ z : K, ∃ S : Finset (Fin s), ∀ x : K, ∑ i ∈ S, A i x = z * x) : k + 1 ≤ s := by
  classical
  set μ := LinearMap.mul (ZMod 2) K with hμ
  set M := LinearMap.range μ with hM
  set V := Submodule.span (ZMod 2) (Set.range A) with hV
  have hμinj : Function.Injective μ := by
    intro c d h
    have := LinearMap.congr_fun h 1
    simpa [hμ] using this
  have hMr : Module.finrank (ZMod 2) M = k := by
    rw [hM, LinearMap.finrank_range_of_inj hμinj, hK]
  have hsing : ∀ f ∈ M, Module.finrank (ZMod 2) (LinearMap.range f) < k → f = 0 := by
    rintro f ⟨c, rfl⟩ hf
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exfalso
      have := rank_full (μ c) c h0 (fun x => by simp [hμ])
      omega
  have hMV : M ≤ V := by
    rintro f ⟨c, rfl⟩
    obtain ⟨S, hS⟩ := hc c
    have : μ c = ∑ i ∈ S, A i := by
      ext x
      rw [LinearMap.sum_apply, hS]
      simp [hμ]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  by_contra hs
  have eV : Set.finrank (ZMod 2) (Set.range A) = Module.finrank (ZMod 2) V := rfl
  have hVle : Module.finrank (ZMod 2) V ≤ s := by
    have := finrank_range_le_card (R := ZMod 2) A
    rw [eV, Fintype.card_fin] at this
    exact this
  have hMeq : M = V := Submodule.eq_of_le_of_finrank_le hMV (by omega)
  have hz : ∀ i, A i = 0 := fun i =>
    hsing _ (hMeq ▸ Submodule.subset_span ⟨i, rfl⟩) (hA i)
  have hbot : V = ⊥ := by
    rw [hV, Submodule.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    exact hz i
  rw [hMeq, hbot, finrank_bot] at hMr
  omega

end PEqualNP.Outside.L_lib_859

open PEqualNP.Outside.L_lib_859 in
theorem PEqualNP.Outside.L_lib_859 :
let F := ZMod 2
∀ (d : ℕ), 0 < d →
  ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
    Module.finrank F K = 2*d →
    ∃ (a : Fin (2*d+1) → K) (D : Fin (2*d+1) → (K →ₗ[F] K)),
      (∀ i, (a i)^(2^d+1) = 1) ∧
      (∀ i x, D i x = x^(2^d) + a i*x) ∧
      (∀ i, Module.finrank F (LinearMap.range (D i)) = d) ∧
      (∀ z : K, ∃! S : Finset (Fin (2*d+1)),
        Even S.card ∧ ∀ x : K, ∑ i ∈ S, D i x = z*x) ∧
      (∀ (s : ℕ) (A : Fin s → (K →ₗ[F] K)),
        (∀ i, Module.finrank F (LinearMap.range (A i)) ≤ d) →
        (∀ z : K, ∃ S : Finset (Fin s), ∀ x : K, ∑ i ∈ S, A i x = z*x) →
        2*d+1 ≤ s) := by
  intro F d hd K _ _ _ _ hK
  classical
  obtain ⟨g, hgN, hgli⟩ := diff_basis (K := K) d hd hK
  let a : Fin (2 * d + 1) → K := Fin.cons 1 g
  let D : Fin (2 * d + 1) → (K →ₗ[ZMod 2] K) := fun i => fr K d + LinearMap.mulLeft (ZMod 2) (a i)
  have ha : ∀ i, (a i) ^ (2 ^ d + 1) = 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [a]
    · simpa [a] using hgN j
  have hD : ∀ i x, D i x = x ^ (2 ^ d) + a i * x := fun i x => rfl
  have hr : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (D i)) = d :=
    fun i => rank_eq d hd hK (a i) (ha i) (D i) (hD i)
  refine ⟨a, D, ha, hD, hr, ?_, ?_⟩
  · intro z
    have L := l858 (2 * d) (by omega) K hK D (fun i => by rw [hr i]; omega)
    have hcov := L.1.mpr ⟨fun i => g i - 1, hgli, fun i x => by
      rw [hD, hD]
      simp only [a, Fin.cons_succ, Fin.cons_zero]
      ring⟩
    obtain ⟨hpar, huniq⟩ := L.2 hcov
    obtain ⟨S, hS, hSu⟩ := huniq z
    exact ⟨S, ⟨(hpar S).mp ⟨z, hS⟩, hS⟩, fun S' hS' => hSu S' hS'.2⟩
  · intro s A hA hc
    exact minimal (2 * d) (by omega) hK s A (fun i => by
      have h : Module.finrank (ZMod 2) (LinearMap.range (A i)) ≤ d := hA i
      omega) hc
