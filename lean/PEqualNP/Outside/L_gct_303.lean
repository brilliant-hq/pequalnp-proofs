import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_gct_303

private abbrev V := Fin 5 → ℂ

private def good (u : V) : Prop := (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0

private def pair (a b : ℂ) : V := ![a, -a, b, -b, 0]

private def reindex (p : Equiv.Perm (Fin 5)) : V ≃ₗ[ℂ] V where
  toFun u i := u (p i)
  invFun u i := u (p.symm i)
  left_inv u := by funext i; simp
  right_inv u := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma good_reindex (p : Equiv.Perm (Fin 5)) {u : V} (h : good u) :
    good (reindex p u) := by
  obtain ⟨hs, hc⟩ := h
  exact ⟨(Equiv.sum_comp p u).trans hs, (Equiv.sum_comp p (fun i => (u i)^3)).trans hc⟩

private lemma vec_reindex {u : V} {p : Equiv.Perm (Fin 5)} (i : Fin 5) :
    reindex p u i = u (p i) := rfl

private lemma pair_coords {u : V} (h₁ : u 0 + u 1 = 0) (h₂ : u 2 + u 3 = 0)
    (h₃ : u 4 = 0) : u = pair (u 0) (u 2) := by
  funext j
  fin_cases j
  · rfl
  · change u 1 = -u 0; linear_combination h₁
  · rfl
  · change u 3 = -u 2; linear_combination h₂
  · exact h₃

private lemma either_zero {S : Submodule ℂ V} (f g : V →ₗ[ℂ] ℂ)
    (h : ∀ u ∈ S, f u = 0 ∨ g u = 0) :
    (∀ u ∈ S, f u = 0) ∨ (∀ u ∈ S, g u = 0) := by
  by_cases hf : ∀ u ∈ S, f u = 0
  · exact Or.inl hf
  · push Not at hf
    obtain ⟨x, hx, hfx⟩ := hf
    refine Or.inr fun y hy => ?_
    by_contra hgy
    have hgx := (h x hx).resolve_left hfx
    have hfy := (h y hy).resolve_right hgy
    rcases h (x + y) (S.add_mem hx hy) with hxy | hxy
    · simp [hfy, hfx] at hxy
    · simp [hgx, hgy] at hxy

private lemma three_zero {S : Submodule ℂ V} (f g k : V →ₗ[ℂ] ℂ)
    (h : ∀ u ∈ S, f u * g u * k u = 0) :
    (∀ u ∈ S, f u = 0) ∨ (∀ u ∈ S, g u = 0) ∨ (∀ u ∈ S, k u = 0) := by
  by_cases hf : ∀ u ∈ S, f u = 0
  · exact Or.inl hf
  · push Not at hf
    obtain ⟨x, hx, hfx⟩ := hf
    refine Or.inr (either_zero g k fun y hy => mul_eq_zero.mp ?_)
    by_cases hfy : f y = 0
    -- Recover the constant term of the quadratic on the line through y in direction x.
    · have ht (t : ℂ) (ht₀ : t ≠ 0) :
          (g y + t * g x) * (k y + t * k x) = 0 := by
        have hh := h (y + t • x) (S.add_mem hy (S.smul_mem t hx))
        simp only [map_add, map_smul, smul_eq_mul, hfy, zero_add] at hh
        exact (mul_eq_zero.mp (show (t * f x) * ((g y + t * g x) *
            (k y + t * k x)) = 0 by rwa [← mul_assoc])).resolve_left (mul_ne_zero ht₀ hfx)
      linear_combination 3 * ht 1 one_ne_zero - 3 * ht 2 (by norm_num) + ht 3 (by norm_num)
    · exact (mul_eq_zero.mp (show f y * (g y * k y) = 0 by rw [← mul_assoc]; exact h y hy)).resolve_left hfy

private def coord (i : Fin 5) : V →ₗ[ℂ] ℂ := LinearMap.proj i

private def slice (U : Submodule ℂ V) : Submodule ℂ V := U ⊓ (coord 4).ker

private lemma slice_mem {u : V} {U : Submodule ℂ V} : u ∈ slice U ↔ u ∈ U ∧ u 4 = 0 := Iff.rfl

private lemma slicePair {U : Submodule ℂ V} (h : ∀ u ∈ U, good u) :
    ∃ p : Equiv.Perm (Fin 5), p 4 = 4 ∧
      ∀ u ∈ slice U, reindex p u = pair (reindex p u 0) (reindex p u 2) := by
  let f := coord 0 + coord 1
  let g := coord 0 + coord 2
  let k := coord 0 + coord 3
  have hprod (u : V) (hu : u ∈ slice U) : f u * g u * k u = 0 := by
    obtain ⟨hu, hz⟩ := slice_mem.mp hu
    obtain ⟨hs, hc⟩ := h u hu
    simp only [Fin.sum_univ_five, hz, zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero] at hs hc
    have h3 : u 3 = -(u 0 + u 1 + u 2) := by linear_combination hs
    rw [h3] at hc
    change (u 0 + u 1) * (u 0 + u 2) * (u 0 + u 3) = 0
    rw [h3]
    linear_combination (1/3 : ℂ) * hc
  rcases three_zero f g k hprod with hf | hg | hk
  · refine ⟨Equiv.refl _, rfl, fun u hu => ?_⟩
    obtain ⟨huU, hz⟩ := slice_mem.mp hu
    have hs := (h u huU).1
    simp only [Fin.sum_univ_five, hz, add_zero] at hs
    change u = pair (u 0) (u 2)
    have h01 : u 0 + u 1 = 0 := hf u hu
    exact pair_coords h01 (by linear_combination hs - h01) hz
  · let p := Equiv.swap (1 : Fin 5) 2
    have hp₄ : p 4 = 4 := by decide
    refine ⟨p, hp₄, fun u hu => ?_⟩
    obtain ⟨huU, hz⟩ := slice_mem.mp hu
    have hz' : reindex p u 4 = 0 := by rw [vec_reindex, hp₄, hz]
    have hs := (good_reindex p (h u huU)).1
    simp only [Fin.sum_univ_five, hz', add_zero] at hs
    have h01 : reindex p u 0 + reindex p u 1 = 0 := hg u hu
    exact pair_coords h01 (by linear_combination hs - h01) hz'
  · let p := Equiv.swap (1 : Fin 5) 3
    have hp₄ : p 4 = 4 := by decide
    refine ⟨p, hp₄, fun u hu => ?_⟩
    obtain ⟨huU, hz⟩ := slice_mem.mp hu
    have hz' : reindex p u 4 = 0 := by rw [vec_reindex, hp₄, hz]
    have hs := (good_reindex p (h u huU)).1
    simp only [Fin.sum_univ_five, hz', add_zero] at hs
    have h01 : reindex p u 0 + reindex p u 1 = 0 := hk u hu
    exact pair_coords h01 (by linear_combination hs - h01) hz'

private lemma nonzero_slice {U : Submodule ℂ V} (hU : 2 ≤ Module.finrank ℂ U) :
    ∃ w ∈ slice U, w ≠ 0 := by
  by_contra! hn
  let f := (coord 4).comp U.subtype
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (by
    apply bot_unique
    intro v hv
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact hn v.val (slice_mem.mpr ⟨v.property, LinearMap.mem_ker.mp hv⟩))
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hdim
  omega

private noncomputable def tablePerm (v : Fin 5 → Fin 5) (h : Function.Injective v) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective v ⟨h, Finite.injective_iff_surjective.mp h⟩

private noncomputable def swapPairs : Equiv.Perm (Fin 5) :=
  tablePerm ![2, 3, 0, 1, 4] (by decide)

private noncomputable def dropThird : Equiv.Perm (Fin 5) :=
  tablePerm ![0, 1, 3, 4, 2] (by decide)

private noncomputable def dropFourth : Equiv.Perm (Fin 5) :=
  tablePerm ![0, 1, 2, 4, 3] (by decide)

private noncomputable def rootOrder : Equiv.Perm (Fin 5) :=
  tablePerm ![4, 0, 2, 3, 1] (by decide)

private noncomputable def rootOrderSwap : Equiv.Perm (Fin 5) :=
  tablePerm ![4, 0, 3, 2, 1] (by decide)

private lemma reindex_trans (p q : Equiv.Perm (Fin 5)) (u : V) :
    reindex (q.trans p) u = reindex q (reindex p u) := rfl

private lemma swap_pair (a b : ℂ) : reindex swapPairs (pair a b) = pair b a := by
  funext i
  fin_cases i <;> rfl

private lemma pivotPair {U : Submodule ℂ V} (h : ∀ u ∈ U, good u)
    {w : V} (hw : w ∈ slice U) (hw₀ : w ≠ 0) :
    ∃ p : Equiv.Perm (Fin 5), p 4 = 4 ∧ reindex p w 0 ≠ 0 ∧
      ∀ u ∈ slice U, reindex p u = pair (reindex p u 0) (reindex p u 2) := by
  obtain ⟨p, hp, hpairs⟩ := slicePair h
  by_cases h0 : reindex p w 0 = 0
  · have h2 : reindex p w 2 ≠ 0 := by
      intro hz
      apply hw₀
      apply (reindex p).injective
      calc
        reindex p w = pair 0 0 := by rw [hpairs w hw, h0, hz]
        _ = reindex p 0 := by
          rw [map_zero]
          funext i
          fin_cases i <;> simp [pair]
    refine ⟨swapPairs.trans p, hp, h2, fun u hu => ?_⟩
    rw [reindex_trans, hpairs u hu, swap_pair]
    congr 1
  · exact ⟨p, hp, h0, hpairs⟩

private lemma map_reindex_mem {U : Submodule ℂ V} (p : Equiv.Perm (Fin 5)) (u : V) :
    reindex p u ∈ U.map (reindex p).toLinearMap ↔ u ∈ U := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact (reindex p).injective he ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

private lemma flatPair {U : Submodule ℂ V} (hU : 2 ≤ Module.finrank ℂ U)
    (hs : ∀ u ∈ U, u 4 = 0) (h : ∀ u ∈ U, good u) :
    ∃ p : Equiv.Perm (Fin 5), ∀ u : V, u ∈ U ↔ ∃ a b : ℂ, reindex p u = pair a b := by
  obtain ⟨p, -, hp⟩ := slicePair h
  have hall u (hu : u ∈ U) := hp u (slice_mem.mpr ⟨hu, hs u hu⟩)
  let f := ((coord 0).prod (coord 2)).comp ((reindex p).toLinearMap.comp U.subtype)
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply (reindex p).injective
    have h0 : reindex p u.val 0 = reindex p v.val 0 := congrArg Prod.fst huv
    have h2 : reindex p u.val 2 = reindex p v.val 2 := congrArg Prod.snd huv
    rw [hall u.val u.property, hall v.val v.property, h0, h2]
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have he := (LinearEquiv.ofInjective f hf).finrank_eq
    have hd := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_prod, Module.finrank_self] at hd ⊢
    omega
  refine ⟨p, fun u => ⟨fun hu => ⟨_, _, hall u hu⟩, ?_⟩⟩
  rintro ⟨a, b, he⟩
  obtain ⟨v, hv⟩ := hsurj (a, b)
  have h0 : reindex p v.val 0 = a := congrArg Prod.fst hv
  have h2 : reindex p v.val 2 = b := congrArg Prod.snd hv
  have huv : reindex p u = reindex p v.val := by
    rw [he, hall v.val v.property, h0, h2]
  exact (reindex p).injective huv ▸ v.property

private def liftVec (m n y : ℂ) : V := ![m, m, n + y, n - y, 1]

private lemma dropThirdVec : reindex dropThird (liftVec 0 (-1/2) (1/2)) = pair 0 (-1) := by
  funext i
  fin_cases i
  · change (0 : ℂ) = 0; rfl
  · change (0 : ℂ) = -0; exact neg_zero.symm
  · change (-1/2 : ℂ) - 1/2 = -1; norm_num
  · change (1 : ℂ) = -(-1); exact (neg_neg _).symm
  · change (-1/2 : ℂ) + 1/2 = 0; norm_num

private lemma dropFourthVec : reindex dropFourth (liftVec 0 (-1/2) (-1/2)) = pair 0 (-1) := by
  funext i
  fin_cases i
  · change (0 : ℂ) = 0; rfl
  · change (0 : ℂ) = -0; exact neg_zero.symm
  · change (-1/2 : ℂ) + (-1/2) = -1; norm_num
  · change (1 : ℂ) = -(-1); exact (neg_neg _).symm
  · change (-1/2 : ℂ) - (-1/2) = 0; norm_num

private lemma lift_coords (v : V) (h01 : v 0 = v 1) (h4 : v 4 = 1) :
    v = liftVec (v 0) ((v 2 + v 3) / 2) ((v 2 - v 3) / 2) := by
  funext i
  fin_cases i
  · rfl
  · exact h01.symm
  · change v 2 = (v 2 + v 3) / 2 + (v 2 - v 3) / 2; ring
  · change v 3 = (v 2 + v 3) / 2 - (v 2 - v 3) / 2; ring
  · exact h4

private lemma lift_eqs {m n y : ℂ} (hg : good (liftVec m n y)) :
    m + n = -1 / 2 ∧ 2 * m^3 + 2 * n^3 + 6 * n * y^2 + 1 = 0 := by
  obtain ⟨hs, hc⟩ := hg
  simp only [Fin.sum_univ_five] at hs hc
  change m + m + (n + y) + (n - y) + 1 = 0 at hs
  change m^3 + m^3 + (n + y)^3 + (n - y)^3 + 1^3 = 0 at hc
  constructor
  · linear_combination (1/2 : ℂ) * hs
  · linear_combination hc

private lemma lift_coeff {W : Submodule ℂ V} (hg : ∀ u ∈ W, good u)
    {m n y a b : ℂ} (hl : liftVec m n y ∈ W) (hw : pair a b ∈ W) :
    m*a^2 + n*b^2 = 0 ∧ n*y*b = 0 := by
  -- Evaluation at zero and at plus or minus one isolates the mixed coefficients.
  have he := (lift_eqs (hg _ hl)).2
  have hp := (hg _ (W.add_mem hl hw)).2
  have hn := (hg _ (W.sub_mem hl hw)).2
  rw [Fin.sum_univ_five] at hp hn
  change (m+a)^3 + (m + (-a))^3 + (n+y+b)^3 + (n-y + (-b))^3 + (1+0)^3 = 0 at hp
  change (m-a)^3 + (m - (-a))^3 + (n+y-b)^3 + (n-y - (-b))^3 + (1-0)^3 = 0 at hn
  constructor
  · linear_combination (1/12 : ℂ) * hp + (1/12 : ℂ) * hn - (1/6 : ℂ) * he
  · linear_combination (1/24 : ℂ) * hp - (1/24 : ℂ) * hn

private lemma liftSpan {W : Submodule ℂ V} (hg : ∀ u ∈ W, good u)
    (hs : ∀ u ∈ W, u 4 = 0 → u = pair (u 0) (u 2))
    {a b m n y : ℂ} (ha : a ≠ 0) (hn : n ≠ 0)
    (hw : pair a b ∈ W) (hl : liftVec m n y ∈ W) :
    ∀ u : V, u ∈ W ↔ ∃ c d : ℂ, u = c • pair a b + d • liftVec m n y := by
  -- The quadratic forces a slice vector with zero first coordinate to vanish.
  have hline (v : V) (hv : v ∈ W) (hv₄ : v 4 = 0) : v = (v 0 / a) • pair a b := by
    let x := v - (v 0 / a) • pair a b
    have hx : x ∈ W := W.sub_mem hv (W.smul_mem _ hw)
    have hx0 : x 0 = 0 := by
      change v 0 - (v 0 / a) * a = 0
      rw [div_mul_cancel₀ _ ha, sub_self]
    have hx4 : x 4 = 0 := by change v 4 - (v 0 / a) * 0 = 0; simp [hv₄]
    have hxp : x = pair 0 (x 2) := by simpa [hx0] using hs x hx hx4
    have hq := (lift_coeff hg hl (hxp ▸ hx)).1
    have hx2 : x 2 = 0 := by
      simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add] at hq
      by_contra hx₂
      exact (pow_ne_zero 2 hx₂) ((mul_eq_zero.mp hq).resolve_left hn)
    have hzero : x = 0 := by
      rw [hxp, hx2]
      funext j
      fin_cases j <;> simp [pair]
    exact sub_eq_zero.mp hzero
  intro u
  constructor
  · intro hu
    let v := u - u 4 • liftVec m n y
    have hv₄ : v 4 = 0 := by change u 4 - u 4 * 1 = 0; simp
    have he := hline v (W.sub_mem hu (W.smul_mem _ hl)) hv₄
    exact ⟨v 0 / a, u 4, sub_eq_iff_eq_add.mp he⟩
  · rintro ⟨c, d, rfl⟩
    exact W.add_mem (W.smul_mem c hw) (W.smul_mem d hl)

private lemma twoGenerators {U : Submodule ℂ V} (hU : 2 ≤ Module.finrank ℂ U)
    (h : ∀ u ∈ U, good u) (hex : ∃ u ∈ U, u 4 ≠ 0) :
    ∃ (p : Equiv.Perm (Fin 5)) (a b m n y : ℂ),
      a ≠ 0 ∧ n ≠ 0 ∧ m+n = -1/2 ∧ 2*m^3+2*n^3+6*n*y^2+1 = 0 ∧
      m*a^2+n*b^2 = 0 ∧ n*y*b = 0 ∧
      ∀ u : V, u ∈ U ↔ ∃ c d : ℂ, reindex p u = c • pair a b + d • liftVec m n y := by
  obtain ⟨w, hw, hw₀⟩ := nonzero_slice hU
  obtain ⟨p, hp, ha, hpairs⟩ := pivotPair h hw hw₀
  let W := U.map (reindex p).toLinearMap
  have hg : ∀ u ∈ W, good u := by
    rintro _ ⟨v, hv, rfl⟩
    exact good_reindex p (h v hv)
  have hs : ∀ u ∈ W, u 4 = 0 → u = pair (u 0) (u 2) := by
    rintro _ ⟨v, hv, rfl⟩ hz
    exact hpairs v (slice_mem.mpr ⟨hv, by simpa [vec_reindex, hp] using hz⟩)
  obtain ⟨r, hr, hr₀⟩ := hex
  let a := reindex p w 0
  let b := reindex p w 2
  have hwW : pair a b ∈ W := by
    rw [← hpairs w hw]
    exact (map_reindex_mem p w).mpr (slice_mem.mp hw).1
  let r' := (r 4)⁻¹ • reindex p r
  have hrW : r' ∈ W := W.smul_mem _ ((map_reindex_mem p r).mpr hr)
  have hr4 : r' 4 = 1 := by change (r 4)⁻¹ * r (p 4) = 1; rw [hp, inv_mul_cancel₀ hr₀]
  let d := (r' 0 - r' 1) / (2 * a)
  let l := r' - d • pair a b
  have hlW : l ∈ W := W.sub_mem hrW (W.smul_mem _ hwW)
  have hl01 : l 0 = l 1 := by
    change r' 0 - d*a = r' 1 - d*(-a)
    have hd : d * (2*a) = r' 0 - r' 1 := div_mul_cancel₀ _ (mul_ne_zero (by norm_num) ha)
    linear_combination -hd
  have hl4 : l 4 = 1 := by change r' 4 - d*0 = 1; simp [hr4]
  obtain ⟨m, n, y, he⟩ : ∃ m n y : ℂ, l = liftVec m n y :=
    ⟨_, _, _, lift_coords l hl01 hl4⟩
  have hl : liftVec m n y ∈ W := he ▸ hlW
  obtain ⟨hsum, hcub⟩ := lift_eqs (hg _ hl)
  obtain ⟨hq, hy⟩ := lift_coeff hg hl hwW
  have hn : n ≠ 0 := by
    intro h0
    have hm : m ≠ 0 := by
      intro h0'
      norm_num [h0, h0'] at hsum
    exact (mul_ne_zero hm (pow_ne_zero 2 ha)) (by simpa only [h0, zero_mul, add_zero] using hq)
  refine ⟨p, a, b, m, n, y, ha, hn, hsum, hcub, hq, hy, fun u => ?_⟩
  exact (map_reindex_mem p u).symm.trans (liftSpan hg hs ha hn hwW hl _)

private lemma span_reindex {U : Submodule ℂ V} {p : Equiv.Perm (Fin 5)} {w l : V}
    (h : ∀ u : V, u ∈ U ↔ ∃ c d : ℂ, reindex p u = c • w + d • l)
    (q : Equiv.Perm (Fin 5)) (u : V) :
    u ∈ U ↔ ∃ c d : ℂ, reindex (q.trans p) u = c • reindex q w + d • reindex q l := by
  rw [h, reindex_trans]
  simp only [← map_smul, ← map_add, (reindex q).injective.eq_iff]

private lemma fourierLift {m n a b : ℂ} (hs : m + n = -1 / 2) (hp : m * n = -1 / 4)
    (ha : a ≠ 0) (hr : b = 2 * m * a) :
    ∃ z : ℂ, IsPrimitiveRoot z 5 ∧ ∀ v : Fin 5 → ℂ,
      (∃ c d : ℂ, v = c • (![0, a, b, -b, -a] : Fin 5 → ℂ) +
        d • (![1, m, n, n, m] : Fin 5 → ℂ)) ↔
      ∃ s t : ℂ, ∀ j : Fin 5, v j = s * z ^ j.val + t * z ^ (4 * j.val) := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (m ^ 2 - 1) (n := 2) (by decide)
  let z := m + w
  have hq : z ^ 2 - 2 * m * z + 1 = 0 := by
    dsimp [z]
    linear_combination hw
  have hm : 4 * m ^ 2 + 2 * m - 1 = 0 := by
    linear_combination 4 * m * hs - 4 * hp
  have hc : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
    linear_combination (z ^ 2 + (1 + 2 * m) * z + 1) * hq + z ^ 2 * hm
  have hz5 : z ^ 5 = 1 := by
    linear_combination (z - 1) * hc
  have hz0 : z ≠ 0 := by
    intro h
    norm_num [h] at hz5
  have hz1 : z ≠ 1 := by
    intro h
    norm_num [h] at hc
  have hz : IsPrimitiveRoot z 5 :=
    isPrimitiveRoot_of_mem_nthRootsFinset (by decide)
      ((Polynomial.mem_nthRootsFinset (by decide) 1).2 hz5) hz1
  have hgap : z - z ^ 4 ≠ 0 := by
    intro h
    have hh : z ^ 3 = 1 := by
      apply mul_left_cancel₀ hz0
      linear_combination -h
    have hdiv := hz.dvd_of_pow_eq_one 3 hh
    norm_num at hdiv
  have hsum₁ : z + z ^ 4 = 2 * m := by
    linear_combination z ^ 4 * hq - (z - 2 * m) * hz5
  have hsum₂ : z ^ 2 + z ^ 3 = 2 * n := by
    linear_combination hc - hsum₁ - 2 * hs
  have hdiff₂ : z ^ 2 - z ^ 3 = 2 * m * (z - z ^ 4) := by
    linear_combination (1 - z ^ 3) * hq + hz5
  have hz8 : z ^ 8 = z ^ 3 := by linear_combination z ^ 3 * hz5
  have hz12 : z ^ 12 = z ^ 2 := by linear_combination (z ^ 7 + z ^ 2) * hz5
  have hz16 : z ^ 16 = z := by linear_combination (z ^ 11 + z ^ 6 + z) * hz5
  let A : Fin 5 → ℂ := ![0, a, b, -b, -a]
  let B : Fin 5 → ℂ := ![1, m, n, n, m]
  let p (j : Fin 5) := z ^ j.val
  let q (j : Fin 5) := z ^ (4 * j.val)
  have hcos (j : Fin 5) : 2 * B j = p j + q j := by
    fin_cases j <;> norm_num [B, p, q, Matrix.cons_val_zero, Matrix.cons_val_succ,
      hz8, hz12, hz16] <;> first | linear_combination -hsum₁ | linear_combination -hsum₂
  have hsin (j : Fin 5) : (z - z ^ 4) * A j = a * (p j - q j) := by
    fin_cases j <;> norm_num [A, p, q, Matrix.cons_val_zero, Matrix.cons_val_succ,
      hz8, hz12, hz16, hr] <;> first | ring1 | linear_combination -a * hdiff₂ |
      linear_combination a * hdiff₂
  let k := a / (z - z ^ 4)
  have hk : (z - z ^ 4) * k = a := by
    rw [mul_comm, div_mul_cancel₀ _ hgap]
  have hA (j : Fin 5) : A j = k * (p j - q j) := by
    apply mul_left_cancel₀ hgap
    linear_combination hsin j - (p j - q j) * hk
  let l := (z - z ^ 4) / a
  have hl : a * l = z - z ^ 4 := by
    rw [mul_comm, div_mul_cancel₀ _ ha]
  have hP (j : Fin 5) : p j - q j = l * A j := by
    apply mul_left_cancel₀ ha
    linear_combination -hsin j - A j * hl
  refine ⟨z, hz, fun v => ?_⟩
  change (∃ c d : ℂ, v = c • A + d • B) ↔
    ∃ s t : ℂ, ∀ j : Fin 5, v j = s * p j + t * q j
  constructor
  · rintro ⟨c, d, rfl⟩
    refine ⟨c * k + d / 2, d / 2 - c * k, fun j => ?_⟩
    change c * A j + d * B j = _
    linear_combination c * hA j + d / 2 * hcos j
  · rintro ⟨s, t, hv⟩
    refine ⟨(s - t) * l / 2, s + t, funext fun j => ?_⟩
    change v j = (s - t) * l / 2 * A j + (s + t) * B j
    rw [hv]
    linear_combination (s - t) / 2 * hP j - (s + t) / 2 * hcos j

private lemma pairWitness {U : Submodule ℂ V} {p : Equiv.Perm (Fin 5)}
    (h : ∀ u : V, u ∈ U ↔ ∃ a b : ℂ, reindex p u = pair a b) :
    ∀ u : V, u ∈ U ↔ ∃ a b : ℂ, ∀ j : Fin 5,
      u (p j) = (![a, -a, b, -b, 0] : V) j := by
  intro u
  rw [h]
  constructor
  · rintro ⟨a, b, he⟩
    exact ⟨a, b, congrFun he⟩
  · rintro ⟨a, b, he⟩
    exact ⟨a, b, funext he⟩

private lemma spanPair {U : Submodule ℂ V} {p : Equiv.Perm (Fin 5)} {a : ℂ} (ha : a ≠ 0)
    (h : ∀ u : V, u ∈ U ↔ ∃ c d : ℂ, reindex p u = c • pair a 0 + d • pair 0 (-1)) :
    ∀ u : V, u ∈ U ↔ ∃ s t : ℂ, reindex p u = pair s t := by
  have hvec (c d : ℂ) : c • pair a 0 + d • pair 0 (-1) = pair (c*a) (-d) := by
    funext j
    fin_cases j <;> simp [pair, Pi.add_apply, smul_eq_mul]
  intro u
  rw [h]
  constructor
  · rintro ⟨c, d, hu⟩
    exact ⟨c*a, -d, hu.trans (hvec c d)⟩
  · rintro ⟨s, t, hu⟩
    refine ⟨s/a, -t, hu.trans ?_⟩
    rw [hvec, div_mul_cancel₀ _ ha, neg_neg]

private lemma forwardModes (U : Submodule ℂ V) (hU : 2 ≤ Module.finrank ℂ U)
    (h : ∀ u ∈ U, good u) :
    ∃ π : Equiv.Perm (Fin 5),
      (∀ u : V, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : V) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : V, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val)) := by
  by_cases hf : ∀ u ∈ U, u 4 = 0
  · obtain ⟨p, hp⟩ := flatPair hU hf h
    exact ⟨p, Or.inl (pairWitness hp)⟩
  push Not at hf
  obtain ⟨p, a, b, m, n, y, ha, hn, hsum, hcub, hq, hy, hspan⟩ := twoGenerators hU h hf
  by_cases hb : b = 0
  · subst b
    have hm : m = 0 := by
      have he : m * a^2 = 0 := by simpa using hq
      exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ ha)
    subst m
    have hn' : n = -1/2 := by simpa using hsum
    subst n
    have hsq : (y - 1/2) * (y + 1/2) = 0 := by
      linear_combination -(1/3 : ℂ) * hcub
    obtain ⟨q, hw, hl⟩ : ∃ q : Equiv.Perm (Fin 5),
        reindex q (pair a 0) = pair a 0 ∧ reindex q (liftVec 0 (-1/2) y) = pair 0 (-1) := by
      rcases mul_eq_zero.mp hsq with hp | hm
      · have hy' := sub_eq_zero.mp hp
        refine ⟨dropThird, ?_, ?_⟩
        · funext i; fin_cases i <;> rfl
        · simpa only [hy'] using dropThirdVec
      · have hy' : y = -1/2 := by linear_combination hm
        refine ⟨dropFourth, ?_, ?_⟩
        · funext i; fin_cases i <;> rfl
        · simpa only [hy'] using dropFourthVec
    refine ⟨q.trans p, Or.inl (pairWitness (spanPair ha ?_))⟩
    intro u
    simpa only [hw, hl] using span_reindex hspan q u
  · have hy' : y = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hb)).resolve_left hn
    subst y
    have hp : m*n = -1/4 := by
      linear_combination (1/3 : ℂ) * hcub -
        (1/3 : ℂ) * (2*(m+n)^2 - (m+n) + 1/2 - 6*m*n) * hsum
    have hsign : (b - 2*m*a) * (b + 2*m*a) = 0 := by
      apply (mul_eq_zero.mp (show n * ((b - 2*m*a) * (b + 2*m*a)) = 0 by
        linear_combination hq - 4*m*a^2*hp)).resolve_left hn
    obtain ⟨q, B, hr, hw, hl⟩ : ∃ (q : Equiv.Perm (Fin 5)) (B : ℂ), B = 2*m*a ∧
        reindex q (pair a b) = (![0,a,B,-B,-a] : V) ∧
        reindex q (liftVec m n 0) = (![1,m,n,n,m] : V) := by
      rcases mul_eq_zero.mp hsign with hc | hc
      · refine ⟨rootOrder, b, sub_eq_zero.mp hc, ?_, ?_⟩
        · funext i; fin_cases i <;> rfl
        · funext i; fin_cases i <;> first | rfl | exact add_zero _ | exact sub_zero _
      · refine ⟨rootOrderSwap, -b, by linear_combination -hc, ?_, ?_⟩
        · funext i; fin_cases i <;> first | rfl | exact (neg_neg _).symm
        · funext i; fin_cases i <;> first | rfl | exact add_zero _ | exact sub_zero _
    obtain ⟨z, hz, hmode⟩ := fourierLift hsum hp ha hr
    refine ⟨q.trans p, Or.inr ⟨z, hz, ?_⟩⟩
    intro u
    exact ((span_reindex hspan q u).trans (by rw [hw, hl]; exact hmode _))

private lemma reverseModes (U : Submodule ℂ (Fin 5 → ℂ)) :
    (∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧ ∀ u : Fin 5 → ℂ, u ∈ U ↔
        ∃ s t : ℂ, ∀ j : Fin 5, u (π j) = s * z^j.val + t * z^(4*j.val))) →
    ∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0 := by
  rintro ⟨π, h | ⟨z, hz, h⟩⟩ u hu <;>
    obtain ⟨s, t, hst⟩ := (h u).mp hu <;>
    rw [← Equiv.sum_comp π u, ← Equiv.sum_comp π (fun j => (u j)^3)] <;>
    simp only [hst]
  · (constructor <;> simp [Fin.sum_univ_succ]); ring
  · have hsum (k : ℕ) (hk : ¬ 5 ∣ k) : ∑ j : Fin 5, z^(k*j.val) = 0 := by
      simp only [pow_mul]
      rw [Fin.sum_univ_eq_sum_range]
      have hpow : (z^k)^5 = 1 := by
        rw [← pow_mul, Nat.mul_comm k 5, pow_mul, hz.pow_eq_one, one_pow]
      have hgeom := geom_sum_mul (z^k) 5
      rw [hpow, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right
        (sub_ne_zero.mpr (fun he => hk ((hz.pow_eq_one_iff_dvd k).mp he)))
    have hcube (j : Fin 5) :
        (s * z^j.val + t * z^(4*j.val))^3 =
          s^3 * z^(3*j.val) + (3*s^2*t) * z^(6*j.val) +
          (3*s*t^2) * z^(9*j.val) + t^3 * z^(12*j.val) := by
      simp only [Nat.mul_comm _ j.val, pow_mul]
      ring
    constructor
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hsum₁ : ∑ j : Fin 5, z^j.val = 0 := by
        simpa only [one_mul] using hsum 1 (by decide)
      simp only [hsum₁, hsum 4 (by decide), mul_zero, add_zero]
    · simp only [hcube, Finset.sum_add_distrib, ← Finset.mul_sum,
        hsum 3 (by decide), hsum 6 (by decide), hsum 9 (by decide),
        hsum 12 (by decide), mul_zero, add_zero]

end PEqualNP.Outside.L_gct_303

theorem PEqualNP.Outside.L_gct_303 :
    ∀ U : Submodule ℂ (Fin 5 → ℂ), 2 ≤ Module.finrank ℂ U →
      ((∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0) ↔
        ∃ π : Equiv.Perm (Fin 5),
          (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
            u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
          (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
            ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
              u (π j) = s * z^j.val + t * z^(4*j.val))) := by
  intro U hU
  exact ⟨PEqualNP.Outside.L_gct_303.forwardModes U hU, PEqualNP.Outside.L_gct_303.reverseModes U⟩
