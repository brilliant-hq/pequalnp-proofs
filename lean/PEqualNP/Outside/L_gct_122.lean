import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

namespace PEqualNP.Outside.L_gct_122

open Module Finset PEqualNP.Gct.Helpers

def QuarticIso {ι : Type} [Fintype ι] (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ w ∈ W, ∀ z ∈ W, ∑ i, u i * v i * w i * z i = 0)

theorem sum_eq_zero_of_mem_sq {ι : Type} [Fintype ι] {W : Submodule ℂ (ι → ℂ)}
    (hW : QuarticIso W) : ∀ q ∈ W * W, ∑ i, q i = 0 := by
  intro q hq
  refine Submodule.mul_induction_on hq ?_ ?_
  · intro u hu v hv
    simpa only [Pi.mul_apply] using hW.1 u hu v hv
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

theorem sq_perp_sq {ι : Type} [Fintype ι] {W : Submodule ℂ (ι → ℂ)}
    (hW : QuarticIso W) : ∀ q1 ∈ W * W, ∀ q2 ∈ W * W, ∑ i, q1 i * q2 i = 0 := by
  intro q1 hq1
  refine Submodule.mul_induction_on hq1 ?_ ?_
  · intro u hu v hv q2 hq2
    refine Submodule.mul_induction_on hq2 ?_ ?_
    · intro w hw z hz
      have h4 := hW.2 u hu v hv w hw z hz
      refine (sum_congr rfl fun i _ => ?_).trans h4
      simp only [Pi.mul_apply]
      ring
    · intro a b ha hb
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha, hb, add_zero]
  · intro a b ha hb q2 hq2
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha q2 hq2, hb q2 hq2, add_zero]

theorem sq_sup_one_perp {ι : Type} [Fintype ι] {W : Submodule ℂ (ι → ℂ)}
    (hW : QuarticIso W) :
    ∀ v ∈ (W * W) ⊔ Submodule.span ℂ {(1 : ι → ℂ)}, ∀ z ∈ W * W, ∑ i, v i * z i = 0 := by
  intro v hv z hz
  obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have h1 := sq_perp_sq hW q hq z hz
  have h2 := sum_eq_zero_of_mem_sq hW z hz
  calc ∑ i, (q + c • (1 : ι → ℂ)) i * z i
      = ∑ i, q i * z i + c * ∑ i, z i := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        ring
    _ = 0 := by rw [h1, h2, mul_zero, add_zero]

theorem restr_quarticIso {ι : Type} [Fintype ι] {W : Submodule ℂ (ι → ℂ)}
    (hW : QuarticIso W) {p : ι → ℂ} (hp : p ∈ stab (W * W))
    (hp01 : ∀ k, p k = 0 ∨ p k = 1) : QuarticIso (W.map (restr p)) := by
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have hpuv : p * (u * v) ∈ W * W := hp (u * v) (Submodule.mul_mem_mul hu hv)
    simpa only [Pi.mul_apply] using sum_eq_zero_of_mem_sq hW (p * (u * v)) hpuv
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * w k * z k)]
    have hpuv : p * (u * v) ∈ W * W := hp (u * v) (Submodule.mul_mem_mul hu hv)
    have hwz : w * z ∈ W * W := Submodule.mul_mem_mul hw hz
    have h0 := sq_perp_sq hW (p * (u * v)) hpuv (w * z) hwz
    refine (sum_congr rfl fun k _ => ?_).trans h0
    simp only [Pi.mul_apply]
    ring

theorem quartic_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), QuarticIso W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  have hd_ne : finrank ℂ W ≠ 0 := fun h0 => hW0 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  set Q := W * W with hQdef
  have hone : (1 : ι → ℂ) ∉ Q := by
    intro h
    have := sum_eq_zero_of_mem_sq hW 1 h
    simp only [Pi.one_apply, sum_const, card_univ, nsmul_eq_mul, mul_one] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab Q, ∀ j k, x j = x k
  · have hSt : finrank ℂ (stab Q) ≤ 1 := by
      have : stab Q ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hU : finrank ℂ ↥(Q ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ Q + 1 := by
      have hinf : Q ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxQ, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := Q.smul_mem c⁻¹ hxQ
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq Q (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hk := hK ι W W (stab Q) hW0 hW0 (fun x => Iff.rfl)
    have hp := perp_bound (Q ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) Q (sq_sup_one_perp hW)
    rw [hU, hcard] at hp
    change finrank ℂ W + finrank ℂ W ≤ finrank ℂ Q + finrank ℂ (stab Q) at hk
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab Q := (stab Q).sub_mem (one_mem_stab Q) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_quarticIso hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_quarticIso hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

end PEqualNP.Outside.L_gct_122

open PEqualNP.Outside.L_gct_122 PEqualNP.Gct.Helpers Finset in
theorem PEqualNP.Outside.L_gct_122 : ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
  intro m X h2 h4
  have hQ : ∀ u ∈ X, ∀ v ∈ X, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (X.add_mem hu hv), h2 u hu, h2 v hv, ← mul_sum] at key
    simpa using key
  have hF : ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ∀ z ∈ X, ∑ i, u i * v i * w i * z i = 0 := by
    intro u hu v hv w hw z hz
    have h_uv := X.add_mem hu hv
    have h_uw := X.add_mem hu hw
    have h_uz := X.add_mem hu hz
    have h_vw := X.add_mem hv hw
    have h_vz := X.add_mem hv hz
    have h_wz := X.add_mem hw hz
    have h_uvw := X.add_mem h_uv hw
    have h_uvz := X.add_mem h_uv hz
    have h_uwz := X.add_mem h_uw hz
    have h_vwz := X.add_mem h_vw hz
    have h_uvwz := X.add_mem h_uvw hz
    have key : ∑ i, (24 : ℂ) * (u i * v i * w i * z i) =
        (∑ i, (u + v + w + z) i ^ 4)
        - (∑ i, (u + v + w) i ^ 4) - (∑ i, (u + v + z) i ^ 4)
        - (∑ i, (u + w + z) i ^ 4) - (∑ i, (v + w + z) i ^ 4)
        + (∑ i, (u + v) i ^ 4) + (∑ i, (u + w) i ^ 4) + (∑ i, (u + z) i ^ 4)
        + (∑ i, (v + w) i ^ 4) + (∑ i, (v + z) i ^ 4) + (∑ i, (w + z) i ^ 4)
        - (∑ i, u i ^ 4) - (∑ i, v i ^ 4) - (∑ i, w i ^ 4) - (∑ i, z i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h4 _ h_uvwz, h4 _ h_uvw, h4 _ h_uvz, h4 _ h_uwz, h4 _ h_vwz,
        h4 _ h_uv, h4 _ h_uw, h4 _ h_uz, h4 _ h_vw, h4 _ h_vz, h4 _ h_wz,
        h4 u hu, h4 v hv, h4 w hw, h4 z hz, ← mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact quartic_general (kneserFor_of_fin PEqualNP.Gct.L065) m (Fin m) (Fintype.card_fin m) X ⟨hQ, hF⟩
