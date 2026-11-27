import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_798

open Finset Module

abbrev F2 := ZMod 2

theorem two_vals (t : F2) : t = 0 ∨ t = 1 := by
  revert t; decide

/-- Pivot coordinates: a subspace is determined by at most its dimension coordinates. -/
theorem pivots {m : ℕ} (W : Submodule F2 (Fin m → F2)) :
    ∃ R : Finset (Fin m), R.card ≤ finrank F2 W ∧
      ∀ w ∈ W, (∀ j ∈ R, w j = 0) → w = 0 := by
  classical
  let c : Fin m → Module.Dual F2 W := fun j => (LinearMap.proj j).comp W.subtype
  obtain ⟨κ, e, hinj, hspan, hli⟩ := exists_linearIndependent' F2 c
  haveI : Fintype κ := Fintype.ofInjective e hinj
  refine ⟨Finset.univ.image e, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have := hli.fintype_card_le_finrank
    rwa [Subspace.dual_finrank_eq] at this
  · intro w hw h0
    let ww : W := ⟨w, hw⟩
    have hle : Submodule.span F2 (Set.range (c ∘ e)) ≤
        LinearMap.ker (Module.Dual.eval F2 W ww) := by
      rw [Submodule.span_le]
      rintro f ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, Function.comp_apply]
      exact h0 (e i) (Finset.mem_image_of_mem e (Finset.mem_univ i))
    funext j
    have hj : c j ∈ Submodule.span F2 (Set.range (c ∘ e)) := by
      rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    have := hle hj
    simpa [c, ww] using this

def ind {m : ℕ} (S : Finset (Fin m)) : Fin m → F2 := fun j => if j ∈ S then 1 else 0

theorem main (k m a h : ℕ) (v : Fin m → (Fin k → F2))
    (hv : ∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a+1)*h → (∑ j ∈ S, v j) ≠ 0)
    (p : Fin a → (Fin k → F2)) :
    ∃ R : Finset (Fin m), R.card ≤ a ∧
      ∀ S : Finset (Fin m), S.Nonempty → Disjoint S R → S.card ≤ h →
        ∀ z : Fin a → F2, (∑ j ∈ S, v j) ≠ ∑ i : Fin a, z i • p i := by
  classical
  let P : Submodule F2 (Fin k → F2) := Submodule.span F2 (Set.range p)
  let Φ : (Fin m → F2) →ₗ[F2] (Fin k → F2) :=
    ∑ j : Fin m, (LinearMap.proj j : (Fin m → F2) →ₗ[F2] F2).smulRight (v j)
  have hΦ : ∀ x, Φ x = ∑ j, x j • v j := by
    intro x; simp [Φ]
  have hΦsupp : ∀ x, Φ x = ∑ j ∈ Finset.univ.filter (fun j => x j ≠ 0), v j := by
    intro x
    rw [hΦ, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rcases two_vals (x j) with h0 | h1
    · simp [h0]
    · simp [h1]
  have hΦind : ∀ S, Φ (ind S) = ∑ j ∈ S, v j := by
    intro S
    rw [hΦ]
    simp [ind, ite_smul, Finset.sum_ite_mem]
  let bad : Finset (Finset (Fin m)) := Finset.univ.filter
    (fun S => S.Nonempty ∧ S.card ≤ h ∧ (∑ j ∈ S, v j) ∈ P)
  let g : bad → (Fin m → F2) := fun S => ind S.val
  let W : Submodule F2 (Fin m → F2) := Submodule.span F2 (Set.range g)
  have hdim : finrank F2 W ≤ a := by
    obtain ⟨κ, e, hinj, hspan, hli⟩ := exists_linearIndependent' F2 g
    haveI : Fintype κ := Fintype.ofInjective e hinj
    have hW : finrank F2 W = Fintype.card κ := by
      show finrank F2 (Submodule.span F2 (Set.range g)) = _
      rw [← hspan]; exact finrank_span_eq_card hli
    rw [hW]
    by_contra hlt
    push_neg at hlt
    obtain ⟨κ0, -, hκ0⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset κ))
      (n := a + 1) (by rw [Finset.card_univ]; omega)
    have hli0 : LinearIndependent F2 ((g ∘ e) ∘ (Subtype.val : κ0 → κ)) :=
      hli.comp _ Subtype.val_injective
    let fam : κ0 → (Fin k → F2) := fun i => Φ (g (e i.val))
    have hnot : ¬ LinearIndependent F2 fam := by
      intro hl
      have h1 := finrank_span_eq_card hl
      have h2 : Submodule.span F2 (Set.range fam) ≤ P := by
        rw [Submodule.span_le]
        rintro y ⟨i, rfl⟩
        have hb := (e i.val).property
        simp only [bad, Finset.mem_filter] at hb
        simp only [fam, g, hΦind]
        exact hb.2.2.2
      have h3 := Submodule.finrank_mono h2
      have h4 : finrank F2 P ≤ a := by
        have := finrank_range_le_card (R := F2) p
        simpa [Set.finrank, P] using this
      rw [Fintype.card_coe] at h1
      omega
    obtain ⟨c, hc0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnot
    let w : Fin m → F2 := ∑ i : κ0, c i • g (e i.val)
    have hΦw : Φ w = 0 := by
      simp only [w, map_sum, map_smul]
      exact hc0
    have hw0 : w ≠ 0 := by
      intro hw
      have := (Fintype.linearIndependent_iff.mp hli0) c hw i0
      exact hi0 this
    let T : Finset (Fin m) := Finset.univ.filter (fun j => w j ≠ 0)
    have hTsub : T ⊆ κ0.attach.biUnion (fun i => (e i.val).val) := by
      intro j hj
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hn
      apply hj
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, not_exists] at hn
      simp only [w, Finset.sum_apply, Pi.smul_apply, g, ind]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp [hn i]
    have hTcard : T.card ≤ (a+1)*h := by
      refine (Finset.card_le_card hTsub).trans ((Finset.card_biUnion_le).trans ?_)
      have : ∀ i ∈ κ0.attach, ((e i.val).val).card ≤ h := by
        intro i _
        have hb := (e i.val).property
        simp only [bad, Finset.mem_filter] at hb
        exact hb.2.2.1
      refine (Finset.sum_le_card_nsmul _ _ h this).trans ?_
      simp [hκ0]
    have hTne : T.Nonempty := by
      by_contra hn
      apply hw0
      funext j
      by_contra hj
      exact hn ⟨j, by simpa [T] using hj⟩
    apply hv T hTne hTcard
    rw [← hΦw, hΦsupp]
  obtain ⟨R, hR, hRW⟩ := pivots W
  refine ⟨R, hR.trans hdim, ?_⟩
  intro S hS hdisj hcard z hz
  have hSbad : S ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hS, hcard, ?_⟩
    rw [hz]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  have hmem : ind S ∈ W := Submodule.subset_span ⟨⟨S, hSbad⟩, rfl⟩
  have h0 := hRW _ hmem (by
    intro j hj
    have : j ∉ S := fun hjS => Finset.disjoint_left.mp hdisj hjS hj
    simp [ind, this])
  obtain ⟨j, hj⟩ := hS
  have := congrFun h0 j
  simp [ind, hj] at this

end PEqualNP.Outside.L_lib_798

open PEqualNP.Outside.L_lib_798 in
theorem PEqualNP.Outside.L_lib_798 : ∀ (k m a h : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m → V,
    (∀ S : Finset (Fin m), S.Nonempty → S.card ≤ (a+1)*h →
      (∑ j ∈ S, v j) ≠ 0) →
    ∀ p : Fin a → V,
      ∃ R : Finset (Fin m), R.card ≤ a ∧
        ∀ S : Finset (Fin m), S.Nonempty → Disjoint S R → S.card ≤ h →
          ∀ z : Fin a → F, (∑ j ∈ S, v j) ≠ ∑ i : Fin a, z i • p i := by
  intro k m a h
  exact fun v hv p => main k m a h v hv p
