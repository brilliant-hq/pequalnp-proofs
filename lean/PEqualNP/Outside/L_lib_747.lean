import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_747

theorem dual_one_on {E K : Type} [Field E] [Field K] [Algebra E K]
    (s : Set K) (p : K) (hp : p ∈ s) (h0 : (0 : K) ∉ affineSpan E s) :
    ∃ g : K →ₗ[E] E, ∀ a ∈ s, g a = 1 := by
  have hpv : p ∉ vectorSpan E s := by
    intro hv
    apply h0
    have hneg : -p ∈ (affineSpan E s).direction := by
      rw [direction_affineSpan]; exact Submodule.neg_mem _ hv
    have := AffineSubspace.vadd_mem_of_mem_direction hneg (subset_affineSpan E s hp)
    simpa using this
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hpv inferInstance
  refine ⟨(f p)⁻¹ • f, fun a ha => ?_⟩
  have hd : a - p ∈ vectorSpan E s := vsub_mem_vectorSpan E ha hp
  have hz : f (a - p) = 0 := by
    have : f (a - p) ∈ (vectorSpan E s).map f := Submodule.mem_map_of_mem hd
    rw [hmap] at this; simpa using this
  rw [map_sub, sub_eq_zero] at hz
  simp [hz, hf]

theorem not_mem_of_dual {E K : Type} [Field E] [Field K] [Algebra E K]
    (s : Set K) (g : K →ₗ[E] E) (hg : ∀ a ∈ s, g a = 1) :
    (0 : K) ∉ affineSpan E s := by
  intro h0
  have hne : (affineSpan E s) ≠ ⊥ := fun h => by rw [h] at h0; exact h0
  rw [Ne, affineSpan_eq_bot] at hne
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hv : (0 : K) -ᵥ p ∈ vectorSpan E s := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction h0 (subset_affineSpan E s hp)
  have hle : vectorSpan E s ≤ LinearMap.ker g := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨a, ha, b, hb, rfl⟩
    simp [hg a ha, hg b hb]
  have := hle hv
  simp [hg p hp] at this

end PEqualNP.Outside.L_lib_747

open PEqualNP.Outside.L_lib_747 in
theorem PEqualNP.Outside.L_lib_747 : ∀ (E K : Type) [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K), (0 : K) ∉ S →
  ((∃ C : K →ₗ[E] K, Module.finrank E (LinearMap.range C) ≤ 1 ∧
    ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x) ↔
    (0 : K) ∉ affineSpan E (Set.image (fun z : K => z⁻¹) (↑S : Set K))) := by
  intro E K _ _ _ _ S hS
  constructor
  · rintro ⟨C, hC, hz⟩
    by_cases hne : S.Nonempty
    · obtain ⟨z0, hz0⟩ := hne
      obtain ⟨x0, hx0, hCx0⟩ := hz z0 hz0
      have hz0ne : z0 ≠ 0 := fun h => hS (h ▸ hz0)
      set u := C x0 with hu
      have hune : u ≠ 0 := by rw [hCx0]; exact mul_ne_zero hz0ne hx0
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hune
      -- every element of the range is a multiple of u
      have hmul : ∀ y, C y = f (C y) • u := by
        intro y
        have hr : Module.finrank E (LinearMap.range C) ≤ 1 := hC
        obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hr
        obtain ⟨cu, hcu⟩ := hv ⟨u, LinearMap.mem_range_self C x0⟩
        obtain ⟨cy, hcy⟩ := hv ⟨C y, LinearMap.mem_range_self C y⟩
        have hcu' : cu • (v : K) = u := by simpa using congrArg Subtype.val hcu
        have hcy' : cy • (v : K) = C y := by simpa using congrArg Subtype.val hcy
        have hcu0 : cu ≠ 0 := by
          rintro rfl; apply hune; rw [← hcu']; simp
        have hvy : C y = (cy / cu) • u := by
          rw [← hcy', ← hcu', smul_smul, div_mul_cancel₀ _ hcu0]
        rw [hvy, map_smul, hf, smul_eq_mul, mul_one]
      let g : K →ₗ[E] E := f ∘ₗ C ∘ₗ LinearMap.mulLeft E u
      apply not_mem_of_dual _ g
      rintro a ⟨z, hzS, rfl⟩
      obtain ⟨x, hx, hCx⟩ := hz z hzS
      have hzne : z ≠ 0 := fun h => hS (h ▸ hzS)
      have hfx : f (C x) ≠ 0 := by
        intro h0; rw [hmul x, h0, zero_smul] at hCx
        exact mul_ne_zero hzne hx hCx.symm
      have hxeq : x = f (C x) • (u * z⁻¹) := by
        have hh : z * x = f (C x) • u := by rw [← hCx]; exact hmul x
        rw [← smul_mul_assoc, ← hh]
        field_simp
      show f (C (u * z⁻¹)) = 1
      have h2 : f (C x) = f (C x) * f (C (u * z⁻¹)) := by
        conv_lhs => rw [hxeq]
        rw [map_smul, map_smul, smul_eq_mul]
      have := mul_left_cancel₀ hfx (h2.symm.trans (mul_one _).symm)
      exact this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp only [Finset.coe_empty, Set.image_empty, AffineSubspace.span_empty]
      exact AffineSubspace.notMem_bot E K 0
  · intro h0
    by_cases hne : S.Nonempty
    · obtain ⟨z0, hz0⟩ := hne
      obtain ⟨g, hg⟩ := dual_one_on ((fun z : K => z⁻¹) '' (↑S : Set K)) z0⁻¹ ⟨z0, hz0, rfl⟩ h0
      refine ⟨g.smulRight (1 : K), ?_, ?_⟩
      · calc Module.finrank E (LinearMap.range (g.smulRight (1 : K)))
            ≤ Module.finrank E (Submodule.span E {(1 : K)}) := by
              apply Submodule.finrank_mono
              rintro y ⟨x, rfl⟩
              exact Submodule.mem_span_singleton.mpr ⟨g x, rfl⟩
          _ = 1 := finrank_span_singleton one_ne_zero
      · intro z hz
        have hzne : z ≠ 0 := fun h => hS (h ▸ hz)
        refine ⟨z⁻¹, inv_ne_zero hzne, ?_⟩
        rw [LinearMap.smulRight_apply, hg _ ⟨z, hz, rfl⟩, one_smul, mul_inv_cancel₀ hzne]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨0, by rw [LinearMap.range_zero, finrank_bot]; norm_num, fun z hz => by simp at hz⟩
