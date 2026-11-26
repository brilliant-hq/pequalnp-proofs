import PEqualNP.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

theorem PEqualNP.Outside.L_gct_166 : ∀ (d q : ℕ) (g : Fin q → MvPolynomial (Fin d) ℂ), 1 ≤ q → (∀ j, MvPolynomial.constantCoeff (g j) = 1) → ∑ j, g j = MvPolynomial.C (q : ℂ) → ∃ s : Finset (MvPolynomial (Fin d) ℂ), Ideal.span (s : Set (MvPolynomial (Fin d) ℂ)) = Ideal.span (Set.range fun j => g j - 1) ∧ s.card + 1 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range g)) := by
  intro d q g hq hg hsum
  let V : Submodule ℂ (MvPolynomial (Fin d) ℂ) := Submodule.span ℂ (Set.range g)
  let W : Submodule ℂ (MvPolynomial (Fin d) ℂ) := Submodule.span ℂ (Set.range fun j => g j - 1)
  haveI hfinV : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  haveI hfinW : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1V : (1 : MvPolynomial (Fin d) ℂ) ∈ V := by
    have hsV : ∑ j : Fin q, g j ∈ V := Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, rfl⟩
    have hsm : ((q : ℂ)⁻¹) • (∑ j : Fin q, g j) ∈ V := V.smul_mem _ hsV
    have heq : ((q : ℂ)⁻¹) • (∑ j : Fin q, g j) = (1 : MvPolynomial (Fin d) ℂ) := by
      rw [hsum, MvPolynomial.smul_eq_C_mul, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    rwa [heq] at hsm
  have hWV : W ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact V.sub_mem (Submodule.subset_span ⟨j, rfl⟩) h1V
  have hconstW : ∀ p ∈ W, MvPolynomial.constantCoeff p = 0 := by
    intro p hp
    refine Submodule.span_induction (p := fun x _ => MvPolynomial.constantCoeff x = 0) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨j, rfl⟩
      simp [map_sub, hg j]
    · simp
    · intro x y _ _ hx hy
      simp [map_add, hx, hy]
    · intro c x _ hx
      rw [MvPolynomial.smul_eq_C_mul, map_mul, hx, mul_zero]
  have h1nW : (1 : MvPolynomial (Fin d) ℂ) ∉ W := by
    intro h1W
    have h0 := hconstW 1 h1W
    simp at h0
  have hlt : W < V := lt_of_le_of_ne hWV fun heq => h1nW (heq ▸ h1V)
  have hrank : Module.finrank ℂ W < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hlt
  let b := Module.finBasis ℂ W
  let s : Finset (MvPolynomial (Fin d) ℂ) := Finset.univ.image fun i => (b i : MvPolynomial (Fin d) ℂ)
  refine ⟨s, ?_, ?_⟩
  · apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      intro x hx
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨i, _, rfl⟩
      have hbiW : (b i : MvPolynomial (Fin d) ℂ) ∈ W := (b i).2
      refine Submodule.span_induction
        (p := fun y _ => y ∈ Ideal.span (Set.range fun j => g j - 1)) ?_ ?_ ?_ ?_ hbiW
      · intro y hy
        exact Ideal.subset_span hy
      · exact Ideal.zero_mem _
      · intro x y _ _ hx hy
        exact Ideal.add_mem _ hx hy
      · intro c y _ hy
        rw [MvPolynomial.smul_eq_C_mul]
        exact Ideal.mul_mem_left _ _ hy
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      have hmemW : g j - 1 ∈ W := Submodule.subset_span ⟨j, rfl⟩
      have hrep := b.sum_repr ⟨g j - 1, hmemW⟩
      have hval : g j - 1 = ∑ i, MvPolynomial.C (b.repr ⟨g j - 1, hmemW⟩ i) * (b i : MvPolynomial (Fin d) ℂ) := by
        have hcoe := congrArg W.subtype hrep
        simp only [map_sum, LinearMap.map_smul, Submodule.coe_subtype, MvPolynomial.smul_eq_C_mul] at hcoe
        exact hcoe.symm
      change g j - 1 ∈ Ideal.span (s : Set (MvPolynomial (Fin d) ℂ))
      rw [hval]
      refine Ideal.sum_mem _ fun i _ => ?_
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))
  · have hcard : s.card ≤ Module.finrank ℂ W := by
      calc s.card ≤ (Finset.univ : Finset (Fin (Module.finrank ℂ W))).card := Finset.card_image_le
        _ = Module.finrank ℂ W := by simp
    change s.card + 1 ≤ Module.finrank ℂ V
    omega
