import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_941_aux

open Classical

abbrev F2 := ZMod 2

lemma f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

def nextIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def prevIdx {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma nextIdx_prevIdx {n : ℕ} (i : Fin n) : nextIdx (prevIdx i) = i := by
  ext
  simp only [nextIdx, prevIdx]
  have hi := i.isLt
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  by_cases h0 : i.val = 0
  · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, Nat.mod_self]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      have h2 : i.val + n - 1 = (i.val - 1) + n := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have h3 : i.val - 1 + 1 = i.val := by omega
    rw [h3, Nat.mod_eq_of_lt hi]

lemma prevIdx_nextIdx {n : ℕ} (i : Fin n) : prevIdx (nextIdx i) = i := by
  ext
  simp only [nextIdx, prevIdx]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < n)]
    have h1 : i.val + 1 + n - 1 = i.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma nextIdx_injective {n : ℕ} : Function.Injective (@nextIdx n) := by
  intro i j hij
  have := congrArg prevIdx hij
  simpa [prevIdx_nextIdx] using this

lemma prevIdx_injective {n : ℕ} : Function.Injective (@prevIdx n) := by
  intro i j hij
  have := congrArg nextIdx hij
  simpa [nextIdx_prevIdx] using this

def hMat {n : ℕ} (i : Fin n) (b : Fin 4) : F2 :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
  then (1 : F2) else 0

def laneSet {n : ℕ} (b : Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)

def endsSet {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => nextIdx i ∉ S)

def runsCard {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : ℕ :=
  (endsSet S).card


lemma card_linIndep_fin (d : ℕ) :
    ∀ k ≤ d,
      (Finset.univ.filter (fun f : Fin k → (Fin d → F2) => LinearIndependent F2 f)).card =
        ∏ i ∈ Finset.range k, (2 ^ d - 2 ^ i) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.prod_empty]
    have huniv : Finset.univ.filter (fun f : Fin 0 → (Fin d → F2) => LinearIndependent F2 f) =
        Finset.univ := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (linearIndependent_empty_type (R := F2) (v := f))
    rw [huniv, Finset.card_univ, Fintype.card_unique]
  | succ k ih =>
    intro hkd
    rw [Finset.prod_range_succ, ← ih (Nat.le_of_succ_le hkd)]
    let e : (Fin (k + 1) → (Fin d → F2)) ≃ (Fin k → (Fin d → F2)) × (Fin d → F2) :=
      { toFun := fun f => (fun i => f i.castSucc, f (Fin.last k))
        invFun := fun p => Fin.lastCases p.2 p.1
        left_inv := fun f => by
          ext i j
          refine Fin.lastCases ?_ (fun r => ?_) i <;> simp
        right_inv := fun p => Prod.ext (by ext i j; simp) (by ext j; simp) }
    have hlin : ∀ (g : Fin k → (Fin d → F2)) (x : Fin d → F2),
        LinearIndependent F2 (Fin.lastCases x g) ↔
          LinearIndependent F2 g ∧ x ∉ Submodule.span F2 (Set.range g) := by
      intro g x
      constructor
      · intro h
        have hg : LinearIndependent F2 g := by
          have hsub := h.comp Fin.castSucc (Fin.castSucc_injective k)
          convert hsub using 1
          ext i j
          simp
        refine ⟨hg, ?_⟩
        intro hx
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨c, hc⟩ := hx
        have hzero : (∑ i : Fin (k + 1),
            Fin.lastCases (motive := fun _ => F2) (1 : F2) c i •
            Fin.lastCases (motive := fun _ => Fin d → F2) x g i) = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_smul]
          rw [hc]
          ext j
          simp only [Pi.add_apply, Pi.zero_apply]
          have h2 : ∀ a : F2, a + a = 0 := fun a => by rcases f2_eq_zero_or_one a with rfl | rfl <;> decide
          exact h2 (x j)
        have hcoeff := Fintype.linearIndependent_iff.mp h
          (Fin.lastCases (motive := fun _ => F2) (1 : F2) c) hzero (Fin.last k)
        simp at hcoeff
      · rintro ⟨hg, hx⟩
        rw [Fintype.linearIndependent_iff]
        intro c hc
        rw [Fin.sum_univ_castSucc] at hc
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last] at hc
        have hlast0 : c (Fin.last k) = 0 := by
          rcases f2_eq_zero_or_one (c (Fin.last k)) with h0 | h1
          · exact h0
          · exfalso
            rw [h1, one_smul] at hc
            have hxeq : x = ∑ i : Fin k, c i.castSucc • g i := by
              ext j
              have hcj := congrFun hc j
              simp only [Pi.add_apply, Pi.zero_apply] at hcj
              have h2 : ∀ a b : F2, a + b = 0 → b = a := by
                intro a b hab
                rcases f2_eq_zero_or_one a with rfl | rfl <;>
                  rcases f2_eq_zero_or_one b with rfl | rfl <;> simp_all
              exact h2 _ _ hcj
            apply hx
            rw [Submodule.mem_span_range_iff_exists_fun]
            exact ⟨fun i => c i.castSucc, hxeq.symm⟩
        rw [hlast0, zero_smul, add_zero] at hc
        have hrest := Fintype.linearIndependent_iff.mp hg (fun i => c i.castSucc) hc
        intro i
        refine Fin.lastCases hlast0 (fun j => hrest j) i
    let S_good := Finset.univ.filter (fun g : Fin k → (Fin d → F2) => LinearIndependent F2 g)
    have hcard_eq :
        (Finset.univ.filter (fun f : Fin (k + 1) → (Fin d → F2) => LinearIndependent F2 f)).card =
          ∑ g ∈ S_good, (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card := by
      have h1 :
          (Finset.univ.filter (fun f : Fin (k + 1) → (Fin d → F2) => LinearIndependent F2 f)).card =
            (Finset.univ.filter (fun p : (Fin k → (Fin d → F2)) × (Fin d → F2) =>
              LinearIndependent F2 p.1 ∧ p.2 ∉ Submodule.span F2 (Set.range p.1))).card := by
        refine Finset.card_bij (fun f _ => e f) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          have heq : Fin.lastCases (e f).2 (e f).1 = f := e.left_inv f
          exact (hlin (e f).1 (e f).2).mp (heq.symm ▸ hf)
        · intro f₁ _ f₂ _ h; exact e.injective h
        · intro p hp
          refine ⟨e.symm p, ?_, e.right_inv p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact (hlin p.1 p.2).mpr hp
      rw [h1]
      have h2 :
          (Finset.univ.filter (fun p : (Fin k → (Fin d → F2)) × (Fin d → F2) =>
              LinearIndependent F2 p.1 ∧ p.2 ∉ Submodule.span F2 (Set.range p.1))) =
            (S_good.sigma (fun g => Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g)))).map
              ⟨fun q => (q.1, q.2), fun a b hab => by
                rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
                simp only [Prod.mk.injEq] at hab
                rcases hab with ⟨h1, h2⟩; subst h1; subst h2; rfl⟩ := by
        ext ⟨g, x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_sigma,
          Function.Embedding.coeFn_mk, S_good]
        constructor
        · rintro ⟨hg, hx⟩
          exact ⟨⟨g, x⟩, ⟨hg, hx⟩, rfl⟩
        · rintro ⟨⟨g', x'⟩, ⟨hg', hx'⟩, heq⟩
          cases heq
          exact ⟨hg', hx'⟩
      rw [h2, Finset.card_map, Finset.card_sigma]
    rw [hcard_eq]
    have hconst : ∀ g ∈ S_good,
        (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card = 2 ^ d - 2 ^ k := by
      intro g hg
      simp only [S_good, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hcompl :
          (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card +
          (Finset.univ.filter (fun x : Fin d → F2 => x ∉ Submodule.span F2 (Set.range g))).card =
            2 ^ d := by
        rw [Finset.card_filter_add_card_filter_not]
        simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const]
      have hspan_card :
          (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card = 2 ^ k := by
        let b : Module.Basis (Fin k) F2 (Submodule.span F2 (Set.range g)) := Module.Basis.span hg
        have heq : (Finset.univ.filter (fun x : Fin d → F2 => x ∈ Submodule.span F2 (Set.range g))).card =
            (Finset.univ : Finset (Fin k → F2)).card := by
          refine Finset.card_bij
            (fun x hx => b.equivFun ⟨x, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_
          · intro x _; exact Finset.mem_univ _
          · intro x₁ hx₁ x₂ hx₂ h
            have h' := b.equivFun.injective h
            exact congrArg Subtype.val h'
          · intro c _
            refine ⟨(b.equivFun.symm c).1, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact (b.equivFun.symm c).2
            · exact b.equivFun.apply_symm_apply c
        rw [heq, Finset.card_univ]
        simp [Fintype.card_pi, ZMod.card]
      omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

lemma card_bases_submodule {n : ℕ} (U : Submodule F2 (Fin n → F2)) (d : ℕ)
    (hU : Module.finrank F2 U = d) :
    (Finset.univ.filter (fun f : Fin d → (Fin n → F2) =>
       LinearIndependent F2 f ∧ Submodule.span F2 (Set.range f) = U)).card =
      ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i) := by
  rw [← card_linIndep_fin d d (le_refl d)]
  let bU : Module.Basis (Fin d) F2 U := Module.finBasisOfFinrankEq F2 U hU
  let e : U ≃ₗ[F2] (Fin d → F2) := bU.equivFun
  refine Finset.card_bij
    (fun f hf => fun r => e ⟨f r, by
      have hsp := (Finset.mem_filter.mp hf).2.2
      rw [← hsp]
      exact Submodule.subset_span (Set.mem_range_self r)⟩) ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rcases hf with ⟨hlin, hsp⟩
    rw [Fintype.linearIndependent_iff] at hlin ⊢
    intro c hc
    apply hlin c
    have hc' : (∑ r : Fin d, c r • (⟨f r, by rw [← hsp]; exact Submodule.subset_span ⟨r, rfl⟩⟩ : U)) = 0 := by
      apply e.injective
      rw [map_sum, map_zero]
      simpa only [map_smul] using hc
    have hval := congrArg Subtype.val hc'
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero] using hval
  · intro f₁ hf₁ f₂ hf₂ heq
    ext r j
    have h1 := congrFun heq r
    have h2 := e.injective h1
    exact congrFun (congrArg Subtype.val h2) j
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    let f : Fin d → (Fin n → F2) := fun r => (e.symm (g r)).1
    have hf_lin : LinearIndependent F2 f := by
      rw [Fintype.linearIndependent_iff] at hg ⊢
      intro c hc
      apply hg c
      have hc' : (∑ r : Fin d, c r • e.symm (g r)) = 0 := by
        apply Subtype.ext
        simpa [f] using hc
      have := congrArg e hc'
      simpa only [map_sum, map_smul, LinearEquiv.apply_symm_apply, map_zero] using this
    have hf_le : Submodule.span F2 (Set.range f) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact (e.symm (g r)).2
    have hf_sp : Submodule.span F2 (Set.range f) = U := by
      have hfin1 : Module.finrank F2 (Submodule.span F2 (Set.range f)) = d := by
        rw [finrank_span_eq_card hf_lin, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hf_le (by rw [hfin1, hU])
    refine ⟨f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hf_lin, hf_sp⟩
    · ext r j
      simp [f]

lemma adj_rank_le_one_iff {d : ℕ} (u v : Fin d → F2) :
    (∀ r₁ r₂, u r₁ * v r₂ = v r₁ * u r₂) ↔ (u = 0 ∨ v = 0 ∨ u = v) := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · by_cases hv : v = 0
      · exact Or.inr (Or.inl hv)
      · right; right
        have ⟨r₁, hr₁⟩ : ∃ r₁, u r₁ ≠ 0 := by
          by_contra hall; push Not at hall; exact hu (funext hall)
        have hur₁ : u r₁ = 1 := by
          rcases f2_eq_zero_or_one (u r₁) with h0 | h1
          · exact absurd h0 hr₁
          · exact h1
        have hvr₁ : v r₁ = 1 := by
          rcases f2_eq_zero_or_one (v r₁) with h0 | h1
          · exfalso; apply hv; ext r
            have := h r₁ r
            rw [hur₁, one_mul, h0, zero_mul] at this
            exact this
          · exact h1
        ext r
        have := h r₁ r
        rw [hur₁, one_mul, hvr₁, one_mul] at this
        exact this.symm
  · rintro (rfl | rfl | rfl) r₁ r₂ <;> simp

noncomputable def validCols (n m : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin m → F2) :=
  Finset.univ.filter (fun c =>
    (∀ i, c i ≠ 0 ↔ i ∈ S) ∧
    (∀ i ∈ S, nextIdx i ∈ S → c i = c (nextIdx i)) ∧
    (∀ b : Fin 4, (∑ i : Fin n, hMat i b • c i) = 0))

noncomputable def fullCols (n d : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin d → F2) :=
  (validCols n d S).filter (fun c => LinearIndependent F2 (fun r i => c i r))

lemma actual_eq_fullCols_card (n d : ℕ) (S : Finset (Fin n))
    [Fintype (Submodule F2 (Fin n → F2))] :
    let good := fun U : Submodule F2 (Fin n → F2) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx i) = x (nextIdx i) * y i)
    let supp := fun U : Submodule F2 (Fin n → F2) =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let spaces := (Finset.univ : Finset (Submodule F2 (Fin n → F2))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Fin n → F2) => Module.finrank F2 U = d)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    B * (layer.filter (fun U => supp U = S)).card = (fullCols n d S).card := by
  intro good supp spaces layer B
  let L := layer.filter (fun U => supp U = S)
  let Mset := Finset.univ.filter (fun M : Fin d → (Fin n → F2) =>
    LinearIndependent F2 M ∧
    good (Submodule.span F2 (Set.range M)) ∧
    supp (Submodule.span F2 (Set.range M)) = S)
  have hBM : B * L.card = Mset.card := by
    have hfib : Mset.card = ∑ U ∈ L, (Mset.filter (fun M => Submodule.span F2 (Set.range M) = U)).card := by
      rw [← Finset.card_eq_sum_card_fiberwise]
      intro M hM
      simp only [Finset.mem_coe, Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      simp only [Finset.mem_coe, L, layer, spaces, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hM.2.1, by rw [finrank_span_eq_card hM.1, Fintype.card_fin]⟩, hM.2.2⟩
    rw [hfib]
    have hconst : ∀ U ∈ L, (Mset.filter (fun M => Submodule.span F2 (Set.range M) = U)).card = B := by
      intro U hU
      simp only [L, layer, spaces, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      have heq : Mset.filter (fun M => Submodule.span F2 (Set.range M) = U) =
          Finset.univ.filter (fun M : Fin d → (Fin n → F2) =>
            LinearIndependent F2 M ∧ Submodule.span F2 (Set.range M) = U) := by
        ext M
        simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, _, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; rw [h2]; exact ⟨⟨h1, hU.1.1, hU.2⟩, rfl⟩
      rw [heq]
      exact card_bases_submodule U d hU.1.2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hBM]
  refine Finset.card_bij (fun M _ => fun i r => M r i) ?_ ?_ ?_
  · intro M hM
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    rcases hM with ⟨hlin, ⟨hpar, hadj⟩, hsupp⟩
    simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmemM : ∀ r : Fin d, M r ∈ Submodule.span F2 (Set.range M) :=
      fun r => Submodule.subset_span ⟨r, rfl⟩
    have hsupp_iff : ∀ i : Fin n, (fun r => M r i) ≠ 0 ↔ i ∈ S := by
      intro i
      rw [← hsupp]
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne
        have ⟨r, hr⟩ : ∃ r, M r i ≠ 0 := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        exact ⟨M r, hmemM r, hr⟩
      · rintro ⟨x, hx, hxi⟩ h0
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨c, rfl⟩ := hx
        apply hxi
        have hzero : ∀ r, M r i = 0 := fun r => congrFun h0 r
        simp [hzero]
    refine ⟨⟨hsupp_iff, ?_, ?_⟩, hlin⟩
    · intro i hi hni
      have hrel : ∀ r₁ r₂, M r₁ i * M r₂ (nextIdx i) = M r₁ (nextIdx i) * M r₂ i :=
        fun r₁ r₂ => hadj (M r₁) (hmemM r₁) (M r₂) (hmemM r₂) i
      rcases (adj_rank_le_one_iff (fun r => M r i) (fun r => M r (nextIdx i))).mp hrel with h1 | h2 | h3
      · exact absurd h1 ((hsupp_iff i).mpr hi)
      · exact absurd h2 ((hsupp_iff (nextIdx i)).mpr hni)
      · exact h3
    · intro b
      ext r
      simpa [Finset.sum_apply] using hpar (M r) (hmemM r) b
  · intro M₁ _ M₂ _ h
    ext r i
    exact congrFun (congrFun h i) r
  · intro c hc
    simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨⟨hsupp, hadj, hpar⟩, hlin⟩
    let M : Fin d → (Fin n → F2) := fun r i => c i r
    refine ⟨M, ?_, rfl⟩
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hlin, ⟨?_, ?_⟩, ?_⟩
    · intro x hx b
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨α, rfl⟩ := hx
      have h1 : (∑ i : Fin n, hMat i b * (∑ r : Fin d, α r • M r) i) =
          ∑ r : Fin d, α r * (∑ i : Fin n, hMat i b * c i r) := by
        simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1]
      apply Finset.sum_eq_zero
      intro r _
      have hpr := congrFun (hpar b) r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpr
      rw [hpr, mul_zero]
    · intro x hx y hy i
      rw [Submodule.mem_span_range_iff_exists_fun] at hx hy
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      by_cases hi : i ∈ S
      · by_cases hni : nextIdx i ∈ S
        · have heq := hadj i hi hni
          have hxe : (∑ r : Fin d, α r • M r) (nextIdx i) = (∑ r : Fin d, α r • M r) i := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, heq]
          have hye : (∑ r : Fin d, β r • M r) (nextIdx i) = (∑ r : Fin d, β r • M r) i := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, heq]
          rw [hxe, hye]
        · have h0 : c (nextIdx i) = 0 := by
            by_contra hne; exact hni ((hsupp (nextIdx i)).mp hne)
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, h0, Pi.zero_apply,
            mul_zero, Finset.sum_const_zero, zero_mul]
      · have h0 : c i = 0 := by
          by_contra hne; exact hi ((hsupp i).mp hne)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, h0, Pi.zero_apply,
          mul_zero, Finset.sum_const_zero, zero_mul]
    · ext i
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hsupp i]
      constructor
      · rintro ⟨x, hx, hxi⟩ h0
        rw [Submodule.mem_span_range_iff_exists_fun] at hx
        obtain ⟨α, rfl⟩ := hx
        apply hxi
        simp [M, h0]
      · intro hne
        have ⟨r, hr⟩ : ∃ r, c i r ≠ 0 := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        exact ⟨M r, Submodule.subset_span ⟨r, rfl⟩, hr⟩

lemma fullCols_empty (n d : ℕ) (hd : 1 ≤ d) : (fullCols n d ∅).card = 0 := by
  rw [Finset.card_eq_zero]
  ext c
  simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  rintro ⟨hsupp, _, _⟩ hlin
  have hc0 : ∀ i, c i = 0 := fun i => by
    by_contra hne; exact hsupp i hne
  have := Fintype.linearIndependent_iff.mp hlin (Pi.single ⟨0, by omega⟩ 1) (by
    ext i; simp [hc0 i]) ⟨0, by omega⟩
  simp at this

lemma fullCols_univ (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (fullCols n d Finset.univ).card = 0 := by
  rw [Finset.card_eq_zero]
  ext c
  simp only [fullCols, validCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and]
  rintro ⟨_, hadj, _⟩ hlin
  have hconst : ∀ i : Fin n, c i = c ⟨0, by omega⟩ := by
    intro i
    have hstep : ∀ k : ℕ, (hk : k < n) → c ⟨k, hk⟩ = c ⟨0, by omega⟩ := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hprev : c ⟨k, by omega⟩ = c ⟨0, by omega⟩ := ih (by omega)
        have hnxt : nextIdx (⟨k, by omega⟩ : Fin n) = ⟨k + 1, hk⟩ := by
          ext; simp [nextIdx, Nat.mod_eq_of_lt hk]
        have heq := hadj ⟨k, by omega⟩ trivial trivial
        rw [hnxt] at heq
        exact heq.symm.trans hprev
    exact hstep i.val i.isLt
  let r0 : Fin d := ⟨0, by omega⟩
  let r1 : Fin d := ⟨1, by omega⟩
  have hr01 : r0 ≠ r1 := by intro h; have := congrArg Fin.val h; simp [r0, r1] at this
  let u := c ⟨0, by omega⟩
  rcases f2_eq_zero_or_one (u r0) with h0 | h0
  · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r0 1) (by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hconst i]
      exact h0) r0
    simp at h
  · rcases f2_eq_zero_or_one (u r1) with h1 | h1
    · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r1 1) (by
        ext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hconst i]
        exact h1) r1
      simp at h
    · have h := Fintype.linearIndependent_iff.mp hlin (Pi.single r0 1 + Pi.single r1 1) (by
        ext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_mul,
          Finset.sum_add_distrib]
        simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte, hconst i, u, h0, h1]
        show (1 : F2) + 1 = 0
        decide) r0
      simp [Pi.single_apply, hr01] at h

lemma fullCols_diff_le (n d : ℕ) (hd : 2 ≤ d) (S : Finset (Fin n)) :
    (validCols n d S).card - (fullCols n d S).card ≤
      (2 ^ d - 1) * (validCols n (d - 1) S).card := by
  have hsub : fullCols n d S ⊆ validCols n d S := Finset.filter_subset _ _
  have hsd : (validCols n d S \ fullCols n d S).card = (validCols n d S).card - (fullCols n d S).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    omega
  rw [← hsd]
  let nzA : Finset (Fin d → F2) := Finset.univ.filter (fun α : Fin d → F2 => α ≠ 0)
  have hnzA_card : nzA.card = 2 ^ d - 1 := by
    have h1 : nzA = Finset.univ.erase (0 : Fin d → F2) := by ext α; simp [nzA]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [Fintype.card_pi, ZMod.card]
  have hcover : (validCols n d S \ fullCols n d S) ⊆
      nzA.biUnion (fun α => (validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)) := by
    intro c hc
    simp only [Finset.mem_sdiff, fullCols, Finset.mem_filter] at hc
    rcases hc with ⟨hvc, hnot⟩
    have hnlin : ¬ LinearIndependent F2 (fun r i => c i r) := fun h => hnot ⟨hvc, h⟩
    rw [Fintype.linearIndependent_iff] at hnlin
    push Not at hnlin
    obtain ⟨α, hαsum, r0, hr0⟩ := hnlin
    have hαne : α ≠ 0 := fun h => hr0 (by simp [h])
    rw [Finset.mem_biUnion]
    refine ⟨α, by simp [nzA, hαne], ?_⟩
    simp only [Finset.mem_filter]
    refine ⟨hvc, fun i => ?_⟩
    have := congrFun hαsum i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have hle1 := Finset.card_le_card hcover
  have hle2 := Finset.card_biUnion_le (s := nzA)
    (t := fun α => (validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0))
  have hper : ∀ α ∈ nzA,
      ((validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)).card ≤
        (validCols n (d - 1) S).card := by
    intro α hα
    simp only [nzA, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    have ⟨r0, hr0⟩ : ∃ r0 : Fin d, α r0 ≠ 0 := by
      by_contra hall; push Not at hall; exact hα (funext hall)
    have hαr0 : α r0 = 1 := by
      rcases f2_eq_zero_or_one (α r0) with h0 | h1
      · exact absurd h0 hr0
      · exact h1
    have hd1 : d - 1 + 1 = d := by omega
    let eFin : Fin (d - 1 + 1) ≃ Fin d := finCongr hd1
    let r0' : Fin (d - 1 + 1) := eFin.symm r0
    let dropR : Fin (d - 1) → Fin d := fun j => eFin (r0'.succAbove j)
    have hdrop_ne : ∀ j, dropR j ≠ r0 := by
      intro j h
      have h' : r0'.succAbove j = r0' := eFin.injective (by simpa [dropR, r0'] using h)
      exact Fin.succAbove_ne r0' j h'
    have hrecover : ∀ (c : Fin n → Fin d → F2),
        (∀ i, (∑ r : Fin d, α r * c i r) = 0) →
        ∀ i, c i r0 = ∑ j : Fin (d - 1), α (dropR j) * c i (dropR j) := by
      intro c hc i
      have hsum := hc i
      rw [← Equiv.sum_comp eFin, Fin.sum_univ_succAbove _ r0'] at hsum
      have he0 : eFin r0' = r0 := eFin.apply_symm_apply r0
      rw [he0, hαr0, one_mul] at hsum
      have h2 : ∀ a b : F2, a + b = 0 → a = b := by
        intro a b hab
        rcases f2_eq_zero_or_one a with rfl | rfl <;>
          rcases f2_eq_zero_or_one b with rfl | rfl <;> simp_all
      exact h2 _ _ hsum
    refine Finset.card_le_card_of_injOn (fun c => fun i j => c i (dropR j)) ?_ ?_
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, validCols, Finset.mem_univ, true_and] at hc ⊢
      rcases hc with ⟨⟨hsupp, hadj, hpar⟩, horth⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        rw [← hsupp i]
        constructor
        · intro hne h0; apply hne; ext j; simp [h0]
        · intro hne h0
          apply hne
          ext r
          by_cases hr : r = r0
          · subst hr
            rw [hrecover c horth i]
            apply Finset.sum_eq_zero
            intro j _
            have hj := congrFun h0 j
            simp [hj]
          · have hr' : eFin.symm r ≠ r0' := fun h => hr (by
              have := congrArg eFin h; simpa [r0'] using this)
            obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hr'
            have hdj : dropR j = r := by simp [dropR, hj]
            have hj0 := congrFun h0 j
            simpa [hdj] using hj0
      · intro i hi hni
        ext j
        exact congrFun (hadj i hi hni) (dropR j)
      · intro b
        ext j
        have := congrFun (hpar b) (dropR j)
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hc₁ hc₂
      ext i r
      by_cases hr : r = r0
      · subst hr
        rw [hrecover c₁ hc₁.2 i, hrecover c₂ hc₂.2 i]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hval := congrFun (congrFun heq i) j
        dsimp only at hval
        rw [hval]
      · have hr' : eFin.symm r ≠ r0' := fun h => hr (by
          have := congrArg eFin h; simpa [r0'] using this)
        obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hr'
        have hdj : dropR j = r := by simp [dropR, hj]
        have := congrFun (congrFun heq i) j
        simpa [hdj] using this
  calc
    (validCols n d S \ fullCols n d S).card
        ≤ ∑ α ∈ nzA, ((validCols n d S).filter (fun c => ∀ i, (∑ r : Fin d, α r * c i r) = 0)).card :=
          le_trans hle1 hle2
    _ ≤ ∑ _α ∈ nzA, (validCols n (d - 1) S).card := Finset.sum_le_sum hper
    _ = (2 ^ d - 1) * (validCols n (d - 1) S).card := by
          rw [Finset.sum_const, smul_eq_mul, hnzA_card]


def runEndAux {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) : ℕ → Fin n → Fin n
  | 0, i => i
  | k + 1, i => if nextIdx i ∉ S then i else runEndAux S k (nextIdx i)

def runEnd {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (i : Fin n) : Fin n :=
  runEndAux S n i

lemma nextIdx_iterate_val {n : ℕ} (k : ℕ) (i : Fin n) :
    (nextIdx^[k] i).val = (i.val + k) % n := by
  induction k with
  | zero =>
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [nextIdx, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

lemma exists_step_not_mem {n : ℕ} (S : Finset (Fin n)) (hne : S ≠ Finset.univ) (i : Fin n) :
    ∃ k < n, nextIdx^[k] i ∉ S := by
  have ⟨z, hz⟩ : ∃ z : Fin n, z ∉ S := by
    by_contra hall; push Not at hall
    apply hne; ext x; simp [hall x]
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k := (z.val + n - i.val) % n
  refine ⟨k, Nat.mod_lt _ hn, ?_⟩
  have heq : nextIdx^[k] i = z := by
    ext
    rw [nextIdx_iterate_val]
    have hk : (i.val + k) % n = z.val := by
      dsimp only [k]
      rw [Nat.add_mod_mod]
      have hsum : i.val + (z.val + n - i.val) = z.val + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
    exact hk
  rw [heq]; exact hz

lemma runEndAux_spec {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) :
    ∀ (fuel : ℕ) (i : Fin n), i ∈ S → (∃ k < fuel, nextIdx^[k + 1] i ∉ S) →
      runEndAux S fuel i ∈ endsSet S ∧
      (∀ (m : ℕ) (c : Fin n → Fin m → F2),
        (∀ x ∈ S, nextIdx x ∈ S → c x = c (nextIdx x)) → c i = c (runEndAux S fuel i)) ∧
      (∀ f : ℕ, fuel ≤ f → runEndAux S f i = runEndAux S fuel i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i _ ⟨k, hk, _⟩; omega
  | succ fuel ih =>
    intro i hi ⟨k, hk, hnk⟩
    by_cases h1 : nextIdx i ∉ S
    · refine ⟨?_, ?_, ?_⟩
      · simp [runEndAux, h1, endsSet, hi]
      · intro _ _ _; simp [runEndAux, h1]
      · intro f hf
        cases f with
        | zero => omega
        | succ f => simp [runEndAux, h1]
    · push Not at h1
      have hkpos : 0 < k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        simp at hnk
        exact hnk h1
      have hex : ∃ k' < fuel, nextIdx^[k' + 1] (nextIdx i) ∉ S := by
        refine ⟨k - 1, by omega, ?_⟩
        have hstep : nextIdx^[k - 1 + 1] (nextIdx i) = nextIdx^[k + 1] i := by
          have hk1 : k - 1 + 1 = k := by omega
          rw [hk1, ← Function.iterate_succ_apply]
        rw [hstep]; exact hnk
      obtain ⟨hmem, hceq, hstab⟩ := ih (nextIdx i) h1 hex
      have hne1 : ¬ (nextIdx i ∉ S) := fun h => h h1
      refine ⟨?_, ?_, ?_⟩
      · simpa [runEndAux, hne1] using hmem
      · intro m c hadj
        simp only [runEndAux, hne1, ↓reduceIte]
        exact (hadj i hi h1).trans (hceq m c hadj)
      · intro f hf
        cases f with
        | zero => omega
        | succ f =>
          simp only [runEndAux, hne1, ↓reduceIte]
          exact hstab f (by omega)

lemma runEnd_spec {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (i : Fin n) (hi : i ∈ S) :
    runEnd S i ∈ endsSet S ∧
    (∀ (m : ℕ) (c : Fin n → Fin m → F2),
      (∀ x ∈ S, nextIdx x ∈ S → c x = c (nextIdx x)) → c i = c (runEnd S i)) := by
  obtain ⟨k, hk, hnk⟩ := exists_step_not_mem S hne i
  have hkpos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    exact hnk hi
  have hex : ∃ k' < n, nextIdx^[k' + 1] i ∉ S := ⟨k - 1, by omega, by
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1]; exact hnk⟩
  obtain ⟨h1, h2, _⟩ := runEndAux_spec S n i hi hex
  exact ⟨h1, h2⟩

lemma runEnd_of_mem_ends {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n))
    (e : Fin n) (he : e ∈ endsSet S) : runEnd S e = e := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt
  cases n with
  | zero => omega
  | succ m =>
    have hnot : nextIdx e ∉ S := (Finset.mem_filter.mp he).2
    simp [runEnd, runEndAux, hnot]

lemma runEnd_next {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (i : Fin n) (hi : i ∈ S) (hni : nextIdx i ∈ S) :
    runEnd S i = runEnd S (nextIdx i) := by
  obtain ⟨k, hk, hnk⟩ := exists_step_not_mem S hne (nextIdx i)
  have hkpos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    exact hnk hni
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h1 : runEnd S i = runEndAux S (n - 1) (nextIdx i) := by
    have hstep : ∀ m : ℕ, 1 ≤ m → runEndAux S m i = runEndAux S (m - 1) (nextIdx i) := by
      intro m hm
      cases m with
      | zero => omega
      | succ m =>
        have hnot : ¬ (nextIdx i ∉ S) := fun h => h hni
        simp [runEndAux, hnot]
    exact hstep n hn
  rw [h1]
  have hex : ∃ k' < n - 1, nextIdx^[k' + 1] (nextIdx i) ∉ S := by
    by_cases hkn : k = n - 1
    · exfalso
      have hcy : nextIdx^[k] (nextIdx i) = i := by
        ext; rw [nextIdx_iterate_val]; simp only [nextIdx]
        rw [Nat.mod_add_mod]
        have hsum : i.val + 1 + k = i.val + n := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      rw [hcy] at hnk; exact hnk hi
    · refine ⟨k - 1, by omega, ?_⟩
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1]; exact hnk
  have hstab := (runEndAux_spec S (n - 1) (nextIdx i) hni hex).2.2 n (by omega)
  exact hstab.symm

lemma runEnd_singleton {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (hne : S ≠ Finset.univ)
    (e : Fin n) (he : e ∈ endsSet S) (hprev : prevIdx e ∉ S) :
    S.filter (fun i => runEnd S i = e) = {e} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hre⟩
    by_contra hne_ie
    have hwalk : ∀ (fuel : ℕ) (x : Fin n), x ∈ S → x ≠ e → runEndAux S fuel x = e → False := by
      intro fuel
      induction fuel with
      | zero => intro x _ hne' heq; exact hne' heq
      | succ fuel ih =>
        intro x hx hne' heq
        by_cases hnx : nextIdx x ∉ S
        · simp [runEndAux, hnx] at heq; exact hne' heq
        · push Not at hnx
          have hne_nx : ¬ (nextIdx x ∉ S) := fun h => h hnx
          simp only [runEndAux, hne_nx, ↓reduceIte] at heq
          by_cases hxe : nextIdx x = e
          · have hxp : x = prevIdx e := by
              rw [← hxe, prevIdx_nextIdx]
            rw [hxp] at hx
            exact hprev hx
          · exact ih (nextIdx x) hnx hxe heq
    exact hwalk n i hi hne_ie hre
  · rintro rfl
    exact ⟨(Finset.mem_filter.mp he).1, runEnd_of_mem_ends S i he⟩

def runParity {n : ℕ} [DecidableEq (Fin n)] (S : Finset (Fin n)) (e : Fin n) (b : Fin 4) : F2 :=
  ∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b

def chi (x : F2) : ℝ := if x = 0 then 1 else -1

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  have h11 : (1 : F2) + 1 = 0 := rfl
  rcases f2_eq_zero_or_one x with rfl | rfl <;> rcases f2_eq_zero_or_one y with rfl | rfl <;>
    simp [chi, h11]

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma sum_chi_f2 (a : F2) : (∑ x : F2, chi (x * a)) = if a = 0 then 2 else 0 := by
  have hsum : ∀ f : F2 → ℝ, (∑ x : F2, f x) = f 0 + f 1 := fun f => by
    change (∑ x : Fin 2, f x) = f 0 + f 1
    exact Fin.sum_univ_two _
  rcases f2_eq_zero_or_one a with rfl | rfl <;> simp [hsum, chi] <;> norm_num

lemma prod_chi_sum {ι : Type*} [Fintype ι] (f : ι → F2) :
    (∏ i : ι, chi (f i)) = chi (∑ i : ι, f i) := by
  have h : ∀ (s : Finset ι), (∏ i ∈ s, chi (f i)) = chi (∑ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [chi_zero]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, chi_add, ih]
  exact h Finset.univ

lemma sum_chi_vec_all {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → F2) :
    (∑ v : ι → F2, ∏ i : ι, chi (v i * u i)) = if u = 0 then (2 : ℝ) ^ Fintype.card ι else 0 := by
  rw [← Fintype.prod_sum (fun i x => chi (x * u i))]
  simp_rw [sum_chi_f2]
  by_cases hu : u = 0
  · subst hu
    simp only [Pi.zero_apply, ↓reduceIte, Finset.prod_const, Finset.card_univ]
  · rw [ite_eq_right hu]
    have ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
      by_contra hall; push Not at hall; exact hu (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (ite_eq_right hi0)

lemma sum_chi_nonzero (m : ℕ) (u : Fin m → F2) :
    (∑ w ∈ (Finset.univ.erase (0 : Fin m → F2)), ∏ j : Fin m, chi (u j * w j)) =
      if u = 0 then (2 : ℝ) ^ m - 1 else -1 := by
  have hall := sum_chi_vec_all u
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [hcard] at hall
  have hcomm : ∀ w : Fin m → F2, (∏ j : Fin m, chi (u j * w j)) = ∏ j : Fin m, chi (w j * u j) :=
    fun w => Finset.prod_congr rfl (fun j _ => by rw [mul_comm])
  simp_rw [hcomm]
  have hsplit := Finset.add_sum_erase Finset.univ (fun w : Fin m → F2 => ∏ j : Fin m, chi (w j * u j))
    (Finset.mem_univ (0 : Fin m → F2))
  have h0 : (∏ j : Fin m, chi ((0 : Fin m → F2) j * u j)) = 1 := by
    simp [chi_zero]
  rw [h0, hall] at hsplit
  split_ifs at hsplit ⊢ <;> linarith

lemma validCols_card_eq_fourier (n m : ℕ) (S : Finset (Fin n)) (hne : S ≠ Finset.univ) :
    ((validCols n m S).card : ℝ) =
      (1 / ((2 : ℝ) ^ m) ^ 4) *
        ∑ v : Fin 4 → Fin m → F2,
          ∏ e ∈ endsSet S,
            if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ) := by
  let nzV : Finset (Fin m → F2) := Finset.univ.erase (0 : Fin m → F2)
  let Wset := (endsSet S → {u : Fin m → F2 // u ∈ nzV})
  have hbij : (validCols n m S).card =
      (Finset.univ.filter (fun w : Wset =>
        ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card := by
    refine Finset.card_bij
      (fun c hc => fun e : endsSet S => ⟨c e.1, by
        simp only [nzV, Finset.mem_erase, Finset.mem_univ, and_true]
        have hvc := (Finset.mem_filter.mp hc).2
        have he2 := e.2
        simp only [endsSet, Finset.mem_filter] at he2
        exact (hvc.1 e.1).mpr he2.1⟩) ?_ ?_ ?_
    · intro c hc
      simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rcases hc with ⟨hsupp, hadj, hpar⟩
      intro b
      have hpart : (∑ i : Fin n, hMat i b • c i) =
          ∑ e ∈ endsSet S, runParity S e b • c e := by
        have h1 : (∑ i : Fin n, hMat i b • c i) = ∑ i ∈ S, hMat i b • c i := by
          symm
          refine Finset.sum_subset (Finset.subset_univ S) ?_
          intro i _ hi
          have h0 : c i = 0 := by by_contra h; exact hi ((hsupp i).mp h)
          simp [h0]
        rw [h1]
        rw [← Finset.sum_fiberwise_of_maps_to (g := runEnd S) (t := endsSet S)
          (fun i hi => (runEnd_spec S hne i hi).1)]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        dsimp only [runParity]
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hiS := (Finset.mem_filter.mp hi).1
        have hre := (Finset.mem_filter.mp hi).2
        have hceq := (runEnd_spec S hne i hiS).2 m c hadj
        rw [hceq, hre]
      rw [Finset.sum_coe_sort (endsSet S) (fun e => runParity S e b • c e)]
      rw [← hpart]
      exact hpar b
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
      ext i j
      by_cases hi : i ∈ S
      · have he1 := (runEnd_spec S hne i hi).1
        have h1 := (runEnd_spec S hne i hi).2 m c₁ hc₁.2.1
        have h2 := (runEnd_spec S hne i hi).2 m c₂ hc₂.2.1
        have h3 := congrArg Subtype.val (congrFun heq ⟨runEnd S i, he1⟩)
        exact congrFun (h1.trans (h3.trans h2.symm)) j
      · have h1 : c₁ i = 0 := by by_contra h; exact hi ((hc₁.1 i).mp h)
        have h2 : c₂ i = 0 := by by_contra h; exact hi ((hc₂.1 i).mp h)
        rw [h1, h2]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let c : Fin n → Fin m → F2 := fun i =>
        if hi : i ∈ S then (w ⟨runEnd S i, (runEnd_spec S hne i hi).1⟩).1 else 0
      refine ⟨c, ?_, ?_⟩
      · simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · intro i
          by_cases hi : i ∈ S
          · simp only [c, dif_pos hi, hi, iff_true]
            exact (Finset.mem_erase.mp (w ⟨runEnd S i, (runEnd_spec S hne i hi).1⟩).2).1
          · simp [c, hi]
        · intro i hi hni
          simp only [c, dif_pos hi, dif_pos hni]
          congr 2
          exact Subtype.ext (runEnd_next S hne i hi hni)
        · intro b
          have h1 : (∑ i : Fin n, hMat i b • c i) = ∑ i ∈ S, hMat i b • c i := by
            symm
            refine Finset.sum_subset (Finset.subset_univ S) ?_
            intro i _ hi; simp [c, hi]
          rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := runEnd S) (t := endsSet S)
            (fun i hi => (runEnd_spec S hne i hi).1)]
          have h2 : ∀ (e : Fin n) (he : e ∈ endsSet S),
              (∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b • c i) =
                runParity S e b • (w ⟨e, he⟩).1 := by
            intro e he
            dsimp only [runParity]
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have hiS := (Finset.mem_filter.mp hi).1
            have hre := (Finset.mem_filter.mp hi).2
            simp only [c, dif_pos hiS]
            congr 3
            exact Subtype.ext hre
          rw [← Finset.sum_coe_sort (endsSet S) (fun e => ∑ i ∈ S.filter (fun i => runEnd S i = e), hMat i b • c i)]
          have h3 : (∑ e : endsSet S, ∑ i ∈ S.filter (fun i => runEnd S i = e.1), hMat i b • c i) =
              ∑ e : endsSet S, runParity S e.1 b • (w e).1 :=
            Finset.sum_congr rfl (fun e _ => h2 e.1 e.2)
          rw [h3]
          exact hw b
      · ext e j
        have he2 := e.2
        simp only [endsSet, Finset.mem_filter] at he2
        have heS : e.1 ∈ S := he2.1
        have hre : runEnd S e.1 = e.1 := runEnd_of_mem_ends S e.1 e.2
        simp only [c, dif_pos heS]
        have hsub : (⟨runEnd S e.1, (runEnd_spec S hne e.1 heS).1⟩ : endsSet S) = e := Subtype.ext hre
        rw [hsub]
  rw [hbij]
  have hpos : ((2 : ℝ) ^ m) ^ 4 ≠ 0 := by positivity
  have hmain :
      (((Finset.univ.filter (fun w : Wset =>
          ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card : ℝ) *
        ((2 : ℝ) ^ m) ^ 4) =
        ∑ v : Fin 4 → Fin m → F2,
          ∏ e ∈ endsSet S,
            if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ) := by
    have hstep1 :
        ∑ w : Wset, ∑ v : Fin 4 → Fin m → F2,
            ∏ b : Fin 4, ∏ j : Fin m,
              chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j)) =
          ((Finset.univ.filter (fun w : Wset =>
            ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)).card : ℝ) *
            ((2 : ℝ) ^ m) ^ 4 := by
      have hinner : ∀ w : Wset,
          (∑ v : Fin 4 → Fin m → F2,
            ∏ b : Fin 4, ∏ j : Fin m,
              chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j))) =
            if (∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0)
            then ((2 : ℝ) ^ m) ^ 4 else 0 := by
        intro w
        let u : Fin 4 × Fin m → F2 := fun p => ∑ e : endsSet S, runParity S e.1 p.1 * (w e).1 p.2
        have hsum_eq := sum_chi_vec_all u
        have hcard4m : (2 : ℝ) ^ Fintype.card (Fin 4 × Fin m) = ((2 : ℝ) ^ m) ^ 4 := by
          simp only [Fintype.card_prod, Fintype.card_fin]
          rw [mul_comm, pow_mul]
        rw [hcard4m] at hsum_eq
        have heq_lhs :
            (∑ v : Fin 4 → Fin m → F2,
              ∏ b : Fin 4, ∏ j : Fin m, chi (v b j * u (b, j))) =
              ∑ v : Fin 4 × Fin m → F2, ∏ p : Fin 4 × Fin m, chi (v p * u p) := by
          refine Fintype.sum_equiv (Equiv.curry (Fin 4) (Fin m) F2).symm _ _ ?_
          intro v
          rw [Fintype.prod_prod_type]
          rfl
        rw [heq_lhs, hsum_eq]
        have hu_iff : u = 0 ↔ ∀ b : Fin 4, (∑ e : endsSet S, runParity S e.1 b • (w e).1) = 0 := by
          constructor
          · intro h b; ext j
            have := congrFun h (b, j)
            simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
          · intro h; ext ⟨b, j⟩
            have := congrFun (h b) j
            simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
        by_cases hu : u = 0
        · rw [ite_eq_left hu, ite_eq_left (hu_iff.mp hu)]
        · rw [ite_eq_right hu, ite_eq_right (fun h => hu (hu_iff.mpr h))]
      simp_rw [hinner]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [← hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hfactor : ∀ w : Wset,
        (∏ b : Fin 4, ∏ j : Fin m, chi (v b j * (∑ e : endsSet S, runParity S e.1 b * (w e).1 j))) =
          ∏ e : endsSet S, ∏ j : Fin m,
            chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * (w e).1 j) := by
      intro w
      simp_rw [prod_chi_sum]
      congr 1
      have hL :
          (∑ b : Fin 4, ∑ j : Fin m, v b j * ∑ e : endsSet S, runParity S e.1 b * (w e).1 j) =
            ∑ b : Fin 4, ∑ j : Fin m, ∑ e : endsSet S, v b j * (runParity S e.1 b * (w e).1 j) := by
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _))
      have hR :
          (∑ e : endsSet S, ∑ j : Fin m, (∑ b : Fin 4, runParity S e.1 b • v b) j * (w e).1 j) =
            ∑ e : endsSet S, ∑ j : Fin m, ∑ b : Fin 4, (runParity S e.1 b * v b j) * (w e).1 j := by
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [hL, hR]
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun b _ => by ring))
    simp_rw [hfactor]
    dsimp only [Wset]
    rw [← Fintype.prod_sum (fun (e : endsSet S) (u : {u : Fin m → F2 // u ∈ nzV}) =>
      ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u.1 j))]
    rw [← Finset.prod_coe_sort (endsSet S)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    have hsum_sub :
        (∑ u : {u : Fin m → F2 // u ∈ nzV},
            ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u.1 j)) =
          ∑ u ∈ nzV, ∏ j : Fin m, chi ((∑ b : Fin 4, runParity S e.1 b • v b) j * u j) := by
      rw [← Finset.sum_coe_sort nzV]
    rw [hsum_sub]
    exact sum_chi_nonzero m (∑ b : Fin 4, runParity S e.1 b • v b)
  rw [← hmain]
  field_simp [hpos]

noncomputable def inKer {n m : ℕ} [DecidableEq (Fin n)] (v : Fin 4 → Fin m → F2) (S : Finset (Fin n)) : ℕ :=
  ((endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)).card

lemma abs_fourier_term_eq (n m : ℕ) (hm : 1 ≤ m) (v : Fin 4 → Fin m → F2) (S : Finset (Fin n)) :
    |∏ e ∈ endsSet S,
        if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ)| =
      ((2 : ℝ) ^ m - 1) ^ (inKer v S) := by
  have hq1 : (0 : ℝ) ≤ (2 : ℝ) ^ m - 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    linarith
  rw [Finset.abs_prod]
  have hterm : ∀ e ∈ endsSet S,
      |if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else (-1 : ℝ)| =
        if (∑ b : Fin 4, runParity S e b • v b) = 0 then ((2 : ℝ) ^ m - 1) else 1 := by
    intro e _
    split_ifs
    · exact abs_of_nonneg hq1
    · norm_num
  rw [Finset.prod_congr rfl hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl


def matA (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; q - 1, 1]
def matT2 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2, 2; 2 * (q - 1), q]
def matA2 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![q, 2; 2 * (q - 1), q]
def matM6 (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := matT2 q * matT2 q * matA2 q

def matProd : ∀ (k : ℕ), (Fin k → Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | k + 1, f => matProd k (fun j => f j.castSucc) * f (Fin.last k)

lemma matProd_const (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ k : ℕ, matProd k (fun _ => M) = M ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [matProd, ih, pow_succ]

lemma matProd_period3 (M0 M1 M2 : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (t : ℕ) (f : Fin (3 * t) → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j : Fin (3 * t), f j = if j.val % 3 = 0 then M0 else if j.val % 3 = 1 then M1 else M2) →
      matProd (3 * t) f = (M0 * M1 * M2) ^ t := by
  intro t
  induction t with
  | zero => intro _ _; rfl
  | succ t ih =>
    intro f hf
    have hstep : matProd (3 * (t + 1)) f =
        matProd (3 * t) (fun j => f ⟨j.val, by omega⟩) *
          f ⟨3 * t, by omega⟩ * f ⟨3 * t + 1, by omega⟩ * f ⟨3 * t + 2, by omega⟩ := by
      rfl
    rw [hstep]
    have hih := ih (fun j => f ⟨j.val, by omega⟩) (fun j => hf ⟨j.val, by omega⟩)
    rw [hih]
    have h0 : f ⟨3 * t, by omega⟩ = M0 := by
      rw [hf]; simp [Nat.mul_mod_right]
    have h1 : f ⟨3 * t + 1, by omega⟩ = M1 := by
      rw [hf]; have : (3 * t + 1) % 3 = 1 := by omega
      simp [this]
    have h2 : f ⟨3 * t + 2, by omega⟩ = M2 := by
      rw [hf]; have : (3 * t + 2) % 3 = 2 := by omega
      simp [this]
    rw [h0, h1, h2, pow_succ]
    simp only [Matrix.mul_assoc]

lemma matProd_apply_eq_sum :
    ∀ (k : ℕ) (f : Fin k → Matrix (Fin 2) (Fin 2) ℝ) (a b : Fin 2),
      matProd k f a b =
        ∑ x : Fin (k + 1) → Fin 2,
          if x 0 = a ∧ x (Fin.last k) = b then
            ∏ j : Fin k, f j (x j.castSucc) (x j.succ)
          else 0 := by
  intro k
  induction k with
  | zero =>
    intro f a b
    simp only [matProd, Finset.univ_eq_empty, Finset.prod_empty]
    have hsum : (∑ x : Fin 1 → Fin 2, if x 0 = a ∧ x (Fin.last 0) = b then (1 : ℝ) else 0) =
        if a = b then 1 else 0 := by
      let e : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
      rw [Fintype.sum_equiv e _ (fun c : Fin 2 => if c = a ∧ c = b then (1 : ℝ) else 0)
        (fun x => by simp [e, Fin.last])]
      fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]
    rw [hsum]
    fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]
  | succ k ih =>
    intro f a b
    simp only [matProd, Matrix.mul_apply]
    have hih : ∀ c : Fin 2,
        matProd k (fun j => f j.castSucc) a c =
          ∑ y : Fin (k + 1) → Fin 2,
            if y 0 = a ∧ y (Fin.last k) = c then
              ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)
            else 0 := fun c => ih (fun j => f j.castSucc) a c
    simp_rw [hih, Finset.sum_mul]
    rw [Finset.sum_comm]
    let e : (Fin (k + 2) → Fin 2) ≃ (Fin (k + 1) → Fin 2) × Fin 2 :=
      { toFun := fun x => (fun i => x i.castSucc, x (Fin.last (k + 1)))
        invFun := fun p => Fin.lastCases p.2 p.1
        left_inv := fun x => by
          ext i
          refine Fin.lastCases ?_ (fun r => ?_) i <;> simp
        right_inv := fun p => Prod.ext (by ext i; simp) (by simp) }
    symm
    rw [Fintype.sum_equiv e _
      (fun p : (Fin (k + 1) → Fin 2) × Fin 2 =>
        if p.1 0 = a ∧ p.2 = b then
          (∏ j : Fin k, f j.castSucc (p.1 j.castSucc) (p.1 j.succ)) * f (Fin.last k) (p.1 (Fin.last k)) p.2
        else 0)
      (fun x => by
        dsimp only [e, Equiv.coe_fn_mk]
        rw [Fin.prod_univ_castSucc]
        congr 1)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hL : (∑ c : Fin 2,
        (if y 0 = a ∧ y (Fin.last k) = c then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
          f (Fin.last k) c b) =
        if y 0 = a then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) b
        else 0 := by
      have hc : (∑ c : Fin 2,
          if c = y (Fin.last k) then
            (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) * f (Fin.last k) c b
          else 0) =
          (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
            f (Fin.last k) (y (Fin.last k)) b := by
        simp [Finset.sum_ite_eq']
      have heq : ∀ c : Fin 2,
          (if y 0 = a ∧ y (Fin.last k) = c then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) *
            f (Fin.last k) c b =
          if c = y (Fin.last k) then
            (if y 0 = a then ∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ) else 0) * f (Fin.last k) c b
          else 0 := by
        intro c
        by_cases h1 : y 0 = a <;> by_cases h2 : y (Fin.last k) = c
        · subst h2; simp [h1]
        · have h2' : c ≠ y (Fin.last k) := Ne.symm h2; simp [h1, h2, h2']
        · simp [h1, h2]
        · have h2' : c ≠ y (Fin.last k) := Ne.symm h2; simp [h1, h2, h2']
      simp_rw [heq]
      rw [hc]
      split_ifs <;> ring
    have hR : (∑ z : Fin 2,
        if y 0 = a ∧ z = b then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) z
        else 0) =
        if y 0 = a then
          (∏ j : Fin k, f j.castSucc (y j.castSucc) (y j.succ)) * f (Fin.last k) (y (Fin.last k)) b
        else 0 := by
      by_cases hy : y 0 = a
      · simp [hy, Finset.sum_ite_eq']
      · simp [hy]
    rw [hL, hR]

lemma matProd_trace_eq_sum (L : ℕ) (hL : 1 ≤ L) (f : Fin L → Matrix (Fin 2) (Fin 2) ℝ) :
    (matProd L f).trace = ∑ x : Fin L → Fin 2, ∏ j : Fin L, f j (x j) (x (nextIdx j)) := by
  simp only [Matrix.trace, Matrix.diag_apply, matProd_apply_eq_sum]
  rw [Finset.sum_comm]
  have hcollapse : ∀ y : Fin (L + 1) → Fin 2,
      (∑ a : Fin 2, if y 0 = a ∧ y (Fin.last L) = a then ∏ j : Fin L, f j (y j.castSucc) (y j.succ) else 0) =
        if y 0 = y (Fin.last L) then ∏ j : Fin L, f j (y j.castSucc) (y j.succ) else 0 := by
    intro y
    by_cases h : y 0 = y (Fin.last L)
    · rw [ite_eq_left h]
      have h1 : ∀ a : Fin 2, (y 0 = a ∧ y (Fin.last L) = a) ↔ a = y 0 := by
        intro a; rw [← h]; constructor <;> intro ha
        · exact ha.1.symm
        · exact ⟨ha.symm, ha.symm⟩
      simp_rw [h1]
      simp [Finset.sum_ite_eq']
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro a _
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact h (h1.trans h2.symm)
  simp_rw [hcollapse]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun y _ => fun j : Fin L => y j.castSucc) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro y₁ hy₁ y₂ hy₂ heq
    have h1 := (Finset.mem_filter.mp hy₁).2
    have h2 := (Finset.mem_filter.mp hy₂).2
    funext i
    refine Fin.lastCases (motive := fun idx => y₁ idx = y₂ idx) ?_ (fun j => congrFun heq j) i
    rw [← h1, ← h2]
    have h0 : (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin L).castSucc := by ext; simp
    rw [h0]
    exact congrFun heq ⟨0, by omega⟩
  · intro x _
    let y : Fin (L + 1) → Fin 2 := Fin.lastCases (motive := fun _ => Fin 2) (x ⟨0, by omega⟩) x
    refine ⟨y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h0 : (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin L).castSucc := by ext; simp
      rw [h0]
      dsimp only [y]
      rw [Fin.lastCases_castSucc, Fin.lastCases_last]
    · funext j; simp [y]
  · intro y hy
    have hclose := (Finset.mem_filter.mp hy).2
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have harg : y j.succ = y (nextIdx j).castSucc := by
      by_cases hlast : j.val + 1 = L
      · have hj : j.succ = Fin.last L := by ext; simp [hlast]
        have hn : (nextIdx j).castSucc = (0 : Fin (L + 1)) := by
          ext; simp [nextIdx, hlast, Nat.mod_self]
        rw [hj, hn, ← hclose]
      · have hlt : j.val + 1 < L := by omega
        have hn : (nextIdx j).castSucc = j.succ := by
          ext; simp [nextIdx, Nat.mod_eq_of_lt hlt]
        rw [hn]
    rw [harg]

lemma sum_runs_eq_trace_A (n : ℕ) (hn : 1 ≤ n) (q : ℝ) :
    (∑ S : Finset (Fin n), (q - 1) ^ (runsCard S)) = (matA q ^ n).trace := by
  rw [← matProd_const (matA q) n, matProd_trace_eq_sum n hn]
  let e : Finset (Fin n) ≃ (Fin n → Fin 2) :=
    { toFun := fun S i => if i ∈ S then 1 else 0
      invFun := fun x => Finset.univ.filter (fun i => x i = 1)
      left_inv := fun S => by ext i; by_cases hi : i ∈ S <;> simp [hi]
      right_inv := fun x => by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases fin2_cases (x i) with h | h <;> simp [h] }
  refine Fintype.sum_equiv e _ _ ?_
  intro S
  have hterm : ∀ i : Fin n,
      matA q (e S i) (e S (nextIdx i)) = if i ∈ endsSet S then (q - 1) else 1 := by
    intro i
    simp only [e, endsSet, Finset.mem_filter]
    by_cases h1 : i ∈ S <;> by_cases h2 : nextIdx i ∈ S <;> simp [h1, h2, matA]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hf : Finset.univ.filter (fun i : Fin n => i ∈ endsSet S) = endsSet S := by
    ext i; simp
  rw [hf, runsCard]

lemma matA_pow_formula (q : ℝ) (hq : 1 < q) :
    ∀ k : ℕ,
      let r := Real.sqrt (q - 1)
      (matA q ^ k) 0 0 = ((1 + r) ^ k + (1 - r) ^ k) / 2 ∧
      (matA q ^ k) 0 1 = ((1 + r) ^ k - (1 - r) ^ k) / (2 * r) ∧
      (matA q ^ k) 1 0 = r * ((1 + r) ^ k - (1 - r) ^ k) / 2 ∧
      (matA q ^ k) 1 1 = ((1 + r) ^ k + (1 - r) ^ k) / 2 := by
  intro k
  let r := Real.sqrt (q - 1)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = q - 1 := Real.sq_sqrt (by linarith)
  have hA00 : matA q 0 0 = 1 := rfl
  have hA01 : matA q 0 1 = 1 := rfl
  have hA10 : matA q 1 0 = q - 1 := rfl
  have hA11 : matA q 1 1 = 1 := rfl
  induction k with
  | zero =>
    simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h00, h01, h10, h11⟩
    rw [pow_succ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, hA00, hA10, pow_succ]
      have hne : r ≠ 0 := ne_of_gt hrpos
      rw [show Real.sqrt (q - 1) = r from rfl, show q - 1 = r ^ 2 from hr2.symm]
      field_simp [hne]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, hA01, hA11, pow_succ]
      have hne : r ≠ 0 := ne_of_gt hrpos
      rw [show Real.sqrt (q - 1) = r from rfl]
      field_simp [hne]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hA00, hA10, pow_succ]
      rw [show Real.sqrt (q - 1) = r from rfl, show q - 1 = r ^ 2 from hr2.symm]; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hA01, hA11, pow_succ]
      rw [show Real.sqrt (q - 1) = r from rfl]; ring

lemma trace_matA_pow_eq (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (matA q ^ k).trace = (1 + Real.sqrt (q - 1)) ^ k + (1 - Real.sqrt (q - 1)) ^ k := by
  have hf := matA_pow_formula q hq k
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, hf.1, hf.2.2.2]
  ring

lemma trace_matA_pow_ge_even (q : ℝ) (hq : 1 < q) (a : ℕ) :
    (1 + Real.sqrt (q - 1)) ^ (2 * a) ≤ (matA q ^ (2 * a)).trace := by
  rw [trace_matA_pow_eq q hq (2 * a)]
  have hnn : 0 ≤ (1 - Real.sqrt (q - 1)) ^ (2 * a) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) a
  linarith

lemma trace_matA_pow_le_even (q : ℝ) (hq : 1 < q) (a : ℕ) :
    (matA q ^ (2 * a)).trace ≤ 2 * (1 + Real.sqrt (q - 1)) ^ (2 * a) := by
  rw [trace_matA_pow_eq q hq (2 * a)]
  have hr : 0 ≤ Real.sqrt (q - 1) := Real.sqrt_nonneg _
  have habs : |1 - Real.sqrt (q - 1)| ≤ 1 + Real.sqrt (q - 1) := by
    rw [abs_le]; constructor <;> linarith
  have hpow : (1 - Real.sqrt (q - 1)) ^ (2 * a) ≤ (1 + Real.sqrt (q - 1)) ^ (2 * a) := by
    calc (1 - Real.sqrt (q - 1)) ^ (2 * a)
        ≤ |1 - Real.sqrt (q - 1)| ^ (2 * a) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (1 + Real.sqrt (q - 1)) ^ (2 * a) :=
          pow_le_pow_left₀ (abs_nonneg _) habs (2 * a)
  linarith

lemma mat_pow_nonneg (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ k i j, 0 ≤ (M ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun c _ => mul_nonneg (ih i c) (hM c j))

lemma matT2_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matT2 q i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matT2] <;> linarith

lemma matA2_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matA2 q i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matA2] <;> linarith

lemma matM6_nonneg (q : ℝ) (hq : 1 ≤ q) : ∀ i j, 0 ≤ matM6 q i j := by
  intro i j
  have hT := matT2_nonneg q hq
  have hA := matA2_nonneg q hq
  have hTT : ∀ r c, 0 ≤ (matT2 q * matT2 q) r c := fun r c => by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hT r k) (hT k c))
  dsimp only [matM6]
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hTT i k) (hA k j))

lemma matT2_right_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ k : ℕ,
      (matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q ≤ (q + 4) ^ k * 2 ∧
      (matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q ≤ (q + 4) ^ k * q := by
  intro k
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ']
    have hnn := mat_pow_nonneg (matT2 q) (matT2_nonneg q hq) k
    have hstep0 : (matT2 q * matT2 q ^ k) 0 0 * 2 + (matT2 q * matT2 q ^ k) 0 1 * q =
        2 * ((matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q) +
        2 * ((matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hstep1 : (matT2 q * matT2 q ^ k) 1 0 * 2 + (matT2 q * matT2 q ^ k) 1 1 * q =
        2 * (q - 1) * ((matT2 q ^ k) 0 0 * 2 + (matT2 q ^ k) 0 1 * q) +
        q * ((matT2 q ^ k) 1 0 * 2 + (matT2 q ^ k) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hpow : 0 ≤ (q + 4) ^ k := by positivity
    rw [hstep0, hstep1, pow_succ']
    constructor <;> nlinarith

lemma matT2_left_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ k : ℕ,
      2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0 ≤ (q + 4) ^ k * 2 ∧
      2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1 ≤ (q + 4) ^ k * 1 := by
  intro k
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ]
    have hstep0 : 2 * (matT2 q ^ k * matT2 q) 0 0 + 1 * (matT2 q ^ k * matT2 q) 1 0 =
        (2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0) * 2 +
        (2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1) * (2 * (q - 1)) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hstep1 : 2 * (matT2 q ^ k * matT2 q) 0 1 + 1 * (matT2 q ^ k * matT2 q) 1 1 =
        (2 * (matT2 q ^ k) 0 0 + 1 * (matT2 q ^ k) 1 0) * 2 +
        (2 * (matT2 q ^ k) 0 1 + 1 * (matT2 q ^ k) 1 1) * q := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]; ring
    have hpow : 0 ≤ (q + 4) ^ k := by positivity
    rw [hstep0, hstep1, pow_succ]
    constructor <;> nlinarith

lemma trace_matT2_pow_le (q : ℝ) (hq : 1 ≤ q) (a : ℕ) (ha : 1 ≤ a) :
    (matT2 q ^ a).trace ≤ (q + 4) ^ a + 4 * (q + 4) ^ (a - 1) := by
  have hnn := mat_pow_nonneg (matT2 q) (matT2_nonneg q hq)
  have h11 : (matT2 q ^ a) 1 1 ≤ (q + 4) ^ a := by
    have hr := (matT2_right_vec_le q hq a).2
    have hnn10 : 0 ≤ (matT2 q ^ a) 1 0 * 2 := mul_nonneg (hnn a 1 0) (by norm_num)
    nlinarith
  have h00 : (matT2 q ^ a) 0 0 ≤ 4 * (q + 4) ^ (a - 1) := by
    have ha1 : a = (a - 1) + 1 := by omega
    conv_lhs => rw [ha1, pow_succ']
    have hmul : (matT2 q * matT2 q ^ (a - 1)) 0 0 =
        2 * (matT2 q ^ (a - 1)) 0 0 + 2 * (matT2 q ^ (a - 1)) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, matT2]
    rw [hmul]
    have hl := (matT2_left_vec_le q hq (a - 1)).1
    have hnn00 : 0 ≤ (matT2 q ^ (a - 1)) 0 0 := hnn (a - 1) 0 0
    have hnn10 : 0 ≤ (matT2 q ^ (a - 1)) 1 0 := hnn (a - 1) 1 0
    linarith
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  linarith

lemma matM6_right_vec_le (q : ℝ) (hq : 1 ≤ q) :
    ∀ t : ℕ,
      (matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q ≤ ((q + 6) ^ 3) ^ t * 2 ∧
      (matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q ≤ ((q + 6) ^ 3) ^ t * q := by
  intro t
  have h1step :
      (matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q ≤ (q + 6) ^ 3 * 2 ∧
      (matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q ≤ (q + 6) ^ 3 * q := by
    have h0 : (matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q =
        2 * q ^ 3 + 28 * q ^ 2 + 8 * q - 16 := by
      simp [matM6, matT2, matA2, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have h1 : (matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q =
        q ^ 4 + 16 * q ^ 3 + 16 * q ^ 2 - 48 * q + 16 := by
      simp [matM6, matT2, matA2, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [h0, h1]
    constructor <;> nlinarith [sq_nonneg q, sq_nonneg (q - 1)]
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    rcases ih with ⟨h0, h1⟩
    rw [pow_succ']
    have hnnM := matM6_nonneg q hq
    have hstep0 : (matM6 q * matM6 q ^ t) 0 0 * 2 + (matM6 q * matM6 q ^ t) 0 1 * q =
        (matM6 q) 0 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
        (matM6 q) 0 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hstep1 : (matM6 q * matM6 q ^ t) 1 0 * 2 + (matM6 q * matM6 q ^ t) 1 1 * q =
        (matM6 q) 1 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
        (matM6 q) 1 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    have hpow : 0 ≤ ((q + 6) ^ 3) ^ t := by positivity
    rw [hstep0, hstep1, pow_succ']
    constructor
    · calc (matM6 q) 0 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
           (matM6 q) 0 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q)
          ≤ (matM6 q) 0 0 * (((q + 6) ^ 3) ^ t * 2) + (matM6 q) 0 1 * (((q + 6) ^ 3) ^ t * q) := by
            exact add_le_add (mul_le_mul_of_nonneg_left h0 (hnnM 0 0)) (mul_le_mul_of_nonneg_left h1 (hnnM 0 1))
        _ = ((matM6 q) 0 0 * 2 + (matM6 q) 0 1 * q) * ((q + 6) ^ 3) ^ t := by ring
        _ ≤ ((q + 6) ^ 3 * 2) * ((q + 6) ^ 3) ^ t := mul_le_mul_of_nonneg_right h1step.1 hpow
        _ = (q + 6) ^ 3 * ((q + 6) ^ 3) ^ t * 2 := by ring
    · calc (matM6 q) 1 0 * ((matM6 q ^ t) 0 0 * 2 + (matM6 q ^ t) 0 1 * q) +
           (matM6 q) 1 1 * ((matM6 q ^ t) 1 0 * 2 + (matM6 q ^ t) 1 1 * q)
          ≤ (matM6 q) 1 0 * (((q + 6) ^ 3) ^ t * 2) + (matM6 q) 1 1 * (((q + 6) ^ 3) ^ t * q) := by
            exact add_le_add (mul_le_mul_of_nonneg_left h0 (hnnM 1 0)) (mul_le_mul_of_nonneg_left h1 (hnnM 1 1))
        _ = ((matM6 q) 1 0 * 2 + (matM6 q) 1 1 * q) * ((q + 6) ^ 3) ^ t := by ring
        _ ≤ ((q + 6) ^ 3 * q) * ((q + 6) ^ 3) ^ t := mul_le_mul_of_nonneg_right h1step.2 hpow
        _ = (q + 6) ^ 3 * ((q + 6) ^ 3) ^ t * q := by ring

lemma trace_matM6_pow_le (q : ℝ) (hq : 1 ≤ q) (t : ℕ) :
    (matM6 q ^ t).trace ≤ 2 * (q + 6) ^ (3 * t) := by
  have hnn := mat_pow_nonneg (matM6 q) (matM6_nonneg q hq) t
  obtain ⟨h0, h1⟩ := matM6_right_vec_le q hq t
  rw [← pow_mul] at h0 h1
  have h00 : (matM6 q ^ t) 0 0 ≤ (q + 6) ^ (3 * t) := by
    have hnn01 : 0 ≤ (matM6 q ^ t) 0 1 * q := mul_nonneg (hnn 0 1) (by linarith)
    nlinarith
  have h11 : (matM6 q ^ t) 1 1 ≤ (q + 6) ^ (3 * t) := by
    have hnn10 : 0 ≤ (matM6 q ^ t) 1 0 * 2 := mul_nonneg (hnn 1 0) (by norm_num)
    nlinarith
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  linarith

lemma mul_pow_shift (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ k : ℕ, (X * Y) ^ k * X = X * (Y * X) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc (X * Y) ^ (k + 1) * X
        = (X * Y) ^ k * (X * Y) * X := by rw [pow_succ]
      _ = ((X * Y) ^ k * X) * (Y * X) := by simp only [Matrix.mul_assoc]
      _ = X * (Y * X) ^ k * (Y * X) := by rw [ih]
      _ = X * (Y * X) ^ (k + 1) := by rw [pow_succ, Matrix.mul_assoc]

lemma trace_pow_mul_comm (X Y : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) :
    ((X * Y) ^ k).trace = ((Y * X) ^ k).trace := by
  cases k with
  | zero => rfl
  | succ k =>
    calc ((X * Y) ^ (k + 1)).trace
        = (((X * Y) ^ k * X) * Y).trace := by rw [pow_succ, Matrix.mul_assoc]
      _ = (Y * ((X * Y) ^ k * X)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * (X * (Y * X) ^ k)).trace := by rw [mul_pow_shift]
      _ = ((Y * X) * (Y * X) ^ k).trace := by rw [← Matrix.mul_assoc]
      _ = ((Y * X) ^ (k + 1)).trace := by rw [← pow_succ']


def idxShift (t : ℕ) (ht : 1 ≤ t) (shift : Fin 2) (k : ℕ) : Fin (6 * t) :=
  ⟨(k + shift.val) % (6 * t), Nat.mod_lt _ (by omega)⟩

def pairW (q : ℝ) (isMiss : Bool) (x y z : Fin 2) : ℝ :=
  if x = 1 ∧ y = 0 then q - 1
  else if y = 1 ∧ z = 0 ∧ (x = 1 ∨ !isMiss) then q - 1
  else 1

lemma sum_pairW_eq_mat (q : ℝ) (isMiss : Bool) (x z : Fin 2) :
    (∑ y : Fin 2, pairW q isMiss x y z) =
      if isMiss then matT2 q x z else matA2 q x z := by
  cases isMiss <;> fin_cases x <;> fin_cases z <;>
    simp [Fin.sum_univ_two, pairW, matT2, matA2] <;> ring

lemma sum_inKer_pair_bound (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m)
    (v : Fin 4 → Fin m → F2) (shift : Fin 2) (miss : Fin (3 * t) → Bool)
    (hmiss : ∀ j : Fin (3 * t), miss j = true →
      (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0) :
    let q : ℝ := (2 : ℝ) ^ m
    let M : Fin (3 * t) → Matrix (Fin 2) (Fin 2) ℝ :=
      fun j => if miss j then matT2 q else matA2 q
    (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        (q - 1) ^ (inKer v S)) ≤ (matProd (3 * t) M).trace ∧
    (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤ (matProd (3 * t) M).trace - (q - 1) ^ (3 * t) := by
  intro q M
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hq1_ge1 : (1 : ℝ) ≤ q - 1 := by linarith
  let W : Finset (Fin (6 * t)) → ℝ := fun S =>
    ∏ j : Fin (3 * t),
      pairW q (miss j)
        (if idxShift t ht shift (2 * j.val) ∈ S then 1 else 0)
        (if idxShift t ht shift (2 * j.val + 1) ∈ S then 1 else 0)
        (if idxShift t ht shift (2 * j.val + 2) ∈ S then 1 else 0)
  have hW_nonneg : ∀ S, 0 ≤ W S := by
    intro S
    refine Finset.prod_nonneg (fun j _ => ?_)
    dsimp only [pairW]
    split_ifs <;> linarith
  have hW_sum : (∑ S : Finset (Fin (6 * t)), W S) = (matProd (3 * t) M).trace := by
    rw [matProd_trace_eq_sum (3 * t) (by omega) M]
    let eS : Finset (Fin (6 * t)) ≃ (Fin (3 * t) → Fin 2) × (Fin (3 * t) → Fin 2) :=
      { toFun := fun S =>
          (fun j => if idxShift t ht shift (2 * j.val) ∈ S then 1 else 0,
           fun j => if idxShift t ht shift (2 * j.val + 1) ∈ S then 1 else 0)
        invFun := fun p => Finset.univ.filter (fun i : Fin (6 * t) =>
          let u := (i.val + 6 * t - shift.val) % (6 * t)
          have hu_lt : u < 6 * t := Nat.mod_lt _ (by omega)
          if u % 2 = 0 then p.1 ⟨u / 2, by omega⟩ = 1 else p.2 ⟨u / 2, by omega⟩ = 1)
        left_inv := fun S => by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          set u := (i.val + 6 * t - shift.val) % (6 * t)
          have hu_lt : u < 6 * t := Nat.mod_lt _ (by omega)
          have hu_add : (u + shift.val) % (6 * t) = i.val := by
            dsimp only [u]
            rw [Nat.mod_add_mod]
            have h1 : i.val + 6 * t - shift.val + shift.val = i.val + 6 * t := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
          by_cases hpar : u % 2 = 0
          · rw [ite_eq_left hpar]
            have hidx : idxShift t ht shift (2 * (u / 2)) = i := by
              ext; simp only [idxShift]
              have h2 : 2 * (u / 2) = u := by omega
              rw [h2]; exact hu_add
            rw [hidx]
            by_cases hi : i ∈ S <;> simp [hi]
          · rw [ite_eq_right hpar]
            have hidx : idxShift t ht shift (2 * (u / 2) + 1) = i := by
              ext; simp only [idxShift]
              have h2 : 2 * (u / 2) + 1 = u := by omega
              rw [h2]; exact hu_add
            rw [hidx]
            by_cases hi : i ∈ S <;> simp [hi]
        right_inv := fun p => by
          ext j
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
            have hu : ((2 * j.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) = 2 * j.val := by
              have hlt : 2 * j.val + shift.val < 6 * t ∨ (2 * j.val + shift.val = 6 * t) := by omega
              rcases hlt with hlt | heq
              · rw [Nat.mod_eq_of_lt hlt]
                have h1 : 2 * j.val + shift.val + 6 * t - shift.val = 2 * j.val + 6 * t := by omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · rw [heq, Nat.mod_self]
                have h1 : 0 + 6 * t - shift.val = 2 * j.val := by omega
                rw [h1, Nat.mod_eq_of_lt (by omega)]
            simp only [hu, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 2)]
            rcases fin2_cases (p.1 j) with h | h <;> simp [h]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
            have hu : ((2 * j.val + 1 + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) = 2 * j.val + 1 := by
              have hlt : 2 * j.val + 1 + shift.val < 6 * t ∨ 2 * j.val + 1 + shift.val = 6 * t := by omega
              rcases hlt with hlt | heq
              · rw [Nat.mod_eq_of_lt hlt]
                have h1 : 2 * j.val + 1 + shift.val + 6 * t - shift.val = 2 * j.val + 1 + 6 * t := by omega
                rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · rw [heq, Nat.mod_self]
                have h1 : 0 + 6 * t - shift.val = 2 * j.val + 1 := by omega
                rw [h1, Nat.mod_eq_of_lt (by omega)]
            have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
            have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
            simp only [hu, hodd, ↓reduceIte, hdiv]
            rcases fin2_cases (p.2 j) with h | h <;> simp [h] }
    rw [Fintype.sum_equiv eS W
      (fun p => ∏ j : Fin (3 * t), pairW q (miss j) (p.1 j) (p.2 j) (p.1 (nextIdx j)))
      (fun S => by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        dsimp only [eS, Equiv.coe_fn_mk]
        have hnxt : idxShift t ht shift (2 * (nextIdx j).val) = idxShift t ht shift (2 * j.val + 2) := by
          ext
          simp only [idxShift, nextIdx]
          by_cases hlast : j.val + 1 = 3 * t
          · rw [hlast, Nat.mod_self, Nat.mul_zero, Nat.zero_add]
            have h6 : 2 * j.val + 2 = 6 * t := by omega
            rw [h6, Nat.add_mod_left]
          · rw [Nat.mod_eq_of_lt (by omega : j.val + 1 < 3 * t)]
            have hmul2 : 2 * (j.val + 1) = 2 * j.val + 2 := by omega
            rw [hmul2]
        rw [hnxt])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    dsimp only
    rw [← Fintype.prod_sum (fun j y => pairW q (miss j) (x j) y (x (nextIdx j)))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [sum_pairW_eq_mat]; dsimp only [M]; split_ifs <;> rfl
  have hW_ge : ∀ S : Finset (Fin (6 * t)), S ≠ Finset.univ →
      (q - 1) ^ (inKer v S) ≤ W S := by
    intro S hne
    let Kset := (endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)
    have hKcard : inKer v S = Kset.card := rfl
    rw [hKcard]
    let f : Fin (3 * t) → ℕ := fun j =>
      (if idxShift t ht shift (2 * j.val) ∈ Kset then 1 else 0) +
      (if idxShift t ht shift (2 * j.val + 1) ∈ Kset then 1 else 0)
    have hsum_f : Kset.card = ∑ j : Fin (3 * t), f j := by
      have h1 : Kset.card = ∑ i : Fin (6 * t), if i ∈ Kset then 1 else 0 := by
        simp
      rw [h1]
      let eIdx : Fin (3 * t) × Fin 2 ≃ Fin (6 * t) :=
        { toFun := fun p => idxShift t ht shift (2 * p.1.val + p.2.val)
          invFun := fun i =>
            (⟨((i.val + 6 * t - shift.val) % (6 * t)) / 2,
              by have := Nat.mod_lt (i.val + 6 * t - shift.val) (by omega : 0 < 6 * t); omega⟩,
             ⟨((i.val + 6 * t - shift.val) % (6 * t)) % 2, Nat.mod_lt _ (by omega)⟩)
          left_inv := fun ⟨j, r⟩ => by
            ext
            · simp only [idxShift]
              have hu : ((2 * j.val + r.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) =
                  2 * j.val + r.val := by
                have hle : 2 * j.val + r.val + shift.val ≤ 6 * t := by omega
                rcases lt_or_eq_of_le hle with hlt | heq
                · rw [Nat.mod_eq_of_lt hlt]
                  have h1' : 2 * j.val + r.val + shift.val + 6 * t - shift.val = 2 * j.val + r.val + 6 * t := by omega
                  rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                · rw [heq, Nat.mod_self]
                  have h1' : 0 + 6 * t - shift.val = 2 * j.val + r.val := by omega
                  rw [h1', Nat.mod_eq_of_lt (by omega)]
              simp only [hu]; omega
            · simp only [idxShift]
              have hu : ((2 * j.val + r.val + shift.val) % (6 * t) + 6 * t - shift.val) % (6 * t) =
                  2 * j.val + r.val := by
                have hle : 2 * j.val + r.val + shift.val ≤ 6 * t := by omega
                rcases lt_or_eq_of_le hle with hlt | heq
                · rw [Nat.mod_eq_of_lt hlt]
                  have h1' : 2 * j.val + r.val + shift.val + 6 * t - shift.val = 2 * j.val + r.val + 6 * t := by omega
                  rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                · rw [heq, Nat.mod_self]
                  have h1' : 0 + 6 * t - shift.val = 2 * j.val + r.val := by omega
                  rw [h1', Nat.mod_eq_of_lt (by omega)]
              simp only [hu]; omega
          right_inv := fun i => by
            ext
            simp only [idxShift]
            set u := (i.val + 6 * t - shift.val) % (6 * t)
            have h2 : 2 * (u / 2) + u % 2 = u := by omega
            rw [h2]
            dsimp only [u]
            rw [Nat.mod_add_mod]
            have h1' : i.val + 6 * t - shift.val + shift.val = i.val + 6 * t := by omega
            rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt] }
      rw [← Equiv.sum_comp eIdx, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.sum_univ_two, f, eIdx, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, add_zero]
    rw [hsum_f, ← Finset.prod_pow_eq_pow_sum]
    have hprod_le : ∀ {ι : Type} (s : Finset ι) (a b : ι → ℝ),
        (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, a i ≤ b i) → (∏ i ∈ s, a i) ≤ ∏ i ∈ s, b i := by
      intro ι s a b ha hab
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.prod_insert hx]
        have ha_s : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
        have hprod_nn : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha_s
        have hxb : 0 ≤ b x := le_trans (ha x (Finset.mem_insert_self x s)) (hab x (Finset.mem_insert_self x s))
        exact mul_le_mul (hab x (Finset.mem_insert_self x s))
          (ih ha_s (fun i hi => hab i (Finset.mem_insert_of_mem hi))) hprod_nn hxb
    refine hprod_le (Finset.univ : Finset (Fin (3 * t))) _ _
      (fun j _ => pow_nonneg (by linarith only [hq2]) _) (fun j _ => ?_)
    let p0 := idxShift t ht shift (2 * j.val)
    let p1 := idxShift t ht shift (2 * j.val + 1)
    let p2 := idxShift t ht shift (2 * j.val + 2)
    have hnxt0 : nextIdx p0 = p1 := by
      ext; simp only [nextIdx, p0, p1, idxShift]; rw [Nat.mod_add_mod]; congr 1; omega
    have hnxt1 : nextIdx p1 = p2 := by
      ext; simp only [nextIdx, p1, p2, idxShift]; rw [Nat.mod_add_mod]; congr 1; omega
    have hprev1 : prevIdx p1 = p0 := by rw [← hnxt0, prevIdx_nextIdx]
    change (q - 1) ^ ((if p0 ∈ Kset then 1 else 0) + (if p1 ∈ Kset then 1 else 0)) ≤
      pairW q (miss j) (if p0 ∈ S then 1 else 0) (if p1 ∈ S then 1 else 0) (if p2 ∈ S then 1 else 0)
    by_cases hp0 : p0 ∈ Kset
    · have hp0e : p0 ∈ endsSet S := (Finset.mem_filter.mp hp0).1
      have hp0S : p0 ∈ S := (Finset.mem_filter.mp hp0e).1
      have hp1nS : p1 ∉ S := by rw [← hnxt0]; exact (Finset.mem_filter.mp hp0e).2
      have hp1nK : p1 ∉ Kset := fun h => hp1nS (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
      rw [ite_eq_left hp0, ite_eq_right hp1nK, Nat.add_zero, pow_one]
      dsimp only [pairW]
      rw [ite_eq_left hp0S, ite_eq_right hp1nS]
      simp
    · by_cases hp1 : p1 ∈ Kset
      · have hp1e : p1 ∈ endsSet S := (Finset.mem_filter.mp hp1).1
        have hp1k : (∑ b : Fin 4, runParity S p1 b • v b) = 0 := (Finset.mem_filter.mp hp1).2
        have hp1S : p1 ∈ S := (Finset.mem_filter.mp hp1e).1
        have hp2nS : p2 ∉ S := by rw [← hnxt1]; exact (Finset.mem_filter.mp hp1e).2
        rw [ite_eq_right hp0, ite_eq_left hp1, Nat.zero_add, pow_one]
        by_cases hp0S : p0 ∈ S
        · dsimp only [pairW]
          rw [ite_eq_left hp0S, ite_eq_left hp1S, ite_eq_right hp2nS]
          simp
        · have hsing : S.filter (fun i => runEnd S i = p1) = {p1} :=
            runEnd_singleton S hne p1 hp1e (by rw [hprev1]; exact hp0S)
          have hpar1 : ∀ b, runParity S p1 b = hMat p1 b := fun b => by
            simp [runParity, hsing]
          have hmiss_false : miss j = false := by
            cases hm_eq : miss j
            · rfl
            · exfalso
              apply hmiss j hm_eq
              simpa [hpar1, p1] using hp1k
          dsimp only [pairW]
          rw [ite_eq_right hp0S, ite_eq_left hp1S, ite_eq_right hp2nS, hmiss_false]
          simp
      · rw [ite_eq_right hp0, ite_eq_right hp1, Nat.add_zero, pow_zero]
        dsimp only [pairW]
        split_ifs <;> linarith only [hq1_ge1]
  have hW_lane : W (laneSet shift) = (q - 1) ^ (3 * t) := by
    have hterm : ∀ j : Fin (3 * t),
        pairW q (miss j)
          (if idxShift t ht shift (2 * j.val) ∈ laneSet shift then 1 else 0)
          (if idxShift t ht shift (2 * j.val + 1) ∈ laneSet shift then 1 else 0)
          (if idxShift t ht shift (2 * j.val + 2) ∈ laneSet shift then 1 else 0) = q - 1 := by
      intro j
      have h0 : idxShift t ht shift (2 * j.val) ∈ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
        have hmod : ((2 * j.val + shift.val) % (6 * t)) % 2 = (2 * j.val + shift.val) % 2 := by
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          exact Nat.mod_mod_of_dvd _ hdvd
        rw [hmod]; omega
      have h1 : idxShift t ht shift (2 * j.val + 1) ∉ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift]
        have hmod : ((2 * j.val + 1 + shift.val) % (6 * t)) % 2 = (2 * j.val + 1 + shift.val) % 2 := by
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          exact Nat.mod_mod_of_dvd _ hdvd
        rw [hmod]; omega
      simp [pairW, h0, h1]
    simp only [W, Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  constructor
  · calc ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), (q - 1) ^ inKer v S
        ≤ ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S :=
          Finset.sum_le_sum (fun S hS => hW_ge S (Finset.mem_erase.mp hS).1)
      _ ≤ ∑ S : Finset (Fin (6 * t)), W S :=
          Finset.sum_le_univ_sum_of_nonneg hW_nonneg
      _ = (matProd (3 * t) M).trace := hW_sum
  · have hlane_ne : laneSet shift ≠ (Finset.univ : Finset (Fin (6 * t))) := by
      intro h
      have hmem : idxShift t ht shift 1 ∈ laneSet shift := by rw [h]; exact Finset.mem_univ _
      simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift] at hmem
      have hmod : ((1 + shift.val) % (6 * t)) % 2 = (1 + shift.val) % 2 :=
        Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
      rw [hmod] at hmem
      omega
    have hsplit : (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift), W S) +
        W (laneSet shift) = ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S := by
      rw [add_comm]
      exact Finset.add_sum_erase _ W (Finset.mem_erase.mpr ⟨hlane_ne, Finset.mem_univ _⟩)
    have hle1 : (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift),
        (q - 1) ^ inKer v S) ≤
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift), W S :=
      Finset.sum_le_sum (fun S hS => hW_ge S (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1)
    have hle2 : ∑ S ∈ Finset.univ.erase (Finset.univ : Finset (Fin (6 * t))), W S ≤ (matProd (3 * t) M).trace := by
      rw [← hW_sum]; exact Finset.sum_le_univ_sum_of_nonneg hW_nonneg
    linarith [hW_lane]

lemma hMat_eval_sum {n m : ℕ} (v : Fin 4 → Fin m → F2) (i : Fin n) :
    (∑ b : Fin 4, hMat i b • v b) =
      if i.val % 2 = 0 then
        if i.val / 2 % 3 = 0 then v 0
        else if i.val / 2 % 3 = 1 then v 1
        else v 0 + v 1
      else
        if i.val / 2 % 3 = 0 then v 2
        else if i.val / 2 % 3 = 1 then v 3
        else v 2 + v 3 := by
  have hmod2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  have hmod3 : i.val / 2 % 3 = 0 ∨ i.val / 2 % 3 = 1 ∨ i.val / 2 % 3 = 2 := by omega
  rw [Fin.sum_univ_four]
  rcases hmod2 with h2 | h2 <;> rcases hmod3 with h3 | h3 | h3 <;>
    simp [hMat, h2, h3]

lemma bucket_R_inKer_le (t m : ℕ) (ht : 1 ≤ t) (v : Fin 4 → Fin m → F2)
    (hE : v 0 ≠ 0 ∨ v 1 ≠ 0) (hO : v 2 ≠ 0 ∨ v 3 ≠ 0)
    (S : Finset (Fin (6 * t))) (hne : S ≠ Finset.univ) :
    3 * inKer v S ≤ 8 * t := by
  let A := (endsSet S).filter (fun e => (∑ b : Fin 4, runParity S e b • v b) = 0)
  let A1 := A.filter (fun e => prevIdx e ∉ S)
  let A2 := A.filter (fun e => prevIdx e ∈ S)
  have hA_split : A.card = A1.card + A2.card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (p := fun e => prevIdx e ∈ S)
    dsimp only [A1, A2]
    omega
  have hA1_le : A1.card ≤ 2 * t := by
    let Bset := Finset.univ.filter (fun i : Fin (6 * t) => (∑ b : Fin 4, hMat i b • v b) = 0)
    have hsub : A1 ⊆ Bset := by
      intro e he
      simp only [A1, A, Finset.mem_filter] at he
      have hsing := runEnd_singleton S hne e he.1.1 he.2
      have hpar : ∀ b, runParity S e b = hMat e b := fun b => by simp [runParity, hsing]
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hpar] using he.1.2
    have hB_le : Bset.card ≤ 2 * t := by
      let e6 : Fin t × Fin 6 ≃ Fin (6 * t) :=
        { toFun := fun p => ⟨6 * p.1.val + p.2.val, by omega⟩
          invFun := fun i => (⟨i.val / 6, by omega⟩, ⟨i.val % 6, Nat.mod_lt _ (by omega)⟩)
          left_inv := fun ⟨a, b⟩ => by ext <;> simp <;> omega
          right_inv := fun i => by ext; simp; omega }
      have hcard : Bset.card = ∑ a : Fin t,
          (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card := by
        have h1 : Bset.card = ∑ i : Fin (6 * t), if (∑ b : Fin 4, hMat i b • v b) = 0 then 1 else 0 := by
          simp [Bset, Finset.sum_boole]
        rw [h1, ← Equiv.sum_comp e6, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp [Finset.sum_boole]
      rw [hcard]
      have hper : ∀ a : Fin t,
          (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card ≤ 2 := by
        intro a
        have hev0 : (∑ b : Fin 4, hMat (e6 (a, 0)) b • v b) = v 0 := by
          have ha1 : (e6 (a, 0)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 0)).val / 2 % 3 = 0 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hev1 : (∑ b : Fin 4, hMat (e6 (a, 2)) b • v b) = v 1 := by
          have ha1 : (e6 (a, 2)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 2)).val / 2 % 3 = 1 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hev2 : (∑ b : Fin 4, hMat (e6 (a, 4)) b • v b) = v 0 + v 1 := by
          have ha1 : (e6 (a, 4)).val % 2 = 0 := by simp [e6]; omega
          have ha2 : (e6 (a, 4)).val / 2 % 3 = 2 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd0 : (∑ b : Fin 4, hMat (e6 (a, 1)) b • v b) = v 2 := by
          have ha1 : (e6 (a, 1)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 1)).val / 2 % 3 = 0 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd1 : (∑ b : Fin 4, hMat (e6 (a, 3)) b • v b) = v 3 := by
          have ha1 : (e6 (a, 3)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 3)).val / 2 % 3 = 1 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        have hodd2 : (∑ b : Fin 4, hMat (e6 (a, 5)) b • v b) = v 2 + v 3 := by
          have ha1 : (e6 (a, 5)).val % 2 = 1 := by simp [e6]; omega
          have ha2 : (e6 (a, 5)).val / 2 % 3 = 2 := by simp [e6]; omega
          rw [hMat_eval_sum, ha1, ha2]; simp
        rw [Finset.card_filter, Fin.sum_univ_six, hev0, hodd0, hev1, hodd1, hev2, hodd2]
        have hE_le : (if v 0 = 0 then 1 else 0) + (if v 1 = 0 then 1 else 0) + (if v 0 + v 1 = 0 then 1 else 0) ≤ 1 := by
          by_cases hv0 : v 0 = 0 <;> by_cases hv1 : v 1 = 0
          · exfalso; rcases hE with h | h <;> exact h (by assumption)
          · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
            simp [hv0, hv1, hne01]
          · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
            simp [hv0, hv1, hne01]
          · simp [hv0, hv1]; split_ifs <;> omega
        have hO_le : (if v 2 = 0 then 1 else 0) + (if v 3 = 0 then 1 else 0) + (if v 2 + v 3 = 0 then 1 else 0) ≤ 1 := by
          by_cases hv2 : v 2 = 0 <;> by_cases hv3 : v 3 = 0
          · exfalso; rcases hO with h | h <;> exact h (by assumption)
          · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
            simp [hv2, hv3, hne23]
          · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
            simp [hv2, hv3, hne23]
          · simp [hv2, hv3]; split_ifs <;> omega
        omega
      calc ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 6 =>
            (∑ b : Fin 4, hMat (e6 (a, r)) b • v b) = 0)).card
          ≤ ∑ _a : Fin t, 2 := Finset.sum_le_sum (fun a _ => hper a)
        _ = 2 * t := by simp [mul_comm]
    exact le_trans (Finset.card_le_card hsub) hB_le
  have hdisj_pack : 2 * A1.card + 3 * A2.card ≤ 6 * t := by
    let U1 := A
    let U2 := A.image nextIdx
    let U3 := A2.image prevIdx
    have hcardU1 : U1.card = A1.card + A2.card := hA_split
    have hcardU2 : U2.card = A1.card + A2.card := by
      rw [Finset.card_image_of_injective _ nextIdx_injective, hA_split]
    have hcardU3 : U3.card = A2.card := Finset.card_image_of_injective _ prevIdx_injective
    have hd12 : Disjoint U1 U2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [U1, A, endsSet, Finset.mem_filter] at hx1
      rcases Finset.mem_image.mp hx2 with ⟨e, he, rfl⟩
      simp only [A, endsSet, Finset.mem_filter] at he
      exact he.1.2 hx1.1.1
    have hd13 : Disjoint U1 U3 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx3
      simp only [U1, A, endsSet, Finset.mem_filter] at hx1
      rcases Finset.mem_image.mp hx3 with ⟨e, he, rfl⟩
      simp only [A2, A, endsSet, Finset.mem_filter] at he
      have hnx := hx1.1.2
      rw [nextIdx_prevIdx] at hnx
      exact hnx he.1.1.1
    have hd23 : Disjoint U2 U3 := by
      rw [Finset.disjoint_left]
      intro x hx2 hx3
      rcases Finset.mem_image.mp hx2 with ⟨e1, he1, rfl⟩
      rcases Finset.mem_image.mp hx3 with ⟨e2, he2, heq⟩
      simp only [A, endsSet, Finset.mem_filter] at he1
      have h2 : prevIdx e2 ∈ S := (Finset.mem_filter.mp he2).2
      rw [heq] at h2
      exact he1.1.2 h2
    have hunion : (U1 ∪ U2 ∪ U3).card = U1.card + U2.card + U3.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12]
    have hle : (U1 ∪ U2 ∪ U3).card ≤ 6 * t := by
      calc (U1 ∪ U2 ∪ U3).card ≤ (Finset.univ : Finset (Fin (6 * t))).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 6 * t := by simp
    omega
  change 3 * A.card ≤ 8 * t
  omega

lemma inKer_lane_le (t m : ℕ) (ht : 1 ≤ t) (v : Fin 4 → Fin m → F2) (shift : Fin 2)
    (hne : if shift = 0 then (v 0 ≠ 0 ∨ v 1 ≠ 0) else (v 2 ≠ 0 ∨ v 3 ≠ 0)) :
    inKer v (laneSet shift : Finset (Fin (6 * t))) ≤ t := by
  have hlane_ne : laneSet shift ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : idxShift t ht shift 1 ∈ laneSet shift := by rw [h]; exact Finset.mem_univ _
    simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and, idxShift] at hmem
    have hmod : ((1 + shift.val) % (6 * t)) % 2 = (1 + shift.val) % 2 :=
      Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
    rw [hmod] at hmem
    omega
  have hends_eq : endsSet (laneSet shift : Finset (Fin (6 * t))) = laneSet shift := by
    ext i
    simp only [endsSet, laneSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    intro hi
    simp only [nextIdx]
    have hmod : ((i.val + 1) % (6 * t)) % 2 = (i.val + 1) % 2 :=
      Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
    rw [hmod]; omega
  have hpar_eq : ∀ i ∈ (laneSet shift : Finset (Fin (6 * t))), ∀ b,
      runParity (laneSet shift : Finset (Fin (6 * t))) i b = hMat i b := by
    intro i hi b
    have hprev : prevIdx i ∉ laneSet shift := by
      simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simp only [prevIdx]
      have hmod : ((i.val + 6 * t - 1) % (6 * t)) % 2 = (i.val + 6 * t - 1) % 2 :=
        Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩
      rw [hmod]; omega
    have hsing := runEnd_singleton (laneSet shift) hlane_ne i (by rw [hends_eq]; exact hi) hprev
    simp [runParity, hsing]
  have hcard : inKer v (laneSet shift : Finset (Fin (6 * t))) =
      ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card := by
    dsimp only [inKer]
    rw [hends_eq]
    congr 1
    refine Finset.filter_congr (fun i hi => ?_)
    simp [hpar_eq i hi]
  rw [hcard]
  let eL : Fin t × Fin 3 ≃ {i : Fin (6 * t) // i ∈ laneSet shift} :=
    { toFun := fun p => ⟨⟨6 * p.1.val + 2 * p.2.val + shift.val, by omega⟩, by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
      invFun := fun i =>
        have hi : i.1.val % 2 = shift.val := (Finset.mem_filter.mp i.2).2
        (⟨i.1.val / 6, by omega⟩, ⟨(i.1.val % 6) / 2, by omega⟩)
      left_inv := fun ⟨a, r⟩ => by ext <;> simp <;> omega
      right_inv := fun ⟨i, hi⟩ => by
        have hpar : i.val % 2 = shift.val := (Finset.mem_filter.mp hi).2
        ext; simp; omega }
  have hsum : ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card =
      ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
        (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card := by
    have h1 : ((laneSet shift : Finset (Fin (6 * t))).filter (fun i => (∑ b : Fin 4, hMat i b • v b) = 0)).card =
        ∑ i : {i : Fin (6 * t) // i ∈ laneSet shift},
          if (∑ b : Fin 4, hMat i.1 b • v b) = 0 then 1 else 0 := by
      rw [Finset.sum_coe_sort (laneSet shift : Finset (Fin (6 * t))) (fun i => if (∑ b : Fin 4, hMat i b • v b) = 0 then 1 else 0)]
      simp [Finset.sum_boole]
    rw [h1, ← Equiv.sum_comp eL, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [Finset.sum_boole]
  rw [hsum]
  have hper : ∀ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
      (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card ≤ 1 := by
    intro a
    fin_cases shift
    · simp only [↓reduceIte] at hne
      have h0 : (∑ b : Fin 4, hMat (eL (a, 0)).1 b • v b) = v 0 := by
        have ha1 : (eL (a, 0)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 0)).1.val / 2 % 3 = 0 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h1 : (∑ b : Fin 4, hMat (eL (a, 1)).1 b • v b) = v 1 := by
        have ha1 : (eL (a, 1)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 1)).1.val / 2 % 3 = 1 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h2 : (∑ b : Fin 4, hMat (eL (a, 2)).1 b • v b) = v 0 + v 1 := by
        have ha1 : (eL (a, 2)).1.val % 2 = 0 := by simp [eL]; omega
        have ha2 : (eL (a, 2)).1.val / 2 % 3 = 2 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      rw [Finset.card_filter, Fin.sum_univ_three, h0, h1, h2]
      by_cases hv0 : v 0 = 0 <;> by_cases hv1 : v 1 = 0
      · exfalso; rcases hne with h | h <;> exact h (by assumption)
      · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
        simp [hv0, hv1, hne01]
      · have hne01 : v 0 + v 1 ≠ 0 := by simp [hv0, hv1]
        simp [hv0, hv1, hne01]
      · simp [hv0, hv1]; split_ifs <;> omega
    · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hne
      have h0 : (∑ b : Fin 4, hMat (eL (a, 0)).1 b • v b) = v 2 := by
        have ha1 : (eL (a, 0)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 0)).1.val / 2 % 3 = 0 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h1 : (∑ b : Fin 4, hMat (eL (a, 1)).1 b • v b) = v 3 := by
        have ha1 : (eL (a, 1)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 1)).1.val / 2 % 3 = 1 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      have h2 : (∑ b : Fin 4, hMat (eL (a, 2)).1 b • v b) = v 2 + v 3 := by
        have ha1 : (eL (a, 2)).1.val % 2 = 1 := by simp [eL]; omega
        have ha2 : (eL (a, 2)).1.val / 2 % 3 = 2 := by simp [eL]; omega
        rw [hMat_eval_sum, ha1, ha2]; simp
      rw [Finset.card_filter, Fin.sum_univ_three, h0, h1, h2]
      by_cases hv2 : v 2 = 0 <;> by_cases hv3 : v 3 = 0
      · exfalso; rcases hne with h | h <;> exact h (by assumption)
      · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
        simp [hv2, hv3, hne23]
      · have hne23 : v 2 + v 3 ≠ 0 := by simp [hv2, hv3]
        simp [hv2, hv3, hne23]
      · simp [hv2, hv3]; split_ifs <;> omega
  calc ∑ a : Fin t, (Finset.univ.filter (fun r : Fin 3 =>
        (∑ b : Fin 4, hMat (eL (a, r)).1 b • v b) = 0)).card
      ≤ ∑ _a : Fin t, 1 := Finset.sum_le_sum (fun a _ => hper a)
    _ = t := by simp


lemma sum_bucket_E_or_O_nonlane (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) (shift : Fin 2) :
    let q : ℝ := (2 : ℝ) ^ m
    let Bset : Finset (Fin 4 → Fin m → F2) :=
      Finset.univ.filter (fun v =>
        v ≠ 0 ∧ (if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)))
    (1 / q ^ 4) * ∑ v ∈ Bset,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3 := by
  intro q Bset
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  let B1 := Bset.filter (fun v =>
    if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3)
    else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1))
  let B2 := Bset.filter (fun v =>
    ¬ (if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3)
       else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1)))
  have hsplit : ∑ v ∈ Bset,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) =
      (∑ v ∈ B1, ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) +
      (∑ v ∈ B2, ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Bset
      (fun v => if shift = 0 then (v 2 = 0 ∨ v 3 = 0 ∨ v 2 = v 3) else (v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1))]
  rw [hsplit, mul_add]
  have hB2_card : (B2.card : ℝ) ≤ q ^ 2 := by
    have hsub : B2 ⊆ Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
        if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)) := by
      intro v hv
      simp only [B2, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.1.2
    have hcard_eq : (Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
        if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))).card = (2 ^ m) ^ 2 := by
      have hcard_bij : (Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
          if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))).card =
          (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).card := by
        refine Finset.card_bij
          (fun v _ => if shift = 0 then (v 2, v 3) else (v 0, v 1)) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro v₁ hv₁ v₂ hv₂ heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
          rcases fin2_cases shift with rfl | rfl
          · simp only [↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
            ext b j; fin_cases b <;> dsimp only
            · simp [hv₁.1, hv₂.1]
            · simp [hv₁.2, hv₂.2]
            · exact congrFun heq.1 j
            · exact congrFun heq.2 j
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [h10, ↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
            ext b j; fin_cases b <;> dsimp only
            · exact congrFun heq.1 j
            · exact congrFun heq.2 j
            · simp [hv₁.1, hv₂.1]
            · simp [hv₁.2, hv₂.2]
        · intro ⟨u1, u2⟩ _
          rcases fin2_cases shift with rfl | rfl
          · refine ⟨fun b => if b = 2 then u1 else if b = 3 then u2 else 0, ?_, by simp⟩
            simp
          · refine ⟨fun b => if b = 0 then u1 else if b = 1 then u2 else 0, ?_, by simp⟩
            simp
      rw [hcard_bij]
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card,
        Finset.prod_const, sq]
    have hle : B2.card ≤ (2 ^ m) ^ 2 := le_trans (Finset.card_le_card hsub) (le_of_eq hcard_eq)
    dsimp only [q]
    exact_mod_cast hle
  have hB1_card : (B1.card : ℝ) ≤ 3 * q := by
    let U0 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) else (v 2 = 0 ∧ v 3 = 0 ∧ v 0 = 0))
    let U1 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 3 = 0) else (v 2 = 0 ∧ v 3 = 0 ∧ v 1 = 0))
    let U2 := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = v 3) else (v 2 = 0 ∧ v 3 = 0 ∧ v 0 = v 1))
    have hsub : B1 ⊆ U0 ∪ U1 ∪ U2 := by
      intro v hv
      simp only [B1, Bset, U0, U1, U2, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at hv ⊢
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv ⊢
        rcases hv.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inl (Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv ⊢
        rcases hv.2 with h | h | h
        · exact Or.inl (Or.inl ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inl (Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩)
        · exact Or.inr ⟨hv.1.2.1, hv.1.2.2, h⟩
    have hU0 : U0.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 3 else v 1)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U0, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · simp [hv₁.2.2, hv₂.2.2]
        · exact congrFun heq j
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.2.2, hv₂.2.2]
        · exact congrFun heq j
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hU1 : U1.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 2 else v 0)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U1, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · exact congrFun heq j
        · simp [hv₁.2.2, hv₂.2.2]
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · exact congrFun heq j
        · simp [hv₁.2.2, hv₂.2.2]
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hU2 : U2.card ≤ 2 ^ m := by
      refine le_trans (Finset.card_le_card_of_injOn (fun v => if shift = 0 then v 2 else v 0)
        (fun _ _ => Finset.mem_univ _) ?_) (by simp [Fintype.card_pi, ZMod.card])
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, U2, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
        · exact congrFun heq j
        · change v₁ 3 j = v₂ 3 j; rw [← hv₁.2.2, ← hv₂.2.2]; exact congrFun heq j
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv₁ hv₂ heq
        ext b j; fin_cases b <;> dsimp only
        · exact congrFun heq j
        · change v₁ 1 j = v₂ 1 j; rw [← hv₁.2.2, ← hv₂.2.2]; exact congrFun heq j
        · simp [hv₁.1, hv₂.1]
        · simp [hv₁.2.1, hv₂.2.1]
    have hle : B1.card ≤ 3 * 2 ^ m := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (U0 ∪ U1) U2
      have h3 := Finset.card_union_le U0 U1
      omega
    dsimp only [q]
    exact_mod_cast hle
  have hperB2 : ∀ v ∈ B2,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤
        (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) := by
    intro v hv
    simp only [B2, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hmiss : ∀ j : Fin (3 * t), (true : Bool) = true →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      intro j _
      rw [hMat_eval_sum]
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte, not_or] at hv
        rcases hv.2 with ⟨hv2, hv3, hv23⟩
        have hpar : (idxShift t ht 0 (2 * j.val + 1)).val % 2 = 1 := by
          simp only [idxShift, Fin.val_zero, add_zero]
          rw [Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 < 6 * t)]; omega
        simp only [hpar, one_ne_zero, ↓reduceIte]
        split_ifs
        · exact hv2
        · exact hv3
        · intro hsum
          apply hv23
          ext r
          have hr := congrFun hsum r
          simp only [Pi.add_apply, Pi.zero_apply] at hr
          rcases f2_eq_zero_or_one (v 2 r) with h0 | h1 <;>
            rcases f2_eq_zero_or_one (v 3 r) with h0' | h1' <;> simp_all
      · have h10 : (1 : Fin 2) ≠ 0 := by decide
        simp only [h10, ↓reduceIte, not_or] at hv
        rcases hv.2 with ⟨hv0, hv1, hv01⟩
        have hpar : (idxShift t ht 1 (2 * j.val + 1)).val % 2 = 0 := by
          simp only [idxShift, Fin.val_one]
          have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
          have hmod := Nat.mod_mod_of_dvd (2 * j.val + 1 + 1) hdvd
          rw [hmod]; omega
        simp only [hpar, ↓reduceIte]
        split_ifs
        · exact hv0
        · exact hv1
        · intro hsum
          apply hv01
          ext r
          have hr := congrFun hsum r
          simp only [Pi.add_apply, Pi.zero_apply] at hr
          rcases f2_eq_zero_or_one (v 0 r) with h0 | h1 <;>
            rcases f2_eq_zero_or_one (v 1 r) with h0' | h1' <;> simp_all
    have hb := (sum_inKer_pair_bound t m ht hm v shift (fun _ => true) hmiss).2
    simp only [↓reduceIte, matProd_const] at hb
    have htr := trace_matT2_pow_le q (by linarith) (3 * t) (by omega)
    linarith
  have hperB1 : ∀ v ∈ B1,
      (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S)) ≤ 2 * (q + 6) ^ (3 * t) := by
    intro v hv
    simp only [B1, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hex_c : ∃ c : Fin 3, ∀ j : Fin (3 * t), j.val % 3 ≠ c.val →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      rcases fin2_cases shift with rfl | rfl
      · simp only [↓reduceIte] at hv
        rcases hv with ⟨⟨hvne, hv0, hv1⟩, hcase⟩
        have hnotboth : ¬ (v 2 = 0 ∧ v 3 = 0) := by
          rintro ⟨h2, h3⟩; apply hvne; ext b j; fin_cases b <;> simp [hv0, hv1, h2, h3]
        have hpos : ∀ j : Fin (3 * t),
            (idxShift t ht 0 (2 * j.val + 1)).val % 2 = 1 ∧
            (idxShift t ht 0 (2 * j.val + 1)).val / 2 % 3 = j.val % 3 := by
          intro j
          simp only [idxShift, Fin.val_zero, add_zero, Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 < 6 * t)]
          omega
        rcases hcase with hv2 | hv3 | hv23
        · refine ⟨0, fun j hj => ?_⟩
          have hv3ne : v 3 ≠ 0 := fun h => hnotboth ⟨hv2, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_zero] at hj ⊢
          rw [ite_eq_right hj]
          split_ifs
          · exact hv3ne
          · simpa [hv2] using hv3ne
        · refine ⟨1, fun j hj => ?_⟩
          have hv2ne : v 2 ≠ 0 := fun h => hnotboth ⟨h, hv3⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_one] at hj ⊢
          rw [ite_eq_right hj]
          split_ifs
          · exact hv2ne
          · simpa [hv3] using hv2ne
        · refine ⟨2, fun j hj => ?_⟩
          have hv2ne : v 2 ≠ 0 := fun h => hnotboth ⟨h, hv23.symm.trans h⟩
          have hv3ne : v 3 ≠ 0 := fun h => hnotboth ⟨hv23.trans h, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [one_ne_zero, ↓reduceIte, Fin.val_two] at hj ⊢
          have h01 : j.val % 3 = 0 ∨ j.val % 3 = 1 := by omega
          rcases h01 with h0 | h1
          · simp [h0, hv2ne]
          · simp [h1, hv3ne]
      · simp only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, ↓reduceIte] at hv
        rcases hv with ⟨⟨hvne, hv2, hv3⟩, hcase⟩
        have hnotboth : ¬ (v 0 = 0 ∧ v 1 = 0) := by
          rintro ⟨h0, h1⟩; apply hvne; ext b j; fin_cases b <;> simp [hv2, hv3, h0, h1]
        have hpos : ∀ j : Fin (3 * t),
            (idxShift t ht 1 (2 * j.val + 1)).val % 2 = 0 ∧
            (idxShift t ht 1 (2 * j.val + 1)).val / 2 % 3 = (j.val + 1) % 3 := by
          intro j
          simp only [idxShift, Fin.val_one]
          by_cases hlast : j.val + 1 = 3 * t
          · have h6 : 2 * j.val + 1 + 1 = 6 * t := by omega
            rw [h6, Nat.mod_self]; omega
          · rw [Nat.mod_eq_of_lt (by omega : 2 * j.val + 1 + 1 < 6 * t)]; omega
        rcases hcase with hv0 | hv1 | hv01
        · refine ⟨2, fun j hj => ?_⟩
          have hv1ne : v 1 ≠ 0 := fun h => hnotboth ⟨hv0, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_two] at hj ⊢
          have hne0 : (j.val + 1) % 3 ≠ 0 := by omega
          rw [ite_eq_right hne0]
          split_ifs
          · exact hv1ne
          · simpa [hv0] using hv1ne
        · refine ⟨0, fun j hj => ?_⟩
          have hv0ne : v 0 ≠ 0 := fun h => hnotboth ⟨h, hv1⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_zero] at hj ⊢
          have hne1 : (j.val + 1) % 3 ≠ 1 := by omega
          rw [ite_eq_right hne1]
          split_ifs
          · exact hv0ne
          · simpa [hv1] using hv0ne
        · refine ⟨1, fun j hj => ?_⟩
          have hv0ne : v 0 ≠ 0 := fun h => hnotboth ⟨h, hv01.symm.trans h⟩
          have hv1ne : v 1 ≠ 0 := fun h => hnotboth ⟨hv01.trans h, h⟩
          rw [hMat_eval_sum, (hpos j).1, (hpos j).2]
          simp only [↓reduceIte, Fin.val_one] at hj ⊢
          have h01 : (j.val + 1) % 3 = 0 ∨ (j.val + 1) % 3 = 1 := by omega
          rcases h01 with h0 | h1
          · simp [h0, hv0ne]
          · simp [h1, hv1ne]
    obtain ⟨c, hc⟩ := hex_c
    let miss : Fin (3 * t) → Bool := fun j => decide (j.val % 3 ≠ c.val)
    have hmiss : ∀ j : Fin (3 * t), miss j = true →
        (∑ b : Fin 4, hMat (idxShift t ht shift (2 * j.val + 1)) b • v b) ≠ 0 := by
      intro j hj
      exact hc j (of_decide_eq_true hj)
    have hb := (sum_inKer_pair_bound t m ht hm v shift miss hmiss).1
    have hsub_sum :
        (∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
          (q - 1) ^ (inKer v S)) ≤
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
          (q - 1) ^ (inKer v S) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by
        exact pow_nonneg (by linarith) _)
    have htr_eq : (matProd (3 * t) (fun j => if miss j then matT2 q else matA2 q)).trace =
        (matM6 q ^ t).trace := by
      rcases c with ⟨cv, hcv⟩
      interval_cases cv
      · rw [matProd_period3 (matA2 q) (matT2 q) (matT2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        have h1 : matA2 q * matT2 q * matT2 q = matA2 q * (matT2 q * matT2 q) := Matrix.mul_assoc _ _ _
        rw [h1, trace_pow_mul_comm]
        rfl
      · rw [matProd_period3 (matT2 q) (matA2 q) (matT2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        rw [trace_pow_mul_comm (matT2 q * matA2 q) (matT2 q)]
        have h1 : matT2 q * (matT2 q * matA2 q) = matM6 q := by
          simp [matM6, Matrix.mul_assoc]
        rw [h1]
      · rw [matProd_period3 (matT2 q) (matT2 q) (matA2 q) t _ (fun j => by
          dsimp only [miss]
          have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
          rcases h3 with h | h | h <;> simp [h])]
        rfl
    exact le_trans hsub_sum (le_trans hb (by rw [htr_eq]; exact trace_matM6_pow_le q (by linarith) t))
  have hB2_nn : 0 ≤ (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) := by
    have h1 : (q - 1) ^ (3 * t) ≤ (q + 4) ^ (3 * t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (3 * t)
    have h2 : 0 ≤ 4 * (q + 4) ^ (3 * t - 1) := by positivity
    linarith
  have hsumB2 : (1 / q ^ 4) * ∑ v ∈ B2,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 := by
    calc (1 / q ^ 4) * ∑ v ∈ B2,
          ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
            (q - 1) ^ (inKer v S)
        ≤ (1 / q ^ 4) * ∑ _v ∈ B2,
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) := by
          gcongr with v hv; exact hperB2 v hv
      _ = (1 / q ^ 4) * ((B2.card : ℝ) *
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / q ^ 4) * (q ^ 2 *
          ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t))) := by
          gcongr
      _ = ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 := by
          field_simp [ne_of_gt hqpos]
  have hsumB1 : (1 / q ^ 4) * ∑ v ∈ B1,
      ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
        (q - 1) ^ (inKer v S) ≤
      6 * (q + 6) ^ (3 * t) / q ^ 3 := by
    calc (1 / q ^ 4) * ∑ v ∈ B1,
          ∑ S ∈ ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).erase (laneSet shift)),
            (q - 1) ^ (inKer v S)
        ≤ (1 / q ^ 4) * ∑ _v ∈ B1, (2 * (q + 6) ^ (3 * t)) := by
          gcongr with v hv; exact hperB1 v hv
      _ = (1 / q ^ 4) * ((B1.card : ℝ) * (2 * (q + 6) ^ (3 * t))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / q ^ 4) * ((3 * q) * (2 * (q + 6) ^ (3 * t))) := by
          gcongr
      _ = 6 * (q + 6) ^ (3 * t) / q ^ 3 := by
          field_simp [ne_of_gt hqpos]; ring
  linarith

lemma sum_bucket_R (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    let q : ℝ := (2 : ℝ) ^ m
    let Rset : Finset (Fin 4 → Fin m → F2) :=
      Finset.univ.filter (fun v => (v 0 ≠ 0 ∨ v 1 ≠ 0) ∧ (v 2 ≠ 0 ∨ v 3 ≠ 0))
    (1 / q ^ 4) * ∑ v ∈ Rset,
      ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        (q - 1) ^ (inKer v S) ≤
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
  intro q Rset
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  have hR_card : (Rset.card : ℝ) ≤ q ^ 4 := by
    have h1 : Rset.card ≤ Fintype.card (Fin 4 → Fin m → F2) := Finset.card_le_univ _
    have h2 : Fintype.card (Fin 4 → Fin m → F2) = (2 ^ m) ^ 4 := by
      simp [Fintype.card_pi, ZMod.card]
    rw [h2] at h1
    dsimp only [q]
    exact_mod_cast h1
  have hS_card : ((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card : ℝ) ≤ (2 : ℝ) ^ (6 * t) := by
    have h1 : (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card ≤
        Fintype.card (Finset (Fin (6 * t))) := Finset.card_le_univ _
    have h2 : Fintype.card (Finset (Fin (6 * t))) = 2 ^ (6 * t) := by simp
    rw [h2] at h1
    exact_mod_cast h1
  have hper : ∀ v ∈ Rset, ∀ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
      (q - 1) ^ (inKer v S) ≤ q ^ (3 * t - t / 3) := by
    intro v hv S hS
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have h3 := bucket_R_inKer_le t m ht v hv.1 hv.2 S (Finset.mem_erase.mp hS).1
    have hle : inKer v S ≤ 3 * t - t / 3 := by omega
    calc (q - 1) ^ (inKer v S)
        ≤ q ^ (inKer v S) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ q ^ (3 * t - t / 3) := pow_le_pow_right₀ (by linarith) hle
  calc (1 / q ^ 4) * ∑ v ∈ Rset,
        ∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))), (q - 1) ^ (inKer v S)
      ≤ (1 / q ^ 4) * ∑ _v ∈ Rset,
        ∑ _S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))), q ^ (3 * t - t / 3) := by
        gcongr with v hv S hS; exact hper v hv S hS
    _ = (1 / q ^ 4) * ((Rset.card : ℝ) * (((Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))).card : ℝ) *
          q ^ (3 * t - t / 3))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / q ^ 4) * (q ^ 4 * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3))) := by
        gcongr
    _ = (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
        field_simp [ne_of_gt hqpos]

lemma validCols_fourier_diff_sum (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    let q : ℝ := (2 : ℝ) ^ m
    let modelM : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then q ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then q ^ (3 * t - 2) else 0) +
      (q - 1) ^ (runsCard S) / q ^ 4
    (∑ S ∈ (Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))),
        |((validCols (6 * t) m S).card : ℝ) - modelM S|) ≤
      2 * (q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t) +
      2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3) +
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
  intro q modelM
  have hq2 : (2 : ℝ) ≤ q := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa [q] using this
  have hqpos : (0 : ℝ) < q := by linarith
  have hlane_ne0 : laneSet (0 : Fin 2) ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : (⟨1, by omega⟩ : Fin (6 * t)) ∈ laneSet 0 := by rw [h]; exact Finset.mem_univ _
    simp [laneSet] at hmem
  have hlane_ne1 : laneSet (1 : Fin 2) ≠ (Finset.univ : Finset (Fin (6 * t))) := by
    intro h
    have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ laneSet 1 := by rw [h]; exact Finset.mem_univ _
    simp [laneSet] at hmem
  have hlane01 : (laneSet (0 : Fin 2) : Finset (Fin (6 * t))) ≠ laneSet (1 : Fin 2) := by
    intro h
    have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ (laneSet (1 : Fin 2) : Finset (Fin (6 * t))) := by
      rw [← h]; simp [laneSet]
    simp [laneSet] at hmem
  let Eset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ v 0 = 0 ∧ v 1 = 0)
  let Oset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ v 2 = 0 ∧ v 3 = 0)
  let Rset : Finset (Fin 4 → Fin m → F2) :=
    Finset.univ.filter (fun v => (v 0 ≠ 0 ∨ v 1 ≠ 0) ∧ (v 2 ≠ 0 ∨ v 3 ≠ 0))
  have hpartV : ∀ f : (Fin 4 → Fin m → F2) → ℝ,
      (∑ v : Fin 4 → Fin m → F2, f v) =
        f 0 + (∑ v ∈ Eset, f v) + (∑ v ∈ Oset, f v) + (∑ v ∈ Rset, f v) := by
    intro f
    have hd0E : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Eset := by
      simp [Eset]
    have hd0O : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Oset := by
      simp [Oset]
    have hd0R : Disjoint ({0} : Finset (Fin 4 → Fin m → F2)) Rset := by
      simp [Rset]
    have hdEO : Disjoint Eset Oset := by
      rw [Finset.disjoint_left]
      intro v hE hO
      simp only [Eset, Oset, Finset.mem_filter, Finset.mem_univ, true_and] at hE hO
      apply hE.1; ext b j; fin_cases b <;> simp [hE.2.1, hE.2.2, hO.2.1, hO.2.2]
    have hdER : Disjoint Eset Rset := by
      rw [Finset.disjoint_left]
      intro v hE hR
      simp only [Eset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hE hR
      rcases hR.1 with h | h
      · exact h hE.2.1
      · exact h hE.2.2
    have hdOR : Disjoint Oset Rset := by
      rw [Finset.disjoint_left]
      intro v hO hR
      simp only [Oset, Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hO hR
      rcases hR.2 with h | h
      · exact h hO.2.1
      · exact h hO.2.2
    have huniv : ({0} : Finset (Fin 4 → Fin m → F2)) ∪ Eset ∪ Oset ∪ Rset = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_singleton, Eset, Oset, Rset, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      by_cases h0 : v = 0
      · exact Or.inl (Or.inl (Or.inl h0))
      · by_cases hE : v 0 = 0 ∧ v 1 = 0
        · exact Or.inl (Or.inl (Or.inr ⟨h0, hE⟩))
        · by_cases hO : v 2 = 0 ∧ v 3 = 0
          · exact Or.inl (Or.inr ⟨h0, hO⟩)
          · rw [not_and_or] at hE hO
            exact Or.inr ⟨hE, hO⟩
    rw [← huniv,
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd0R, hdER⟩, hdOR⟩),
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hd0O, hdEO⟩),
      Finset.sum_union hd0E, Finset.sum_singleton]
  let FT : (Fin 4 → Fin m → F2) → Finset (Fin (6 * t)) → ℝ := fun v S =>
    ∏ e ∈ endsSet S,
      if (∑ b : Fin 4, runParity S e b • v b) = 0 then (q - 1) else (-1 : ℝ)
  have hFT0 : ∀ S, FT 0 S = (q - 1) ^ (runsCard S) := by
    intro S; simp [FT, runsCard]
  have hFT_abs : ∀ v S, |FT v S| = (q - 1) ^ (inKer v S) :=
    fun v S => abs_fourier_term_eq (6 * t) m hm v S
  have hlane_err : ∀ shift : Fin 2,
      |((validCols (6 * t) m (laneSet shift)).card : ℝ) - modelM (laneSet shift)| ≤
        q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t := by
    intro shift
    have hne : (laneSet shift : Finset (Fin (6 * t))) ≠ Finset.univ := by
      rcases fin2_cases shift with rfl | rfl
      · exact hlane_ne0
      · exact hlane_ne1
    rw [validCols_card_eq_fourier (6 * t) m (laneSet shift) hne]
    change |(1 / q ^ 4) * (∑ v : Fin 4 → Fin m → F2, FT v (laneSet shift)) - modelM (laneSet shift)| ≤ _
    have hends : endsSet (laneSet shift : Finset (Fin (6 * t))) = laneSet shift := by
      ext i
      simp only [endsSet, laneSet, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro hi; simp only [nextIdx]
      rw [Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩]; omega
    have hruns : runsCard (laneSet shift : Finset (Fin (6 * t))) = 3 * t := by
      rw [runsCard, hends]
      let eL : Fin (3 * t) ≃ {i : Fin (6 * t) // i ∈ laneSet shift} :=
        { toFun := fun j => ⟨⟨2 * j.val + shift.val, by omega⟩, by simp [laneSet]; omega⟩
          invFun := fun i => ⟨i.1.val / 2, by omega⟩
          left_inv := fun j => by ext; simp; omega
          right_inv := fun ⟨i, hi⟩ => by
            have hpar : i.val % 2 = shift.val := (Finset.mem_filter.mp hi).2
            ext; simp; omega }
      rw [← Fintype.card_coe, ← Fintype.card_congr eL, Fintype.card_fin]
    have hpar_lane : ∀ i ∈ (laneSet shift : Finset (Fin (6 * t))), ∀ b,
        runParity (laneSet shift : Finset (Fin (6 * t))) i b = hMat i b := by
      intro i hi b
      have hprev : prevIdx i ∉ laneSet shift := by
        simp only [laneSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        simp only [prevIdx]
        rw [Nat.mod_mod_of_dvd _ ⟨3 * t, by ring⟩]; omega
      have hsing := runEnd_singleton (laneSet shift) hne i (by rw [hends]; exact hi) hprev
      simp [runParity, hsing]
    let mainV := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))
    let restV := Finset.univ.filter (fun v : Fin 4 → Fin m → F2 =>
      ¬ (if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0)))
    have hsplitV : (∑ v : Fin 4 → Fin m → F2, FT v (laneSet shift)) =
        (∑ v ∈ mainV, FT v (laneSet shift)) + (∑ v ∈ restV, FT v (laneSet shift)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v : Fin 4 → Fin m → F2 => if shift = 0 then (v 0 = 0 ∧ v 1 = 0) else (v 2 = 0 ∧ v 3 = 0))
        (fun v => FT v (laneSet shift))).symm
    have hmain_val : (∑ v ∈ mainV, FT v (laneSet shift)) = q ^ 2 * (q - 1) ^ (3 * t) := by
      have hconst : ∀ v ∈ mainV, FT v (laneSet shift) = (q - 1) ^ (3 * t) := by
        intro v hv
        simp only [mainV, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        dsimp only [FT]
        have hzero : ∀ e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))),
            (∑ b : Fin 4, runParity (laneSet shift : Finset (Fin (6 * t))) e b • v b) = 0 := by
          intro e he
          have heL : e ∈ (laneSet shift : Finset (Fin (6 * t))) := by rw [← hends]; exact he
          simp_rw [hpar_lane e heL]
          rw [hMat_eval_sum]
          have hpar := (Finset.mem_filter.mp heL).2
          rcases fin2_cases shift with rfl | rfl
          · simp only [Fin.val_zero, ↓reduceIte] at hpar hv ⊢
            rw [ite_eq_left hpar]; split_ifs <;> simp [hv.1, hv.2]
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [Fin.val_one, h10, ↓reduceIte] at hpar hv ⊢
            rw [ite_eq_right (by omega : e.val % 2 ≠ 0)]; split_ifs <;> simp [hv.1, hv.2]
        have hprod : (∏ e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))),
            if (∑ b : Fin 4, runParity (laneSet shift : Finset (Fin (6 * t))) e b • v b) = 0 then (q - 1) else (-1 : ℝ)) =
            ∏ _e ∈ endsSet (laneSet shift : Finset (Fin (6 * t))), (q - 1) :=
          Finset.prod_congr rfl (fun e he => by rw [ite_eq_left (hzero e he)])
        rw [hprod, Finset.prod_const, ← runsCard, hruns]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard_main : mainV.card = (2 ^ m) ^ 2 := by
        have hcard_bij : mainV.card = (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).card := by
          refine Finset.card_bij
            (fun v _ => if shift = 0 then (v 2, v 3) else (v 0, v 1)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro v₁ hv₁ v₂ hv₂ heq
            simp only [mainV, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
            rcases fin2_cases shift with rfl | rfl
            · simp only [↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
              ext b j; fin_cases b <;> dsimp only
              · simp [hv₁.1, hv₂.1]
              · simp [hv₁.2, hv₂.2]
              · exact congrFun heq.1 j
              · exact congrFun heq.2 j
            · have h10 : (1 : Fin 2) ≠ 0 := by decide
              simp only [h10, ↓reduceIte, Prod.mk.injEq] at hv₁ hv₂ heq
              ext b j; fin_cases b <;> dsimp only
              · exact congrFun heq.1 j
              · exact congrFun heq.2 j
              · simp [hv₁.1, hv₂.1]
              · simp [hv₁.2, hv₂.2]
          · intro ⟨u1, u2⟩ _
            rcases fin2_cases shift with rfl | rfl
            · refine ⟨fun b => if b = 2 then u1 else if b = 3 then u2 else 0, by simp [mainV], by simp⟩
            · have h10 : (1 : Fin 2) ≠ 0 := by decide
              refine ⟨fun b => if b = 0 then u1 else if b = 1 then u2 else 0,
                by simp [mainV, h10], by simp [h10]⟩
        rw [hcard_bij]
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card,
          Finset.prod_const, sq]
      have hcast : (mainV.card : ℝ) = q ^ 2 := by rw [hcard_main]; push_cast; rfl
      rw [hcast]
    have hrest_le : |(1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift)| ≤ q ^ t := by
      have hcard_rest : (restV.card : ℝ) ≤ q ^ 4 := by
        have h1 : restV.card ≤ Fintype.card (Fin 4 → Fin m → F2) := Finset.card_le_univ _
        have h2 : Fintype.card (Fin 4 → Fin m → F2) = (2 ^ m) ^ 4 := by
          simp [Fintype.card_pi, ZMod.card]
        rw [h2] at h1
        have h1r : (restV.card : ℝ) ≤ ((2 : ℝ) ^ m) ^ 4 := by exact_mod_cast h1
        exact h1r
      have hper : ∀ v ∈ restV, |FT v (laneSet shift)| ≤ q ^ t := by
        intro v hv
        rw [hFT_abs]
        simp only [restV, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hneV : if shift = 0 then (v 0 ≠ 0 ∨ v 1 ≠ 0) else (v 2 ≠ 0 ∨ v 3 ≠ 0) := by
          rcases fin2_cases shift with rfl | rfl
          · simp only [↓reduceIte, not_and_or] at hv ⊢; exact hv
          · have h10 : (1 : Fin 2) ≠ 0 := by decide
            simp only [h10, ↓reduceIte, not_and_or] at hv ⊢; exact hv
        have hle := inKer_lane_le t m ht v shift hneV
        calc (q - 1) ^ inKer v (laneSet shift)
            ≤ q ^ inKer v (laneSet shift) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ q ^ t := pow_le_pow_right₀ (by linarith) hle
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q ^ 4)]
      calc (1 / q ^ 4) * |∑ v ∈ restV, FT v (laneSet shift)|
          ≤ (1 / q ^ 4) * ∑ v ∈ restV, |FT v (laneSet shift)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / q ^ 4) * ∑ _v ∈ restV, q ^ t := by
            gcongr with v hv; exact hper v hv
        _ = (1 / q ^ 4) * ((restV.card : ℝ) * q ^ t) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 / q ^ 4) * (q ^ 4 * q ^ t) := by gcongr
        _ = q ^ t := by field_simp [ne_of_gt hqpos]
    have hmod_val : modelM (laneSet shift) = q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4 := by
      dsimp only [modelM]
      rw [hruns]
      rcases fin2_cases shift with rfl | rfl
      · simp [hlane01]
      · simp [hlane01.symm]
    rw [hsplitV, hmain_val, mul_add, hmod_val]
    have hpow_diff : q ^ (3 * t) - (q - 1) ^ (3 * t) ≤ (3 * (t : ℝ)) * q ^ (3 * t - 1) := by
      have hgen : ∀ k : ℕ, 1 ≤ k → q ^ k - (q - 1) ^ k ≤ (k : ℝ) * q ^ (k - 1) := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          cases k with
          | zero => simp
          | succ k =>
            have hih := ih (by omega)
            have h1 : q ^ (k + 2) - (q - 1) ^ (k + 2) =
                q * (q ^ (k + 1) - (q - 1) ^ (k + 1)) + (q - 1) ^ (k + 1) := by ring
            have h2 : (q - 1) ^ (k + 1) ≤ q ^ (k + 1) :=
              pow_le_pow_left₀ (by linarith) (by linarith) (k + 1)
            have h3 : q * ((k + 1 : ℕ) * q ^ k) = (k + 1 : ℕ) * q ^ (k + 1) := by
              rw [pow_succ']; ring
            have h4 : (k + 1 : ℕ) * q ^ (k + 1) + q ^ (k + 1) = ((k + 2 : ℕ) : ℝ) * q ^ (k + 1) := by
              push_cast; ring
            simp only [Nat.add_sub_cancel] at hih ⊢
            nlinarith
      have h := hgen (3 * t) (by omega)
      push_cast at h
      exact h
    have hpow_le : (q - 1) ^ (3 * t) ≤ q ^ (3 * t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) (3 * t)
    have hpow_eq1 : q ^ (3 * t - 2) * q ^ 2 = q ^ (3 * t) := by
      rw [← pow_add]; congr 1; omega
    have hpow_eq2 : q ^ (3 * t - 2) * q = q ^ (3 * t - 1) := by
      rw [← pow_succ]; congr 1; omega
    have hmain_diff : |(1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) -
        (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4)| ≤
        q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) := by
      have h1 : (1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) = (q - 1) ^ (3 * t) / q ^ 2 := by
        field_simp [ne_of_gt hqpos]
      rw [h1]
      have hneg : (q - 1) ^ (3 * t) / q ^ 2 - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4) ≤ 0 := by
        have hle1 : (q - 1) ^ (3 * t) / q ^ 2 ≤ q ^ (3 * t - 2) := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < q ^ 2), hpow_eq1]; exact hpow_le
        have hnn2 : 0 ≤ (q - 1) ^ (3 * t) / q ^ 4 :=
          div_nonneg (pow_nonneg (by linarith only [hq2]) _) (by positivity)
        linarith
      rw [abs_of_nonpos hneg]
      have hpart1 : q ^ (3 * t - 2) - (q - 1) ^ (3 * t) / q ^ 2 ≤ q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q) := by
        have h := div_le_div_of_nonneg_right hpow_diff (by positivity : (0 : ℝ) ≤ q ^ 2)
        have hL : (q ^ (3 * t) - (q - 1) ^ (3 * t)) / q ^ 2 =
            q ^ (3 * t - 2) - (q - 1) ^ (3 * t) / q ^ 2 := by
          rw [← hpow_eq1]; field_simp [ne_of_gt hqpos]
        have hR : (3 * (t : ℝ) * q ^ (3 * t - 1)) / q ^ 2 = q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q) := by
          rw [← hpow_eq2]; field_simp [ne_of_gt hqpos]
        linarith
      have hpart2 : (q - 1) ^ (3 * t) / q ^ 4 ≤ q ^ (3 * t - 2) * (1 / q ^ 2) := by
        have h := div_le_div_of_nonneg_right hpow_le (by positivity : (0 : ℝ) ≤ q ^ 4)
        have hR : q ^ (3 * t) / q ^ 4 = q ^ (3 * t - 2) * (1 / q ^ 2) := by
          rw [← hpow_eq1]; field_simp [ne_of_gt hqpos]
        linarith
      linarith
    have htri := abs_add_le
      ((1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4))
      ((1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift))
    have hrew : (1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) + (1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift) -
        (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4) =
        ((1 / q ^ 4) * (q ^ 2 * (q - 1) ^ (3 * t)) - (q ^ (3 * t - 2) + (q - 1) ^ (3 * t) / q ^ 4)) +
        (1 / q ^ 4) * ∑ v ∈ restV, FT v (laneSet shift) := by ring
    rw [hrew]
    linarith
  let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
  let Srest := (SnonU.erase (laneSet 0)).erase (laneSet 1)
  have hS_split :
      (∑ S ∈ SnonU, |((validCols (6 * t) m S).card : ℝ) - modelM S|) =
        |((validCols (6 * t) m (laneSet 0)).card : ℝ) - modelM (laneSet 0)| +
        |((validCols (6 * t) m (laneSet 1)).card : ℝ) - modelM (laneSet 1)| +
        ∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S| := by
    have hmem0 : laneSet 0 ∈ SnonU := Finset.mem_erase.mpr ⟨hlane_ne0, Finset.mem_univ _⟩
    have hmem1 : laneSet 1 ∈ SnonU.erase (laneSet 0) :=
      Finset.mem_erase.mpr ⟨hlane01.symm, Finset.mem_erase.mpr ⟨hlane_ne1, Finset.mem_univ _⟩⟩
    rw [← Finset.add_sum_erase SnonU _ hmem0,
      ← Finset.add_sum_erase (SnonU.erase (laneSet 0)) _ hmem1, add_assoc]
  rw [hS_split]
  have hrest_per : ∀ S ∈ Srest,
      |((validCols (6 * t) m S).card : ℝ) - modelM S| ≤
        (1 / q ^ 4) * (∑ v ∈ Eset, (q - 1) ^ inKer v S) +
        (1 / q ^ 4) * (∑ v ∈ Oset, (q - 1) ^ inKer v S) +
        (1 / q ^ 4) * (∑ v ∈ Rset, (q - 1) ^ inKer v S) := by
    intro S hS
    have hne1 : S ≠ laneSet 1 := (Finset.mem_erase.mp hS).1
    have hS1 := (Finset.mem_erase.mp hS).2
    have hne0 : S ≠ laneSet 0 := (Finset.mem_erase.mp hS1).1
    have hneU : S ≠ Finset.univ := (Finset.mem_erase.mp (Finset.mem_erase.mp hS1).2).1
    rw [validCols_card_eq_fourier (6 * t) m S hneU]
    change |(1 / q ^ 4) * (∑ v : Fin 4 → Fin m → F2, FT v S) - modelM S| ≤ _
    rw [hpartV (fun v => FT v S), hFT0 S]
    have hmod : modelM S = (1 / q ^ 4) * (q - 1) ^ (runsCard S) := by
      simp [modelM, hne0, hne1]; ring
    rw [hmod]
    have hsimp : (1 / q ^ 4) * ((q - 1) ^ runsCard S + (∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S) +
          (∑ v ∈ Rset, FT v S)) - (1 / q ^ 4) * (q - 1) ^ runsCard S =
        (1 / q ^ 4) * ((∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S) + (∑ v ∈ Rset, FT v S)) := by ring
    rw [hsimp, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q ^ 4)]
    have h1 := abs_add_le ((∑ v ∈ Eset, FT v S) + (∑ v ∈ Oset, FT v S)) (∑ v ∈ Rset, FT v S)
    have h2 := abs_add_le (∑ v ∈ Eset, FT v S) (∑ v ∈ Oset, FT v S)
    have hE : |∑ v ∈ Eset, FT v S| ≤ ∑ v ∈ Eset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Eset, FT v S| ≤ ∑ v ∈ Eset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Eset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hO : |∑ v ∈ Oset, FT v S| ≤ ∑ v ∈ Oset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Oset, FT v S| ≤ ∑ v ∈ Oset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Oset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hR : |∑ v ∈ Rset, FT v S| ≤ ∑ v ∈ Rset, (q - 1) ^ inKer v S := by
      calc |∑ v ∈ Rset, FT v S| ≤ ∑ v ∈ Rset, |FT v S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ Rset, (q - 1) ^ inKer v S := Finset.sum_congr rfl (fun v _ => hFT_abs v S)
    have hq4pos : (0 : ℝ) ≤ 1 / q ^ 4 := by positivity
    nlinarith
  have hSrest_sum :
      (∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S|) ≤
        2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
          6 * (q + 6) ^ (3 * t) / q ^ 3) +
        (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
    calc ∑ S ∈ Srest, |((validCols (6 * t) m S).card : ℝ) - modelM S|
        ≤ ∑ S ∈ Srest, ((1 / q ^ 4) * (∑ v ∈ Eset, (q - 1) ^ inKer v S) +
            (1 / q ^ 4) * (∑ v ∈ Oset, (q - 1) ^ inKer v S) +
            (1 / q ^ 4) * (∑ v ∈ Rset, (q - 1) ^ inKer v S)) :=
          Finset.sum_le_sum hrest_per
      _ = (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) +
          (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) +
          (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1; congr 1
          · congr 1; exact Finset.sum_comm
          · congr 1; exact Finset.sum_comm
          · congr 1; exact Finset.sum_comm
      _ ≤ (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
            6 * (q + 6) ^ (3 * t) / q ^ 3) +
          (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
            6 * (q + 6) ^ (3 * t) / q ^ 3) +
          (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
          have hsub0 : Srest ⊆ SnonU.erase (laneSet 0) := Finset.erase_subset _ _
          have hsub1 : Srest ⊆ SnonU.erase (laneSet 1) := by
            intro S hS
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hS).1,
              (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2⟩
          have hsubU : Srest ⊆ SnonU := subset_trans hsub0 (Finset.erase_subset _ _)
          have hE0 := sum_bucket_E_or_O_nonlane t m ht hm 0
          have hO1 := sum_bucket_E_or_O_nonlane t m ht hm 1
          have hR0 := sum_bucket_R t m ht hm
          have hq1_nn : (0 : ℝ) ≤ q - 1 := by linarith only [hq2]
          have hE_le : (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Eset, ∑ S ∈ SnonU.erase (laneSet 0), (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsub0 (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          have hO_le : (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Oset, ∑ S ∈ SnonU.erase (laneSet 1), (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          have hR_le : (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ Srest, (q - 1) ^ inKer v S) ≤
              (1 / q ^ 4) * (∑ v ∈ Rset, ∑ S ∈ SnonU, (q - 1) ^ inKer v S) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
              Finset.sum_le_sum_of_subset_of_nonneg hsubU (fun _ _ _ => pow_nonneg hq1_nn _)) (by positivity)
          simp only [↓reduceIte] at hE0
          have h10 : (1 : Fin 2) ≠ 0 := by decide
          simp only [h10, ↓reduceIte] at hO1
          linarith only [hE_le, hO_le, hR_le, hE0, hO1, hR0]
      _ = _ := by ring
  have h0 := hlane_err 0
  have h1 := hlane_err 1
  linarith


lemma pow_one_add_le_two {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hkx : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k ≤ 2 := by
  cases k with
  | zero => norm_num
  | succ k =>
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hx1 : x ≤ 1 / 2 := by nlinarith
    have hsub_pos : (0 : ℝ) < 1 - x := by linarith
    have hinv : 1 + x ≤ 1 / (1 - x) := by
      rw [le_div_iff₀ hsub_pos]
      nlinarith [sq_nonneg x]
    have hpow1 : (1 + x) ^ (k + 1) ≤ 1 / (1 - x) ^ (k + 1) := by
      calc (1 + x) ^ (k + 1) ≤ (1 / (1 - x)) ^ (k + 1) :=
            pow_le_pow_left₀ (by linarith) hinv (k + 1)
        _ = 1 / (1 - x) ^ (k + 1) := by rw [div_pow, one_pow]
    have hbern : 1 - ((k + 1 : ℕ) : ℝ) * x ≤ (1 - x) ^ (k + 1) := by
      have h := one_add_mul_le_pow (a := -x) (by linarith) (k + 1)
      have h1 : 1 + -x = 1 - x := by ring
      rw [h1] at h
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ (1 - x) ^ (k + 1) := by linarith
    have hpow2 : 1 / (1 - x) ^ (k + 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact le_trans hpow1 hpow2

lemma sqrt_ratio_le_five_sixths {s : ℝ} (hs : 64 ≤ s) :
    (1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1)) ≤ 5 / 6 := by
  have hden : 0 < 1 + Real.sqrt (s - 1) := by
    have : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
    linarith
  rw [div_le_iff₀ hden]
  have hr1 : 0 ≤ Real.sqrt (s / 2 - 1) := Real.sqrt_nonneg _
  have hr2 : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt (s / 2 - 1) ^ 2 = s / 2 - 1 := Real.sq_sqrt (by linarith)
  have hsq2 : Real.sqrt (s - 1) ^ 2 = s - 1 := Real.sq_sqrt (by linarith)
  have hr1_le : Real.sqrt (s / 2 - 1) ≤ s / 4 := by
    nlinarith [sq_nonneg (s / 4 - Real.sqrt (s / 2 - 1)), hsq1]
  have hgoal_sq : (1 + 6 * Real.sqrt (s / 2 - 1)) ^ 2 ≤ (5 * Real.sqrt (s - 1)) ^ 2 := by
    nlinarith [hsq1, hsq2, hr1_le]
  have hgoal : 1 + 6 * Real.sqrt (s / 2 - 1) ≤ 5 * Real.sqrt (s - 1) := by
    nlinarith [hr1, hr2, hgoal_sq]
  linarith

lemma main_partA_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t) :
    let s : ℝ := (2 : ℝ) ^ d
    let model : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then s ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then s ^ (3 * t - 2) else 0) +
      (s - 1) ^ (runsCard S) / s ^ 4
    let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
    (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
      2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) := by
  intro s model SnonU
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  have hfd_d : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
      2 * (s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) + s ^ t) +
      2 * (((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 +
        6 * (s + 6) ^ (3 * t) / s ^ 3) +
      (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) :=
    validCols_fourier_diff_sum t d (by omega) (by omega)
  have hpow_1add4 : (s + 4) ^ (3 * t) ≤ 2 * s ^ (3 * t) := by
    have h1 : (1 + 4 / s) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (4 / s) = 2 * (6 * (t : ℝ)) / s := by push_cast; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (s + 4) ^ (3 * t) = s ^ (3 * t) * (1 + 4 / s) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hspos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hspos) (3 * t)]
  have hpow_1add6 : (s + 6) ^ (3 * t) ≤ 2 * s ^ (3 * t) := by
    have h1 : (1 + 6 / s) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (6 / s) = 3 * (6 * (t : ℝ)) / s := by push_cast; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (s + 6) ^ (3 * t) = s ^ (3 * t) * (1 + 6 / s) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hspos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hspos) (3 * t)]
  have hdiff_s4 : (s + 4) ^ (3 * t) - (s - 1) ^ (3 * t) ≤ (15 * (t : ℝ)) * (s + 4) ^ (3 * t - 1) := by
    have hgen : ∀ k : ℕ, 1 ≤ k → (s + 4) ^ k - (s - 1) ^ k ≤ 5 * (k : ℝ) * (s + 4) ^ (k - 1) := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        cases k with
        | zero => simp; linarith only [hspos]
        | succ k =>
          have hih := ih (by omega)
          have h1 : (s + 4) ^ (k + 2) - (s - 1) ^ (k + 2) =
              (s + 4) * ((s + 4) ^ (k + 1) - (s - 1) ^ (k + 1)) + 5 * (s - 1) ^ (k + 1) := by ring
          have h2 : (s - 1) ^ (k + 1) ≤ (s + 4) ^ (k + 1) :=
            pow_le_pow_left₀ (by linarith only [hs64]) (by linarith only [hs64]) (k + 1)
          have h3 : (s + 4) * (5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ k) =
              5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ (k + 1) := by rw [pow_succ']; ring
          have h4 : 5 * ((k + 1 : ℕ) : ℝ) * (s + 4) ^ (k + 1) + 5 * (s + 4) ^ (k + 1) =
              5 * ((k + 2 : ℕ) : ℝ) * (s + 4) ^ (k + 1) := by push_cast; ring
          simp only [Nat.add_sub_cancel] at hih ⊢
          have hs4_nn : (0 : ℝ) ≤ s + 4 := by linarith only [hs64]
          have hm := mul_le_mul_of_nonneg_left hih hs4_nn
          linarith only [h1, h2, h3, h4, hm]
    have h := hgen (3 * t) (by omega)
    have hcast : 5 * ((3 * t : ℕ) : ℝ) = 15 * (t : ℝ) := by push_cast; ring
    rw [hcast] at h
    exact h
  have hpow_1add4_m1 : (s + 4) ^ (3 * t - 1) ≤ 2 * s ^ (3 * t - 1) := by
    have h1 : (s + 4) ^ (3 * t - 1) * (s + 4) = (s + 4) ^ (3 * t) := by
      rw [← pow_succ]; congr 1; omega
    have h2 : s ^ (3 * t - 1) * s = s ^ (3 * t) := by
      rw [← pow_succ]; congr 1; omega
    have hnn : 0 ≤ (s + 4) ^ (3 * t - 1) := by positivity
    nlinarith only [hpow_1add4, h1, h2, hnn, hspos]
  have hpow_eq_s2 : s ^ (3 * t - 2) * s ^ 2 = s ^ (3 * t) := by
    rw [← pow_add]; congr 1; omega
  have hpow_eq_s1 : s ^ (3 * t - 2) * s = s ^ (3 * t - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hterm5 : (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) ≤
      2 * s ^ (3 * t - 2) * ((1 : ℝ) / 2) ^ t := by
    have hexp : 6 * t + d * (3 * t - t / 3) + t ≤ d * (3 * t - 2) := by
      have h1 : d * (3 * t - 2) - d * (3 * t - t / 3) = d * (t / 3 - 2) := by
        rw [← Nat.mul_sub]; congr 1; omega
      have h2 : d * (t / 3 - 2) ≥ 40 * (t / 3 - 2) := Nat.mul_le_mul_right _ hd
      have h3 : 7 * t ≤ 40 * (t / 3 - 2) := by omega
      omega
    have hpow_nat : (2 : ℝ) ^ (6 * t) * ((2 : ℝ) ^ d) ^ (3 * t - t / 3) * (2 : ℝ) ^ t ≤
        ((2 : ℝ) ^ d) ^ (3 * t - 2) := by
      simp only [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h12 : ((1 : ℝ) / 2) ^ t = ((2 : ℝ) ^ t)⁻¹ := by rw [one_div, inv_pow]
    rw [h12]
    have h2tpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have hmul := mul_le_mul_of_nonneg_right hpow_nat (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹)
    have hL : (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) * (2 : ℝ) ^ t * ((2 : ℝ) ^ t)⁻¹ =
        (2 : ℝ) ^ (6 * t) * s ^ (3 * t - t / 3) := by
      dsimp only [s]; field_simp [ne_of_gt h2tpos]
    rw [hL] at hmul
    have hR : s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ ≤ 2 * s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by
      have hnn : 0 ≤ s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by positivity
      linarith only [hnn]
    exact le_trans hmul hR
  have hterm1 : s ^ t ≤ s ^ (3 * t - 2) * (1 / s) := by
    have h1 : s ^ (3 * t - 2) * (1 / s) = s ^ (3 * t - 3) := by
      have hsub : s ^ (3 * t - 3) * s = s ^ (3 * t - 2) := by rw [← pow_succ]; congr 1; omega
      field_simp [ne_of_gt hspos]; linarith only [hsub]
    rw [h1]
    exact pow_le_pow_right₀ (by linarith only [hs64]) (by omega)
  have hterm2 : 1 / s ^ 2 ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hspos]
    nlinarith only [hs64]
  have hterm3 : ((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 ≤
      s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) := by
    have h1 : (s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t) ≤
        (15 * (t : ℝ) + 4) * (2 * s ^ (3 * t - 1)) := by
      have hnn : (0 : ℝ) ≤ 15 * (t : ℝ) + 4 := by positivity
      nlinarith only [hdiff_s4, hpow_1add4_m1, hnn]
    have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ s ^ 2)
    have hR : ((15 * (t : ℝ) + 4) * (2 * s ^ (3 * t - 1))) / s ^ 2 =
        s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) := by
      rw [← hpow_eq_s1]; field_simp [ne_of_gt hspos]; ring
    linarith only [h2, hR]
  have hterm4 : 6 * (s + 6) ^ (3 * t) / s ^ 3 ≤ s ^ (3 * t - 2) * (12 / s) := by
    have h1 : 6 * (s + 6) ^ (3 * t) ≤ 12 * s ^ (3 * t) := by linarith only [hpow_1add6]
    have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ s ^ 3)
    have hR : (12 * s ^ (3 * t)) / s ^ 3 = s ^ (3 * t - 2) * (12 / s) := by
      rw [← hpow_eq_s2]; field_simp [ne_of_gt hspos]
    linarith only [h2, hR]
  have h3t : (3 * (t : ℝ)) / s = (1 / 2) * ((6 * (t : ℝ)) / s) := by ring
  have hs_nn : 0 ≤ s ^ (3 * t - 2) := by positivity
  have hterm0 : s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) ≤
      s ^ (3 * t - 2) * ((1 / 2) * ((6 * (t : ℝ)) / s) + 1 / s) :=
    mul_le_mul_of_nonneg_left (by linarith only [h3t, hterm2]) hs_nn
  have hA_nn : 0 ≤ s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s) := by positivity
  have hB_nn : 0 ≤ s ^ (3 * t - 2) * (1 / s) := by positivity
  have hterm3' : ((s + 4) ^ (3 * t) + 4 * (s + 4) ^ (3 * t - 1) - (s - 1) ^ (3 * t)) / s ^ 2 ≤
      5 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 8 * (s ^ (3 * t - 2) * (1 / s)) := by
    have hr : s ^ (3 * t - 2) * (5 * ((6 * (t : ℝ)) / s) + 8 / s) =
        5 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 8 * (s ^ (3 * t - 2) * (1 / s)) := by ring
    linarith only [hterm3, hr]
  have hterm4' : 6 * (s + 6) ^ (3 * t) / s ^ 3 ≤ 12 * (s ^ (3 * t - 2) * (1 / s)) := by
    have hr : s ^ (3 * t - 2) * (12 / s) = 12 * (s ^ (3 * t - 2) * (1 / s)) := by ring
    linarith only [hterm4, hr]
  have hterm0' : s ^ (3 * t - 2) * ((3 * (t : ℝ)) / s + 1 / s ^ 2) ≤
      (1 / 2) * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + s ^ (3 * t - 2) * (1 / s) := by
    have hr : s ^ (3 * t - 2) * ((1 / 2) * ((6 * (t : ℝ)) / s) + 1 / s) =
        (1 / 2) * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + s ^ (3 * t - 2) * (1 / s) := by ring
    linarith only [hterm0, hr]
  have hrhs : 2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) =
      40 * (s ^ (3 * t - 2) * ((6 * (t : ℝ)) / s)) + 50 * (s ^ (3 * t - 2) * (1 / s)) +
      2 * s ^ (3 * t - 2) * ((1 : ℝ) / 2) ^ t := by ring
  linarith only [hfd_d, hterm0', hterm1, hterm3', hterm4', hterm5, hA_nn, hB_nn, hrhs]

lemma main_partB_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    (Z : ℝ) (hZ_pos : 0 < Z)
    (hZ_ge1 : 2 * ((2 : ℝ) ^ d) ^ (3 * t - 2) ≤ Z)
    (hZ_ge2 : (1 + Real.sqrt ((2 : ℝ) ^ d - 1)) ^ (6 * t) / ((2 : ℝ) ^ d) ^ 4 ≤ Z) :
    let s : ℝ := (2 : ℝ) ^ d
    let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
    s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / Z ≤
      250 * ((1 : ℝ) / 2) ^ t := by
  intro s SnonU
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  let q : ℝ := (2 : ℝ) ^ (d - 1)
  have hq_val : q = s / 2 := by
    have hd1 : d = (d - 1) + 1 := by omega
    dsimp only [s, q]
    conv_rhs => rw [hd1, pow_succ]
    ring
  have hq32 : (32 : ℝ) ≤ q := by linarith only [hs64, hq_val]
  have hqpos : (0 : ℝ) < q := by linarith only [hq32]
  let modelQ : Finset (Fin (6 * t)) → ℝ := fun S =>
    (if S = laneSet 0 then q ^ (3 * t - 2) else 0) +
    (if S = laneSet 1 then q ^ (3 * t - 2) else 0) +
    (q - 1) ^ (runsCard S) / q ^ 4
  have hfd_q : (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) ≤
      2 * (q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) + q ^ t) +
      2 * (((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 +
        6 * (q + 6) ^ (3 * t) / q ^ 3) +
      (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) :=
    validCols_fourier_diff_sum t (d - 1) (by omega) (by omega)
  have hsum_val_le : (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
      (∑ S ∈ SnonU, modelQ S) + (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hle := le_abs_self (((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S)
    linarith only [hle]
  have hsum_modelQ : (∑ S ∈ SnonU, modelQ S) ≤
      2 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 := by
    have hnn : ∀ S, 0 ≤ modelQ S := fun S => by
      dsimp only [modelQ]
      have h1 : (0 : ℝ) ≤ if S = laneSet 0 then q ^ (3 * t - 2) else 0 := by split_ifs <;> positivity
      have h2 : (0 : ℝ) ≤ if S = laneSet 1 then q ^ (3 * t - 2) else 0 := by split_ifs <;> positivity
      have h3 : (0 : ℝ) ≤ (q - 1) ^ (runsCard S) / q ^ 4 :=
        div_nonneg (pow_nonneg (by linarith only [hq32]) _) (by positivity)
      linarith only [h1, h2, h3]
    calc ∑ S ∈ SnonU, modelQ S
        ≤ ∑ S : Finset (Fin (6 * t)), modelQ S := Finset.sum_le_univ_sum_of_nonneg hnn
      _ = 2 * q ^ (3 * t - 2) + (matA q ^ (6 * t)).trace / q ^ 4 := by
          dsimp only [modelQ]
          simp only [Finset.sum_add_distrib, ← Finset.sum_div]
          have h0 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 0 then q ^ (3 * t - 2) else 0) =
              q ^ (3 * t - 2) := by simp
          have h1 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 1 then q ^ (3 * t - 2) else 0) =
              q ^ (3 * t - 2) := by simp
          have h2 := sum_runs_eq_trace_A (6 * t) (by omega) q
          rw [h0, h1, h2]; ring
      _ ≤ 2 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 := by
          have htr := trace_matA_pow_le_even q (by linarith only [hq32]) (3 * t)
          have h6 : 2 * (3 * t) = 6 * t := by ring
          rw [h6] at htr
          have hdiv := div_le_div_of_nonneg_right htr (by positivity : (0 : ℝ) ≤ q ^ 4)
          linarith only [hdiv]
  have hq_1add4 : (q + 4) ^ (3 * t) ≤ 2 * q ^ (3 * t) := by
    have h1 : (1 + 4 / q) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (4 / q) = 4 * (6 * (t : ℝ)) / s := by
          rw [hq_val]; push_cast; field_simp [ne_of_gt hspos]; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (q + 4) ^ (3 * t) = q ^ (3 * t) * (1 + 4 / q) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hqpos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hqpos) (3 * t)]
  have hq_1add6 : (q + 6) ^ (3 * t) ≤ 2 * q ^ (3 * t) := by
    have h1 : (1 + 6 / q) ^ (3 * t) ≤ 2 :=
      pow_one_add_le_two (by positivity) (by
        have h : ((3 * t : ℕ) : ℝ) * (6 / q) = 6 * (6 * (t : ℝ)) / s := by
          rw [hq_val]; push_cast; field_simp [ne_of_gt hspos]; ring
        rw [h, div_le_iff₀ hspos]; linarith only [hds])
    have h2 : (q + 6) ^ (3 * t) = q ^ (3 * t) * (1 + 6 / q) ^ (3 * t) := by
      rw [← mul_pow]; congr 1; field_simp [ne_of_gt hqpos]
    rw [h2]; nlinarith only [h1, pow_nonneg (le_of_lt hqpos) (3 * t)]
  have hq_eq2 : q ^ (3 * t - 2) * q ^ 2 = q ^ (3 * t) := by
    rw [← pow_add]; congr 1; omega
  have hdiff_q_crude : (∑ S ∈ SnonU, |((validCols (6 * t) (d - 1) S).card : ℝ) - modelQ S|) ≤
      40 * q ^ (3 * t - 2) + (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
    have h1 : (3 * (t : ℝ)) / q + 1 / q ^ 2 ≤ 1 := by
      have ha : (3 * (t : ℝ)) / q = 6 * (t : ℝ) / s := by
        rw [hq_val]; field_simp [ne_of_gt hspos]; ring
      have hb : 6 * (t : ℝ) / s ≤ 1 / 100 := by rw [div_le_iff₀ hspos]; linarith only [hds]
      have hc : 1 / q ^ 2 ≤ 1 / 100 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hq32]
      linarith only [ha, hb, hc]
    have h2 : q ^ t ≤ q ^ (3 * t - 2) := pow_le_pow_right₀ (by linarith only [hq32]) (by omega)
    have h3 : ((q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t)) / q ^ 2 ≤
        10 * q ^ (3 * t - 2) := by
      have ha : (q + 4) ^ (3 * t - 1) ≤ (q + 4) ^ (3 * t) :=
        pow_le_pow_right₀ (by linarith only [hq32]) (by omega)
      have hb : (0 : ℝ) ≤ (q - 1) ^ (3 * t) := pow_nonneg (by linarith only [hq32]) _
      have hc : (q + 4) ^ (3 * t) + 4 * (q + 4) ^ (3 * t - 1) - (q - 1) ^ (3 * t) ≤ 10 * q ^ (3 * t) := by
        linarith only [hq_1add4, ha, hb]
      have hd' := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ q ^ 2)
      have hR : 10 * q ^ (3 * t) / q ^ 2 = 10 * q ^ (3 * t - 2) := by
        rw [← hq_eq2]; field_simp [ne_of_gt hqpos]
      linarith only [hd', hR]
    have h4 : 6 * (q + 6) ^ (3 * t) / q ^ 3 ≤ 1 * q ^ (3 * t - 2) := by
      have hc : 6 * (q + 6) ^ (3 * t) ≤ 12 * q ^ (3 * t) := by linarith only [hq_1add6]
      have hd' := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ q ^ 3)
      have hR : 12 * q ^ (3 * t) / q ^ 3 = (12 / q) * q ^ (3 * t - 2) := by
        rw [← hq_eq2]; field_simp [ne_of_gt hqpos]
      have h12 : 12 / q ≤ 1 := by rw [div_le_iff₀ hqpos]; linarith only [hq32]
      have hqnn := pow_nonneg (le_of_lt hqpos) (3 * t - 2)
      nlinarith only [hd', hR, h12, hqnn]
    have hqnn := pow_nonneg (le_of_lt hqpos) (3 * t - 2)
    have h1m : q ^ (3 * t - 2) * ((3 * (t : ℝ)) / q + 1 / q ^ 2) ≤ q ^ (3 * t - 2) := by
      nlinarith only [h1, hqnn]
    linarith only [hfd_q, h1m, h2, h3, h4, hqnn]
  have hPiece1 : s * (42 * q ^ (3 * t - 2)) / Z ≤ 100 * ((1 : ℝ) / 2) ^ t := by
    have hpow_q : q ^ (3 * t - 2) = s ^ (3 * t - 2) / (2 : ℝ) ^ (3 * t - 2) := by
      rw [hq_val, div_pow]
    have hratio : s * (42 * q ^ (3 * t - 2)) / (2 * s ^ (3 * t - 2)) =
        21 * s / (2 : ℝ) ^ (3 * t - 2) := by
      rw [hpow_q]; field_simp [ne_of_gt hspos]; ring
    have hpow2 : 21 * s / (2 : ℝ) ^ (3 * t - 2) ≤ 100 * ((1 : ℝ) / 2) ^ t := by
      have h21 : 21 * (2 : ℝ) ^ d * (2 : ℝ) ^ t ≤ 100 * (2 : ℝ) ^ (3 * t - 2) := by
        have hexp : d + t ≤ 3 * t - 2 := by omega
        have hp : (2 : ℝ) ^ d * (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (3 * t - 2) := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hexp
        have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (3 * t - 2) := by positivity
        linarith only [hp, hnn]
      have h12 : ((1 : ℝ) / 2) ^ t = 1 / (2 : ℝ) ^ t := by rw [div_pow, one_pow]
      rw [h12, div_le_iff₀ (by positivity)]
      dsimp only [s]
      have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
      have hR : 100 * (1 / (2 : ℝ) ^ t) * (2 : ℝ) ^ (3 * t - 2) =
          (100 * (2 : ℝ) ^ (3 * t - 2)) / (2 : ℝ) ^ t := by ring
      rw [hR, le_div_iff₀ h2t]
      linarith only [h21]
    calc s * (42 * q ^ (3 * t - 2)) / Z
        ≤ s * (42 * q ^ (3 * t - 2)) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ = 21 * s / (2 : ℝ) ^ (3 * t - 2) := hratio
      _ ≤ 100 * ((1 : ℝ) / 2) ^ t := hpow2
  have hPiece2 : s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) / Z ≤
      100 * ((1 : ℝ) / 2) ^ t := by
    have hsr := sqrt_ratio_le_five_sixths hs64
    have hpow6 : ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) ≤
        ((3 : ℝ) / 8) ^ t := by
      have h1 : ((5 : ℝ) / 6) ^ 6 ≤ (3 : ℝ) / 8 := by norm_num
      have h2 : ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) ≤
          ((5 : ℝ) / 6) ^ (6 * t) :=
        pow_le_pow_left₀ (by positivity) hsr (6 * t)
      have h3 : ((5 : ℝ) / 6) ^ (6 * t) ≤ ((3 : ℝ) / 8) ^ t := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (by positivity) h1 t
      exact le_trans h2 h3
    have hden_pos : 0 < (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 := by positivity
    have hsimp : s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) /
        ((1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4) =
        32 * s * ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) := by
      rw [hq_val, div_pow, div_pow]
      have hden1 : (1 + Real.sqrt (s - 1)) ^ (6 * t) ≠ 0 := by positivity
      field_simp [ne_of_gt hspos, hden1]
      ring
    have h32 : 32 * s * ((3 : ℝ) / 8) ^ t ≤ 100 * ((1 : ℝ) / 2) ^ t := by
      have h34 : ((3 : ℝ) / 4) ^ t ≤ ((1 : ℝ) / 2) ^ d := by
        have hstep1 : ((3 : ℝ) / 4) ^ t ≤ ((3 : ℝ) / 4) ^ (3 * d) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hstep2 : ((3 : ℝ) / 4) ^ (3 * d) ≤ ((1 : ℝ) / 2) ^ d := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (by positivity) (by norm_num : ((3 : ℝ) / 4) ^ 3 ≤ 1 / 2) d
        exact le_trans hstep1 hstep2
      have hp : s * ((3 : ℝ) / 4) ^ t ≤ 1 := by
        have hm := mul_le_mul_of_nonneg_left h34 (le_of_lt hspos)
        have h1 : s * ((1 : ℝ) / 2) ^ d = 1 := by
          dsimp only [s]; rw [← mul_pow]; norm_num
        linarith only [hm, h1]
      have hsplit : ((3 : ℝ) / 8) ^ t = ((3 : ℝ) / 4) ^ t * ((1 : ℝ) / 2) ^ t := by
        rw [← mul_pow]; norm_num
      rw [hsplit]
      have hnn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) t
      nlinarith only [hp, hnn]
    calc s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) / Z
        ≤ s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) /
          ((1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hZ_ge2
      _ = 32 * s * ((1 + Real.sqrt (s / 2 - 1)) / (1 + Real.sqrt (s - 1))) ^ (6 * t) := hsimp
      _ ≤ 32 * s * ((3 : ℝ) / 8) ^ t := by gcongr
      _ ≤ 100 * ((1 : ℝ) / 2) ^ t := h32
  have hPiece3 : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / Z ≤ 50 * ((1 : ℝ) / 2) ^ t := by
    have hexp : d + 6 * t + (d - 1) * (3 * t - t / 3) + t ≤ d * (3 * t - 2) := by
      have h1 : (d - 1) * (3 * t - t / 3) ≤ d * (3 * t - t / 3) :=
        Nat.mul_le_mul_right _ (Nat.sub_le d 1)
      have h2 : d * (3 * t - 2) - d * (3 * t - t / 3) = d * (t / 3 - 2) := by
        rw [← Nat.mul_sub]; congr 1; omega
      have h3 : d * (t / 3 - 2) ≥ 40 * (t / 3 - 2) := Nat.mul_le_mul_right _ hd
      have h4 : d + 7 * t ≤ 40 * (t / 3 - 2) := by omega
      omega
    have hpow_nat : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) * (2 : ℝ) ^ t ≤
        s ^ (3 * t - 2) := by
      dsimp only [s, q]
      simp only [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / Z
        ≤ s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ ≤ ((1 : ℝ) / 2) ^ t := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s ^ (3 * t - 2))]
          have h12 : ((1 : ℝ) / 2) ^ t = ((2 : ℝ) ^ t)⁻¹ := by rw [one_div, inv_pow]
          rw [h12]
          have h2tpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
          have hmul := mul_le_mul_of_nonneg_right hpow_nat (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹)
          have hL : s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) * (2 : ℝ) ^ t * ((2 : ℝ) ^ t)⁻¹ =
              s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) := by field_simp [ne_of_gt h2tpos]
          rw [hL] at hmul
          have hR : s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ ≤ ((2 : ℝ) ^ t)⁻¹ * (2 * s ^ (3 * t - 2)) := by
            have hnn : 0 ≤ s ^ (3 * t - 2) * ((2 : ℝ) ^ t)⁻¹ := by positivity
            linarith only [hnn]
          exact le_trans hmul hR
      _ ≤ 50 * ((1 : ℝ) / 2) ^ t := by
          have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ t := by positivity
          linarith only [hnn]
  have htotB : s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
      s * (42 * q ^ (3 * t - 2)) +
      s * (2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4) +
      s * ((2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3)) := by
    have hsum_le : (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) ≤
        42 * q ^ (3 * t - 2) + 2 * (1 + Real.sqrt (q - 1)) ^ (6 * t) / q ^ 4 +
        (2 : ℝ) ^ (6 * t) * q ^ (3 * t - t / 3) := by
      linarith only [hsum_val_le, hsum_modelQ, hdiff_q_crude]
    have hmul := mul_le_mul_of_nonneg_left hsum_le (le_of_lt hspos)
    linarith only [hmul]
  have hdivB := div_le_div_of_nonneg_right htotB (le_of_lt hZ_pos)
  rw [add_div, add_div] at hdivB
  linarith only [hdivB, hPiece1, hPiece2, hPiece3]

lemma main_ratio_bound_core (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    (actual : Finset (Fin (6 * t)) → ℝ)
    (hact_eq : ∀ S : Finset (Fin (6 * t)), actual S = ((fullCols (6 * t) d S).card : ℝ)) :
    let s : ℝ := (2 : ℝ) ^ d
    let model : Finset (Fin (6 * t)) → ℝ := fun S =>
      (if S = laneSet 0 then s ^ (3 * t - 2) else 0) +
      (if S = laneSet 1 then s ^ (3 * t - 2) else 0) +
      (s - 1) ^ (runsCard S) / s ^ 4
    (∑ S : Finset (Fin (6 * t)), |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S) ≤
      60 * ((6 * (t : ℝ)) / s) + 40 / s + 300 * ((1 : ℝ) / 2) ^ t := by
  intro s model
  have hs64 : (64 : ℝ) ≤ s := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hspos : (0 : ℝ) < s := by linarith only [hs64]
  have hZ_eq : (∑ S : Finset (Fin (6 * t)), model S) =
      2 * s ^ (3 * t - 2) + (matA s ^ (6 * t)).trace / s ^ 4 := by
    dsimp only [model]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    have h0 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 0 then s ^ (3 * t - 2) else 0) =
        s ^ (3 * t - 2) := by simp
    have h1 : (∑ S : Finset (Fin (6 * t)), if S = laneSet 1 then s ^ (3 * t - 2) else 0) =
        s ^ (3 * t - 2) := by simp
    have h2 : (∑ S : Finset (Fin (6 * t)), (s - 1) ^ (runsCard S)) = (matA s ^ (6 * t)).trace :=
      sum_runs_eq_trace_A (6 * t) (by omega) s
    rw [h0, h1, h2]
    ring
  have hZ_ge1 : 2 * s ^ (3 * t - 2) ≤ ∑ S : Finset (Fin (6 * t)), model S := by
    rw [hZ_eq]
    have htr : 0 ≤ (matA s ^ (6 * t)).trace := by
      have h := trace_matA_pow_ge_even s (by linarith only [hs64]) (3 * t)
      have h6 : 2 * (3 * t) = 6 * t := by ring
      rw [h6] at h
      have hnn : 0 ≤ (1 + Real.sqrt (s - 1)) ^ (6 * t) := by positivity
      linarith only [h, hnn]
    have hdiv : 0 ≤ (matA s ^ (6 * t)).trace / s ^ 4 := div_nonneg htr (by positivity)
    linarith only [hdiv]
  have hZ_ge2 : (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 ≤ ∑ S : Finset (Fin (6 * t)), model S := by
    rw [hZ_eq]
    have htr := trace_matA_pow_ge_even s (by linarith only [hs64]) (3 * t)
    have h6 : 2 * (3 * t) = 6 * t := by ring
    rw [h6] at htr
    have hnn : 0 ≤ 2 * s ^ (3 * t - 2) := by positivity
    have hdiv : (1 + Real.sqrt (s - 1)) ^ (6 * t) / s ^ 4 ≤ (matA s ^ (6 * t)).trace / s ^ 4 :=
      div_le_div_of_nonneg_right htr (by positivity)
    linarith only [hnn, hdiv]
  have hZ_pos : 0 < ∑ S : Finset (Fin (6 * t)), model S := by
    have hpos : 0 < 2 * s ^ (3 * t - 2) := by positivity
    linarith only [hpos, hZ_ge1]
  let SnonU := Finset.univ.erase (Finset.univ : Finset (Fin (6 * t)))
  have hnum_split : (∑ S : Finset (Fin (6 * t)), |actual S - model S|) =
      |actual Finset.univ - model Finset.univ| + ∑ S ∈ SnonU, |actual S - model S| :=
    (Finset.add_sum_erase Finset.univ (fun S => |actual S - model S|) (Finset.mem_univ _)).symm
  have huniv_err : |actual Finset.univ - model Finset.univ| = 1 / s ^ 4 := by
    rw [hact_eq, fullCols_univ (6 * t) d (by omega) (by omega)]
    have hne0 : (Finset.univ : Finset (Fin (6 * t))) ≠ laneSet 0 := by
      intro heq
      have hmem : (⟨1, by omega⟩ : Fin (6 * t)) ∈ laneSet 0 := by rw [← heq]; exact Finset.mem_univ _
      simp [laneSet] at hmem
    have hne1 : (Finset.univ : Finset (Fin (6 * t))) ≠ laneSet 1 := by
      intro heq
      have hmem : (⟨0, by omega⟩ : Fin (6 * t)) ∈ laneSet 1 := by rw [← heq]; exact Finset.mem_univ _
      simp [laneSet] at hmem
    have hrunsU : runsCard (Finset.univ : Finset (Fin (6 * t))) = 0 := by simp [runsCard, endsSet]
    simp only [Nat.cast_zero, zero_sub, abs_neg, model, hne0, hne1, ↓reduceIte, add_zero, zero_add,
      hrunsU, pow_zero]
    exact abs_of_nonneg (by positivity)
  have hnonU_tri : (∑ S ∈ SnonU, |actual S - model S|) ≤
      (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
      s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) := by
    have hper : ∀ S ∈ SnonU,
        |actual S - model S| ≤ |((validCols (6 * t) d S).card : ℝ) - model S| +
          s * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
      intro S _
      rw [hact_eq S]
      have hsub : fullCols (6 * t) d S ⊆ validCols (6 * t) d S := Finset.filter_subset _ _
      have hle_c : (fullCols (6 * t) d S).card ≤ (validCols (6 * t) d S).card :=
        Finset.card_le_card hsub
      have hdiff_nat := fullCols_diff_le (6 * t) d (by omega) S
      have hdiff_r : ((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ) ≤
          s * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
        have h1 : (((validCols (6 * t) d S).card - (fullCols (6 * t) d S).card : ℕ) : ℝ) ≤
            ((2 ^ d - 1 : ℕ) : ℝ) * ((validCols (6 * t) (d - 1) S).card : ℝ) := by
          exact_mod_cast hdiff_nat
        rw [Nat.cast_sub hle_c] at h1
        have h2 : ((2 ^ d - 1 : ℕ) : ℝ) ≤ s := by
          have : 2 ^ d - 1 ≤ 2 ^ d := Nat.sub_le _ _
          dsimp only [s]
          exact_mod_cast this
        have hnn : (0 : ℝ) ≤ ((validCols (6 * t) (d - 1) S).card : ℝ) := Nat.cast_nonneg _
        nlinarith only [h1, h2, hnn]
      have hnn_diff : 0 ≤ ((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ) := by
        have hle : ((fullCols (6 * t) d S).card : ℝ) ≤ ((validCols (6 * t) d S).card : ℝ) :=
          Nat.cast_le.mpr hle_c
        linarith only [hle]
      have htri := abs_add_le (((validCols (6 * t) d S).card : ℝ) - model S)
        (-(((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ)))
      have hrew : ((fullCols (6 * t) d S).card : ℝ) - model S =
          (((validCols (6 * t) d S).card : ℝ) - model S) +
          (-(((validCols (6 * t) d S).card : ℝ) - ((fullCols (6 * t) d S).card : ℝ))) := by ring
      rw [hrew]
      rw [abs_neg, abs_of_nonneg hnn_diff] at htri
      linarith only [htri, hdiff_r]
    calc ∑ S ∈ SnonU, |actual S - model S|
        ≤ ∑ S ∈ SnonU, (|((validCols (6 * t) d S).card : ℝ) - model S| +
            s * ((validCols (6 * t) (d - 1) S).card : ℝ)) := Finset.sum_le_sum hper
      _ = (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hPartA : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) /
      (∑ S : Finset (Fin (6 * t)), model S) ≤
      20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t := by
    have hnum_le : (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) ≤
        2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t) :=
      main_partA_bound t d ht hd hds hdt
    calc (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) /
          (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t)) /
          (∑ S : Finset (Fin (6 * t)), model S) := div_le_div_of_nonneg_right hnum_le (le_of_lt hZ_pos)
      _ ≤ (2 * s ^ (3 * t - 2) * (20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t)) /
          (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ = 20 * ((6 * (t : ℝ)) / s) + 25 / s + ((1 : ℝ) / 2) ^ t := by
          field_simp [ne_of_gt (by positivity : (0 : ℝ) < 2 * s ^ (3 * t - 2))]
  have hPartB : s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) /
      (∑ S : Finset (Fin (6 * t)), model S) ≤ 250 * ((1 : ℝ) / 2) ^ t :=
    main_partB_bound t d ht hd hds hdt (∑ S : Finset (Fin (6 * t)), model S) hZ_pos hZ_ge1 hZ_ge2
  have huniv_ratio : (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) ≤ 1 / s := by
    calc (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (1 / s ^ 4) / (2 * s ^ (3 * t - 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hZ_ge1
      _ ≤ 1 / s := by
          rw [div_div, div_le_div_iff₀ (by positivity) hspos]
          have h1 : 1 ≤ s ^ (3 * t - 2) := one_le_pow₀ (by linarith only [hs64])
          have h2 : s ≤ s ^ 4 := by
            have hs1 : 1 ≤ s := by linarith only [hs64]
            calc s = s ^ 1 := (pow_one s).symm
              _ ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by omega)
          nlinarith only [h1, h2, hspos]
  rw [hnum_split, huniv_err]
  have hcomb : (1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S) ≤
      (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) +
      (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) / (∑ S : Finset (Fin (6 * t)), model S) +
      s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / (∑ S : Finset (Fin (6 * t)), model S) := by
    have hnum_le : 1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S| ≤
        1 / s ^ 4 + ((∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ))) := by
      linarith only [hnonU_tri]
    calc (1 / s ^ 4 + ∑ S ∈ SnonU, |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S)
        ≤ (1 / s ^ 4 + ((∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) +
            s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)))) / (∑ S : Finset (Fin (6 * t)), model S) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hZ_pos)
      _ = (1 / s ^ 4) / (∑ S : Finset (Fin (6 * t)), model S) +
          (∑ S ∈ SnonU, |((validCols (6 * t) d S).card : ℝ) - model S|) / (∑ S : Finset (Fin (6 * t)), model S) +
          s * (∑ S ∈ SnonU, ((validCols (6 * t) (d - 1) S).card : ℝ)) / (∑ S : Finset (Fin (6 * t)), model S) := by ring
  have hgt : 0 ≤ (6 * (t : ℝ)) / s := by positivity
  have hinv_nn : 0 ≤ 1 / s := by positivity
  have hhalf_nn : 0 ≤ ((1 : ℝ) / 2) ^ t := by positivity
  have h25 : (25 : ℝ) / s = 25 * (1 / s) := by ring
  have h40 : (40 : ℝ) / s = 40 * (1 / s) := by ring
  linarith only [hcomb, huniv_ratio, hPartA, hPartB, hgt, hinv_nn, hhalf_nn, h25, h40]

lemma main_ratio_bound (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t)
    [Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))] :
    let F := ZMod 2
    let n := 6 * t
    let a := 3 * t
    let W := Fin n → F
    let next := fun i : Fin n =>
      (⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
    let h := fun (i : Fin n) (b : Fin 4) =>
      if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : F) else 0
    let good := fun U : Submodule F W =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    let supp := fun U : Submodule F W =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let spaces := (Finset.univ : Finset (Submodule F W)).filter good
    let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    let s := (2 : ℝ) ^ d
    let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
    let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
    let model := fun S : Finset (Fin n) =>
      (if S = lane 0 then s ^ (a - 2) else 0) + (if S = lane 1 then s ^ (a - 2) else 0) +
      (s - 1) ^ (runs S) / s ^ 4
    let actual := fun S : Finset (Fin n) => (B : ℝ) *
      ((layer.filter (fun U => supp U = S)).card : ℝ)
    (∑ S : Finset (Fin n), |actual S - model S|) / (∑ S : Finset (Fin n), model S) ≤
      60 * ((6 * (t : ℝ)) / (2 : ℝ) ^ d) + 40 / (2 : ℝ) ^ d + 300 * ((1 : ℝ) / 2) ^ t := by
  intro F n a W next h good supp spaces layer B s lane runs model actual
  exact main_ratio_bound_core t d ht hd hds hdt actual (fun S => by
    have hnat := actual_eq_fullCols_card (6 * t) d S
    dsimp only at hnat
    change (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ) = ((fullCols (6 * t) d S).card : ℝ)
    exact_mod_cast hnat)

lemma main_ratio_bound_exact (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
     let F := ZMod 2
     let n := 6*t
     let a := 3*t
     let W := Fin n → F
     letI : Fintype (Submodule F W) := Fintype.ofFinite _
     let next := fun i : Fin n =>
       (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
     let h := fun (i : Fin n) (b : Fin 4) =>
       if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
       then (1:F) else 0
     let good := fun U : Submodule F W =>
       (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
       (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
     let supp := fun U : Submodule F W =>
       Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
     let spaces := (Finset.univ : Finset (Submodule F W)).filter good
     let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
     let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ)
     let s := (2 : ℝ)^d
     let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
     let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
     let model := fun S : Finset (Fin n) =>
       (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) +
       (s-1)^(runs S)/s^4
     let actual := fun S : Finset (Fin n) => (B : ℝ) *
       ((layer.filter (fun U => supp U = S)).card : ℝ)
     (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) ≤
      60 * ((6 * (t : ℝ)) / (2 : ℝ) ^ d) + 40 / (2 : ℝ) ^ d + 300 * ((1 : ℝ) / 2) ^ t := by
  let instF : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2)) := Fintype.ofFinite _
  have hmain := @main_ratio_bound t d ht hd hds hdt instF
  have hbridge : ∀ (instF' : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))),
      (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
       let F := ZMod 2; let n := 6*t; let a := 3*t; let W := Fin n → F
       letI : Fintype (Submodule F W) := instF'
       let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
       let h := fun (i : Fin n) (b : Fin 4) => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1:F) else 0
       let good := fun U : Submodule F W => (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧ (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
       let supp := fun U : Submodule F W => Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
       let spaces := (Finset.univ : Finset (Submodule F W)).filter good
       let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
       let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ); let s := (2 : ℝ)^d
       let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
       let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
       let model := fun S : Finset (Fin n) => (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) + (s-1)^(runs S)/s^4
       let actual := fun S : Finset (Fin n) => (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ)
       (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) =
      (letI : Fintype (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2)) := instF'
       let F := ZMod 2; let n := 6*t; let a := 3*t; let W := Fin n → F
       let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
       let h := fun (i : Fin n) (b : Fin 4) => if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1:F) else 0
       let good := fun U : Submodule F W => (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧ (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
       let supp := fun U : Submodule F W => Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
       let spaces := (Finset.univ : Finset (Submodule F W)).filter good
       let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
       let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ); let s := (2 : ℝ)^d
       let lane := fun b : Fin 2 => Finset.univ.filter (fun i : Fin n => i.val % 2 = b.val)
       let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
       let model := fun S : Finset (Fin n) => (if S = lane 0 then s^(a-2) else 0) + (if S = lane 1 then s^(a-2) else 0) + (s-1)^(runs S)/s^4
       let actual := fun S : Finset (Fin n) => (B : ℝ) * ((layer.filter (fun U => supp U = S)).card : ℝ)
       (∑ S : Finset (Fin n), |actual S - model S|)/(∑ S : Finset (Fin n), model S)) := by
    intro instF'
    have hfilt2 : ∀ {α : Type} {s₁ s₂ : Finset α} {p q : α → Prop}
        {d₁ : DecidablePred p} {d₂ : DecidablePred q},
        s₁ = s₂ → (∀ x, p x ↔ q x) → @Finset.filter α p d₁ s₁ = @Finset.filter α q d₂ s₂ := by
      intro α s₁ s₂ p q d₁ d₂ hs hpq
      subst hs; ext x; simp only [Finset.mem_filter, hpq]
    have hite : ∀ {α : Type} {p q : Prop} {d₁ : Decidable p} {d₂ : Decidable q} {x y : α},
        (p ↔ q) → @ite α p d₁ x y = @ite α q d₂ x y := by
      intro α p q d₁ d₂ x y hpq
      by_cases hp : p
      · have hq : q := hpq.mp hp; rw [ite_eq_left hp, ite_eq_left hq]
      · have hq : ¬ q := fun h => hp (hpq.mpr h); rw [ite_eq_right hp, ite_eq_right hq]
    dsimp only
    refine congrArg₂ (· / ·) (Finset.sum_congr rfl fun S _ => ?_) (Finset.sum_congr rfl fun S _ => ?_)
    · congr 1
      refine congrArg₂ (· - ·) ?_ ?_
      · congr 2
        refine congrArg Finset.card ?_
        refine hfilt2 (hfilt2 (hfilt2 rfl fun U => ?_) fun _ => Iff.rfl) fun U => ?_
        · constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun x hx b => ?_, h2⟩
          · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).trans (h1 x hx b)
          · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).trans (h1 x hx b)
        · exact iff_of_eq (congrArg (· = S) (hfilt2 rfl fun _ => Iff.rfl))
      · refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
          (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl))))
          (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl)))))
          (congrArg (fun k => ((2 : ℝ) ^ d - 1) ^ k / ((2 : ℝ) ^ d) ^ 4)
            (congrArg Finset.card (hfilt2 rfl fun _ => Iff.rfl)))
    · refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
        (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl))))
        (hite (iff_of_eq (congrArg (S = ·) (hfilt2 rfl fun _ => Iff.rfl)))))
        (congrArg (fun k => ((2 : ℝ) ^ d - 1) ^ k / ((2 : ℝ) ^ d) ^ 4)
          (congrArg Finset.card (hfilt2 rfl fun _ => Iff.rfl)))
  exact (hbridge instF).trans_le hmain


abbrev Space (n : ℕ) := Fin n → F2

noncomputable def supportSub {n : ℕ} (U : Submodule F2 (Space n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

lemma mem_supportSub {n : ℕ} (U : Submodule F2 (Space n)) (i : Fin n) :
    i ∈ supportSub U ↔ ∃ x ∈ U, x i ≠ 0 := by
  simp [supportSub]

def adjacentSub {n : ℕ} (U : Submodule F2 (Space n)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx i) = x (nextIdx i) * y i

lemma f2_one_of_ne {x : F2} (h : x ≠ 0) : x = 1 := by
  rcases f2_eq_zero_or_one x with rfl | rfl
  · exact False.elim (h rfl)
  · rfl

lemma constant_on_pair {n : ℕ} {U : Submodule F2 (Space n)} (h : adjacentSub U) {i : Fin n}
    (hi : i ∈ supportSub U) (hj : nextIdx i ∈ supportSub U) {x : Space n} (hx : x ∈ U) :
    x i = x (nextIdx i) := by
  obtain ⟨a, ha, hai⟩ := (mem_supportSub U i).mp hi
  obtain ⟨b, hb, hbj⟩ := (mem_supportSub U (nextIdx i)).mp hj
  have ai := f2_one_of_ne hai
  have e := h a ha b hb i
  rw [ai, f2_one_of_ne hbj, one_mul] at e
  have aj : a (nextIdx i) ≠ 0 := by
    intro z
    rw [z, zero_mul] at e
    exact one_ne_zero e
  have q := h a ha x hx i
  rw [ai, f2_one_of_ne aj, one_mul, one_mul] at q
  exact q.symm

lemma all_if_forward {n : ℕ} (P : Fin n → Prop) (i : Fin n) (hi : P i)
    (forward : ∀ j, P j → P (nextIdx j)) : ∀ j, P j := by
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  have walk : ∀ k : ℕ, P ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ := by
    intro k
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt i.isLt] using hi
    | succ k ih =>
      have eq : nextIdx (⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ : Fin n) =
          ⟨(i.val + (k + 1)) % n, Nat.mod_lt _ hn⟩ := by
        apply Fin.ext
        change ((i.val + k) % n + 1) % n = (i.val + (k + 1)) % n
        rw [Nat.mod_add_mod, Nat.add_assoc]
      exact eq ▸ forward _ ih
  intro j
  have eq : (⟨(i.val + (n - i.val + j.val)) % n, Nat.mod_lt _ hn⟩ : Fin n) = j := by
    apply Fin.ext
    change (i.val + (n - i.val + j.val)) % n = j.val
    rw [show i.val + (n - i.val + j.val) = n + j.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
  exact eq ▸ walk (n - i.val + j.val)

lemma finrank_le_runsSub {n : ℕ} (U : Submodule F2 (Space n))
    (h : adjacentSub U) (proper : supportSub U ≠ Finset.univ) :
    Module.finrank F2 U ≤ runsCard (supportSub U) := by
  let ev : U →ₗ[F2] (↥(endsSet (supportSub U)) → F2) :=
    { toFun := fun x j => (x : Space n) j.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro x vanish
    apply Subtype.ext
    funext i
    change (x : Space n) i = 0
    by_contra v
    have onward (j : Fin n) (hj : (x : Space n) j ≠ 0) : (x : Space n) (nextIdx j) ≠ 0 := by
      have jmem := (mem_supportSub U j).mpr ⟨x, x.property, hj⟩
      by_cases jm : nextIdx j ∈ supportSub U
      · rwa [← constant_on_pair h jmem jm x.property]
      · have member : j ∈ endsSet (supportSub U) := Finset.mem_filter.mpr ⟨jmem, jm⟩
        have zero := congrFun vanish (⟨j, member⟩ : ↥(endsSet (supportSub U)))
        exact False.elim (hj zero)
    have all := all_if_forward (fun j => (x : Space n) j ≠ 0) i v onward
    apply proper
    exact Finset.eq_univ_of_forall (fun j => (mem_supportSub U j).mpr ⟨x, x.property, all j⟩)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, runsCard] using
    LinearMap.finrank_le_finrank_of_injective inj

lemma full_finrank_le_one {n : ℕ} (hn : 0 < n) (U : Submodule F2 (Space n))
    (h : adjacentSub U) (full : supportSub U = Finset.univ) : Module.finrank F2 U ≤ 1 := by
  let start : Fin n := ⟨0, hn⟩
  let ev : U →ₗ[F2] F2 :=
    { toFun := fun x => (x : Space n) start
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro x vanish
    apply Subtype.ext
    funext j
    have mem (i : Fin n) : i ∈ supportSub U := full ▸ Finset.mem_univ _
    exact all_if_forward (fun i => (x : Space n) i = 0) start vanish
      (fun i hi => (constant_on_pair h (mem i) (mem (nextIdx i)) x.property).symm.trans hi) j
  simpa using LinearMap.finrank_le_finrank_of_injective inj

lemma reachOut {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (i : Fin n) :
    ∃ k : ℕ, nextIdx^[k] i ∉ S := by
  by_contra! h'
  apply h
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨k, hk⟩ := all_if_forward (fun j => ∃ k : ℕ, nextIdx^[k] i = j) i ⟨0, rfl⟩
    (fun j ⟨k, hk⟩ => ⟨k + 1, by rw [Function.iterate_succ_apply', hk]⟩) j
  exact hk ▸ h' k

noncomputable def distOut {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (i : Fin n) : ℕ :=
  Nat.find (reachOut S h i)

lemma out_distOut {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (i : Fin n) :
    nextIdx^[distOut S h i] i ∉ S :=
  Nat.find_spec (reachOut S h i)

lemma in_beforeOut {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n} {k : ℕ}
    (hk : k < distOut S h i) : nextIdx^[k] i ∈ S :=
  not_not.mp (Nat.find_min (reachOut S h i) hk)

lemma distOut_zero {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∉ S) : distOut S h i = 0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' (reachOut S h i) (show nextIdx^[0] i ∉ S from hi))

lemma distOut_step {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∈ S) : distOut S h i = distOut S h (nextIdx i) + 1 := by
  have hpos : 0 < distOut S h i := by
    by_contra! h0
    have H := out_distOut S h i
    rw [Nat.eq_zero_of_le_zero h0] at H
    exact H hi
  have hout := out_distOut S h i
  have hnext : nextIdx^[distOut S h i - 1] (nextIdx i) ∉ S := by
    rw [← Function.iterate_succ_apply, show (distOut S h i - 1).succ = distOut S h i by omega]
    exact hout
  have hl : distOut S h (nextIdx i) ≤ distOut S h i - 1 := Nat.find_min' (reachOut S h (nextIdx i)) hnext
  have hr : distOut S h i ≤ distOut S h (nextIdx i) + 1 := Nat.find_min' (reachOut S h i) (by
    rw [Function.iterate_succ_apply]; exact out_distOut S h (nextIdx i))
  omega

noncomputable def finishOut {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (i : Fin n) : Fin n :=
  nextIdx^[distOut S h i - 1] i

lemma finishOut_end {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∈ S) : finishOut S h i ∈ endsSet S := by
  have H := distOut_step S h hi
  refine Finset.mem_filter.mpr ⟨in_beforeOut S h (by omega), ?_⟩
  change nextIdx (nextIdx^[distOut S h i - 1] i) ∉ S
  rw [← Function.iterate_succ_apply' nextIdx (distOut S h i - 1) i,
    show (distOut S h i - 1).succ = distOut S h i by omega]
  exact out_distOut S h i

lemma finishOut_last {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∈ S) (hn : nextIdx i ∉ S) : finishOut S h i = i := by
  simp [finishOut, distOut_step S h hi, distOut_zero S h hn]

lemma finishOut_next {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) {i : Fin n}
    (hi : i ∈ S) (hn : nextIdx i ∈ S) : finishOut S h i = finishOut S h (nextIdx i) := by
  have h1 := distOut_step S h hn
  simp only [finishOut, distOut_step S h hi, Nat.add_sub_cancel]
  rw [← Function.iterate_succ_apply, show (distOut S h (nextIdx i) - 1).succ = distOut S h (nextIdx i) by omega]

lemma constant_to_endOut {n : ℕ} {C : Type*} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (c : Fin n → C)
    (hc : ∀ i ∈ S, nextIdx i ∈ S → c i = c (nextIdx i)) {i : Fin n} (hi : i ∈ S) :
    c i = c (finishOut S h i) := by
  have h1 := distOut_step S h hi
  suffices H : ∀ k, k < distOut S h i → c i = c (nextIdx^[k] i) from H _ (by omega)
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply']
    have hk' : k < distOut S h i := by omega
    exact (ih hk').trans (hc _ (in_beforeOut S h hk') (Function.iterate_succ_apply' nextIdx k i ▸ in_beforeOut S h hk))

lemma prevIdx_nextIdx_iter {n : ℕ} (k : ℕ) (i : Fin n) : prevIdx^[k] (nextIdx^[k] i) = i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply', prevIdx_nextIdx, ih]

lemma prev_reaches {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    ∃ k : ℕ, prevIdx^[k] j ∈ S := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk⟩ := all_if_forward (fun u => ∃ k : ℕ, nextIdx^[k] s = u) s ⟨0, rfl⟩
    (fun u ⟨k, hk⟩ => ⟨k + 1, by rw [Function.iterate_succ_apply', hk]⟩) j
  refine ⟨k, ?_⟩
  rw [← hk, prevIdx_nextIdx_iter]
  exact hs

noncomputable def zdist {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) : ℕ :=
  Nat.find (prev_reaches S hS j)

lemma zdist_spec {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    prevIdx^[zdist S hS j] j ∈ S :=
  Nat.find_spec (prev_reaches S hS j)

lemma zdist_lt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) {j : Fin n} {k : ℕ}
    (hk : k < zdist S hS j) : prevIdx^[k] j ∉ S :=
  Nat.find_min (prev_reaches S hS j) hk

lemma zdist_eq_zero {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    zdist S hS j = 0 ↔ j ∈ S := by
  constructor
  · intro h; simpa [h] using zdist_spec S hS j
  · intro hj; exact Nat.eq_zero_of_le_zero (Nat.find_min' (prev_reaches S hS j) hj)

lemma zdist_step {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) {j : Fin n} (hj : j ∉ S) :
    zdist S hS j = zdist S hS (prevIdx j) + 1 := by
  have hpos : 0 < zdist S hS j := by
    by_contra! h
    exact hj ((zdist_eq_zero S hS j).mp (Nat.eq_zero_of_le_zero h))
  have h1 : prevIdx^[zdist S hS j - 1] (prevIdx j) ∈ S := by
    rw [← Function.iterate_succ_apply, show (zdist S hS j - 1).succ = zdist S hS j by omega]
    exact zdist_spec S hS j
  have hl : zdist S hS (prevIdx j) ≤ zdist S hS j - 1 := Nat.find_min' (prev_reaches S hS (prevIdx j)) h1
  have hr : zdist S hS j ≤ zdist S hS (prevIdx j) + 1 := Nat.find_min' (prev_reaches S hS j) (by
    rw [Function.iterate_succ_apply]; exact zdist_spec S hS (prevIdx j))
  omega

noncomputable def oddZSet {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ∉ S ∧ zdist S hS j % 2 = 1

lemma runs_le_oddZSet {n : ℕ} (S T : Finset (Fin n)) (hS : S.Nonempty)
    (hST : S ⊆ T) : runsCard T ≤ (oddZSet S hS).card := by
  let W := (endsSet T).image nextIdx
  have hWcard : W.card = runsCard T :=
    Finset.card_image_of_injective _ nextIdx_injective
  have hWout : ∀ w ∈ W, w ∉ T := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2
  have hWnoAdj : ∀ w ∈ W, nextIdx w ∉ W := by
    intro w hw hnw
    rcases Finset.mem_image.mp hnw with ⟨v, hv, heq⟩
    have hv' : v = w := nextIdx_injective heq
    rw [hv'] at hv
    exact hWout w hw (Finset.mem_filter.mp hv).1
  let f : Fin n → Fin n := fun w => if zdist S hS w % 2 = 1 then w else prevIdx w
  have hfMem : ∀ w ∈ W, f w ∈ oddZSet S hS := by
    intro w hw
    have hwS : w ∉ S := fun h => hWout w hw (hST h)
    dsimp only [f]
    split_ifs with hodd
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwS, hodd⟩
    · have hpos : 0 < zdist S hS w := by
        by_contra! h0
        exact hwS ((zdist_eq_zero S hS w).mp (Nat.eq_zero_of_le_zero h0))
      have hge2 : 2 ≤ zdist S hS w := by omega
      have hprevS : prevIdx w ∉ S := by
        intro hp
        have := zdist_step S hS hwS
        rw [(zdist_eq_zero S hS (prevIdx w)).mpr hp] at this
        omega
      have hstep := zdist_step S hS hwS
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprevS, by omega⟩
  have hfInj : Set.InjOn f (W : Set (Fin n)) := by
    intro w₁ hw₁ w₂ hw₂ heq
    dsimp only [f] at heq
    split_ifs at heq with h₁ h₂
    · exact heq
    · have : w₂ = nextIdx w₁ := by rw [heq, nextIdx_prevIdx]
      exact absurd (this ▸ hw₂) (hWnoAdj w₁ hw₁)
    · have : w₁ = nextIdx w₂ := by rw [← heq, nextIdx_prevIdx]
      exact absurd (this ▸ hw₁) (hWnoAdj w₂ hw₂)
    · exact prevIdx_injective heq
  rw [← hWcard]
  exact Finset.card_le_card_of_injOn f hfMem hfInj

noncomputable def Tstar {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) :=
  S ∪ Finset.univ.filter fun j => j ∉ S ∧ nextIdx j ∉ S ∧ zdist S hS j % 2 = 0

lemma Tstar_ne_univ {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    Tstar S hS ≠ Finset.univ := by
  have ⟨s, hs⟩ := hS
  let k := Nat.find (reachOut S hSne s)
  have hk : nextIdx^[k] s ∉ S := Nat.find_spec (reachOut S hSne s)
  have hkpos : 0 < k := by
    by_contra! h0
    have : k = 0 := by omega
    rw [this] at hk
    exact hk hs
  let e := nextIdx^[k - 1] s
  have he : e ∈ S := by
    by_contra he'
    exact Nat.find_min (reachOut S hSne s) (by omega : k - 1 < k) he'
  have hne : nextIdx e ∉ S := by
    change nextIdx (nextIdx^[k - 1] s) ∉ S
    rw [← Function.iterate_succ_apply' nextIdx (k - 1) s, show (k - 1).succ = k by omega]
    exact hk
  have hz : zdist S hS (nextIdx e) = 1 := by
    rw [zdist_step S hS hne, prevIdx_nextIdx, (zdist_eq_zero S hS e).mpr he]
  intro hEq
  have hmem : nextIdx e ∈ Tstar S hS := hEq ▸ Finset.mem_univ _
  rcases Finset.mem_union.mp hmem with h1 | h2
  · exact hne h1
  · have hz0 := (Finset.mem_filter.mp h2).2.2.2
    rw [hz] at hz0
    omega

lemma ends_Tstar_card {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    runsCard (Tstar S hS) = (oddZSet S hS).card := by
  apply Finset.card_bij (fun i _ => nextIdx i)
  · intro i hi
    obtain ⟨hiT, hniT⟩ := Finset.mem_filter.mp hi
    have hniS : nextIdx i ∉ S := fun h => hniT (Finset.mem_union_left _ h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hniS, ?_⟩
    by_contra hnot
    have hzd : zdist S hS (nextIdx i) % 2 = 0 := by omega
    have hpos : 0 < zdist S hS (nextIdx i) := by
      by_contra! h0; exact hniS ((zdist_eq_zero S hS (nextIdx i)).mp (Nat.eq_zero_of_le_zero h0))
    have hiS : i ∉ S := by
      intro hiS
      have := zdist_step S hS hniS
      rw [prevIdx_nextIdx, (zdist_eq_zero S hS i).mpr hiS] at this
      omega
    rcases Finset.mem_union.mp hiT with h | h
    · exact hiS h
    · have hst := zdist_step S hS hniS
      rw [prevIdx_nextIdx] at hst
      have := (Finset.mem_filter.mp h).2.2.2
      omega
  · intro _ _ _ _ h; exact nextIdx_injective h
  · intro j hj
    obtain ⟨_, hjS, hjodd⟩ := Finset.mem_filter.mp hj
    refine ⟨prevIdx j, Finset.mem_filter.mpr ⟨?_, ?_⟩, nextIdx_prevIdx j⟩
    · by_cases hpS : prevIdx j ∈ S
      · exact Finset.mem_union_left _ hpS
      · have hst := zdist_step S hS hjS
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hpS, by rw [nextIdx_prevIdx]; exact hjS, by omega⟩)
    · rw [nextIdx_prevIdx]
      intro hjT
      rcases Finset.mem_union.mp hjT with h | h
      · exact hjS h
      · have := (Finset.mem_filter.mp h).2.2.2
        omega

noncomputable def Vstar {n : ℕ} (T : Finset (Fin n)) : Submodule F2 (Space n) where
  carrier := {x : Space n | (∀ i ∉ T, x i = 0) ∧ (∀ i ∈ T, nextIdx i ∈ T → x i = x (nextIdx i))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩; add_mem' := by
    intro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun i hi => by simp [hx1 i hi, hy1 i hi], fun i hi hni => by simp [hx2 i hi hni, hy2 i hi hni]⟩
  smul_mem' := by
    intro c x ⟨hx1, hx2⟩
    refine ⟨fun i hi => by simp [hx1 i hi], fun i hi hni => by simp [hx2 i hi hni]⟩

lemma Vstar_adjacent {n : ℕ} (T : Finset (Fin n)) : adjacentSub (Vstar T) := by
  intro x hx y hy i
  by_cases hi : i ∈ T
  · by_cases hni : nextIdx i ∈ T
    · rw [hx.2 i hi hni, hy.2 i hi hni]
    · simp [hx.1 _ hni, hy.1 _ hni]
  · simp [hx.1 i hi, hy.1 i hi]

lemma Vstar_finrank {n : ℕ} (T : Finset (Fin n)) (hT : T ≠ Finset.univ) :
    Module.finrank F2 (Vstar T) = runsCard T := by
  let toFun : Vstar T →ₗ[F2] (↥(endsSet T) → F2) :=
    { toFun := fun x j => x.1 j.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let invFun : (↥(endsSet T) → F2) → Vstar T := fun y =>
    ⟨fun i => if hi : i ∈ T then y ⟨finishOut T hT i, finishOut_end T hT hi⟩ else 0,
     fun i hi => by simp [hi],
     fun i hi hni => by
       have H : (⟨finishOut T hT i, finishOut_end T hT hi⟩ : ↥(endsSet T)) =
           ⟨finishOut T hT (nextIdx i), finishOut_end T hT hni⟩ :=
         Subtype.ext (finishOut_next T hT hi hni)
       simp [hi, hni, H]⟩
  have e : Vstar T ≃ₗ[F2] (↥(endsSet T) → F2) :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun x => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ T
        · simp only [invFun, toFun, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left hi]
          exact (constant_to_endOut T hT x.1 x.2.2 hi).symm
        · simp only [invFun, toFun, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hi]
          exact (x.2.1 i hi).symm
      right_inv := fun y => by
        funext j
        have hj := Finset.mem_filter.mp j.2
        have H : (⟨finishOut T hT j.1, finishOut_end T hT hj.1⟩ : ↥(endsSet T)) = j :=
          Subtype.ext (finishOut_last T hT hj.1 hj.2)
        simp [toFun, invFun, hj.1, H]
      map_add' := toFun.map_add'
      map_smul' := toFun.map_smul' }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, runsCard]

lemma U_le_Vstar {n : ℕ} (U : Submodule F2 (Space n)) (hU : adjacentSub U) (hS : (supportSub U).Nonempty) :
    U ≤ Vstar (Tstar (supportSub U) hS) := by
  intro x hx
  let S := supportSub U
  refine ⟨fun i hi => ?_, fun i hi hni => ?_⟩
  · have hiS : i ∉ S := fun h => hi (Finset.mem_union_left _ h)
    by_contra hne
    exact hiS ((mem_supportSub U i).mpr ⟨x, hx, hne⟩)
  · have vanish (u : Fin n) (hu : u ∉ S) : x u = 0 := by
      by_contra hne; exact hu ((mem_supportSub U u).mpr ⟨x, hx, hne⟩)
    by_cases hiS : i ∈ S
    · have hniS : nextIdx i ∈ S := by
        by_contra hniS
        have hz : zdist S hS (nextIdx i) = 1 := by
          rw [zdist_step S hS hniS, prevIdx_nextIdx, (zdist_eq_zero S hS i).mpr hiS]
        rcases Finset.mem_union.mp hni with h | h
        · exact hniS h
        · have hz0 := (Finset.mem_filter.mp h).2.2.2
          rw [hz] at hz0
          omega
      exact constant_on_pair hU hiS hniS hx
    · have hniS : nextIdx i ∉ S := by
        rcases Finset.mem_union.mp hi with h | h
        · exact absurd h hiS
        · exact (Finset.mem_filter.mp h).2.2.1
      rw [vanish i hiS, vanish (nextIdx i) hniS]

lemma host_bounds {n d : ℕ} (hd : 2 ≤ d) (H : Fin n → Fin 4 → F2)
    (U : Submodule F2 (Space n))
    (hUd : Module.finrank F2 U = d)
    (hUcheck : ∀ x ∈ U, ∀ b : Fin 4, (∑ i, H i b * x i) = 0)
    (hUadj : adjacentSub U)
    (hS : (supportSub U).Nonempty)
    [Fintype (Submodule F2 (Space n))] :
    let S := supportSub U
    let spaces := (Finset.univ : Finset (Submodule F2 (Space n))).filter
      (fun E => (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacentSub E)
    (oddZSet S hS).card - 4 ≤
      (spaces.filter (fun E => U ≤ E)).sup (fun E => Module.finrank F2 E) ∧
    (spaces.filter (fun E => U ≤ E)).sup (fun E => Module.finrank F2 E) ≤
      (oddZSet S hS).card := by
  dsimp only
  let S := supportSub U
  have hn : 0 < n := by obtain ⟨s, _⟩ := hS; exact (Nat.zero_le _).trans_lt s.isLt
  have hSne : S ≠ Finset.univ := by
    intro hfull
    have r : Module.finrank F2 U ≤ 1 := full_finrank_le_one hn U hUadj hfull
    omega
  constructor
  · let T := Tstar S hS
    have hTne : T ≠ Finset.univ := Tstar_ne_univ S hS hSne
    let checkMap : Space n →ₗ[F2] (Fin 4 → F2) :=
      { toFun := fun x b => ∑ i, H i b * x i
        map_add' := fun x y => by ext b; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by ext b; simp [Finset.mul_sum, mul_left_comm] }
    let res := checkMap.domRestrict (Vstar T)
    let E : Submodule F2 (Space n) := Vstar T ⊓ LinearMap.ker checkMap
    have hUE : U ≤ E := le_inf (U_le_Vstar U hUadj hS) (fun x hx => by ext b; exact hUcheck x hx b)
    have hEgood : (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacentSub E := by
      refine ⟨fun x hx b => ?_, fun x hx y hy i => Vstar_adjacent T x hx.1 y hy.1 i⟩
      exact congrFun hx.2 b
    have hEmem : E ∈ ((Finset.univ : Finset (Submodule F2 (Space n))).filter
        (fun E => (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacentSub E)).filter (fun E => U ≤ E) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEgood⟩, hUE⟩
    have hker : E = (LinearMap.ker res).map (Vstar T).subtype := by
      ext x
      simp only [E, res, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.domRestrict_apply, Submodule.coe_subtype]
      constructor
      · rintro ⟨hxV, hxk⟩
        exact ⟨⟨x, hxV⟩, hxk, rfl⟩
      · rintro ⟨⟨y, hyV⟩, hyk, rfl⟩
        exact ⟨hyV, hyk⟩
    have hdimE : Module.finrank F2 E = Module.finrank F2 (LinearMap.ker res) := by
      rw [hker]
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Vstar T).subtype (Submodule.injective_subtype _) _).symm
    have hrk := LinearMap.finrank_range_add_finrank_ker res
    have hrng : Module.finrank F2 (LinearMap.range res) ≤ 4 := by
      have hle := Submodule.finrank_le (LinearMap.range res)
      simpa [Module.finrank_fintype_fun_eq_card] using hle
    have hVdim : Module.finrank F2 (Vstar T) = (oddZSet S hS).card := by
      rw [Vstar_finrank T hTne, ends_Tstar_card S hS]
    have hle : (oddZSet S hS).card - 4 ≤ Module.finrank F2 E := by omega
    exact hle.trans (Finset.le_sup (f := fun (E : Submodule F2 (Space n)) => Module.finrank F2 E) hEmem)
  · apply Finset.sup_le
    intro E hE
    obtain ⟨hE1, hUE⟩ := Finset.mem_filter.mp hE
    obtain ⟨_, hEgood⟩ := Finset.mem_filter.mp hE1
    have hST : S ⊆ supportSub E := by
      intro i hi
      obtain ⟨x, hxU, hxi⟩ := (mem_supportSub U i).mp hi
      exact (mem_supportSub E i).mpr ⟨x, hUE hxU, hxi⟩
    have hTne : supportSub E ≠ Finset.univ := by
      intro hfull
      have r : Module.finrank F2 E ≤ 1 := full_finrank_le_one hn E hEgood.2 hfull
      have rd : d ≤ Module.finrank F2 E := by
        rw [← hUd]
        exact Submodule.finrank_mono hUE
      omega
    exact (finrank_le_runsSub E hEgood.2 hTne).trans (runs_le_oddZSet S (supportSub E) hS hST)

noncomputable def remOdd {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) :=
  Finset.univ.filter fun j => 3 ≤ zdist S hS j ∧ zdist S hS j % 2 = 1

lemma oddZSet_card_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    (oddZSet S hS).card = runsCard S + (remOdd S hS).card := by
  let oneZ : Finset (Fin n) := Finset.univ.filter fun j => zdist S hS j = 1
  have hdisj : Disjoint oneZ (remOdd S hS) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2.1
    omega
  have hunion : oddZSet S hS = oneZ ∪ remOdd S hS := by
    ext j
    simp only [oddZSet, oneZ, remOdd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hjS, hmod⟩
      have hne0 : zdist S hS j ≠ 0 := by
        intro h0
        exact hjS ((zdist_eq_zero S hS j).mp h0)
      by_cases h1 : zdist S hS j = 1
      · left; exact h1
      · right; exact ⟨by omega, hmod⟩
    · rintro (h1 | ⟨h3, hmod⟩)
      · exact ⟨fun hjS => by have := (zdist_eq_zero S hS j).mpr hjS; omega, by omega⟩
      · exact ⟨fun hjS => by have := (zdist_eq_zero S hS j).mpr hjS; omega, hmod⟩
  have hruns : oneZ.card = runsCard S := by
    unfold runsCard endsSet
    symm
    refine Finset.card_bij (fun i _ => nextIdx i) ?_ ?_ ?_
    · intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiS, hniS⟩
      simp only [oneZ, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [zdist_step S hS hniS, prevIdx_nextIdx, (zdist_eq_zero S hS i).mpr hiS]
    · intro a _ b _ h
      exact nextIdx_injective h
    · intro j hj
      have hj1 : zdist S hS j = 1 := (Finset.mem_filter.mp hj).2
      have hjS : j ∉ S := fun hs => by have := (zdist_eq_zero S hS j).mpr hs; omega
      have hpz : zdist S hS (prevIdx j) = 0 := by
        have := zdist_step S hS hjS
        omega
      refine ⟨prevIdx j, Finset.mem_filter.mpr ⟨(zdist_eq_zero S hS (prevIdx j)).mp hpz, ?_⟩, nextIdx_prevIdx j⟩
      rwa [nextIdx_prevIdx]
  rw [hunion, Finset.card_union_of_disjoint hdisj, hruns]

def binomProb (n : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  (Nat.choose n m : ℝ) * p ^ m * (1 - p) ^ (n - m)

lemma binomProb_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    0 ≤ binomProb n p m := by
  unfold binomProb
  have h1 : 0 ≤ 1 - p := by linarith
  positivity

lemma sum_binomProb (n : ℕ) (p : ℝ) :
    ∑ m ∈ Finset.range (n + 1), binomProb n p m = 1 := by
  have h := add_pow p (1 - p) n
  have h1 : p + (1 - p) = 1 := by ring
  rw [h1, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold binomProb
  ring

lemma sum_alt_binomProb (n : ℕ) (p : ℝ) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m * binomProb n p m = (1 - 2 * p) ^ n := by
  have h := add_pow (-p) (1 - p) n
  have h1 : -p + (1 - p) = 1 - 2 * p := by ring
  rw [h1] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold binomProb
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

lemma two_mul_sum_even_sub_sum (f : ℕ → ℝ) (K : ℕ) :
    2 * (∑ m ∈ (Finset.range K).filter Even, f m) - (∑ m ∈ Finset.range K, f m) =
      ∑ m ∈ Finset.range K, (-1 : ℝ) ^ m * f m := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : Even m
  · rw [ite_eq_left hm, Even.neg_one_pow hm]; ring
  · rw [ite_eq_right hm, Odd.neg_one_pow (Nat.not_even_iff_odd.mp hm)]; ring

lemma alt_sum_mono_bounds (f : ℕ → ℝ) :
    ∀ M : ℕ, (∀ m ≤ M, 0 ≤ f m) → (∀ m < M, f m ≤ f (m + 1)) →
      0 ≤ (-1 : ℝ) ^ M * (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m) ∧
      (-1 : ℝ) ^ M * (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m) ≤ f M := by
  intro M
  induction M with
  | zero =>
    intro hnn _
    simp [hnn 0 le_rfl]
  | succ M ih =>
    intro hnn hmono
    have ih' := ih (fun m hm => hnn m (Nat.le_succ_of_le hm))
      (fun m hm => hmono m (Nat.lt_succ_of_lt hm))
    have hstep : (-1 : ℝ) ^ (M + 1) * (∑ m ∈ Finset.range (M + 2), (-1 : ℝ) ^ m * f m) =
        f (M + 1) - (-1 : ℝ) ^ M * (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m) := by
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have hsq : (-1 : ℝ) ^ M * (-1 : ℝ) ^ M = 1 := by
        rw [← mul_pow]; norm_num
      have hsq2 : (-1 : ℝ) ^ M * (-1 : ℝ) * ((-1 : ℝ) ^ M * (-1 : ℝ) * f (M + 1)) = f (M + 1) := by
        calc (-1 : ℝ) ^ M * (-1 : ℝ) * ((-1 : ℝ) ^ M * (-1 : ℝ) * f (M + 1))
            = ((-1 : ℝ) ^ M * (-1 : ℝ) ^ M) * ((-1 : ℝ) * (-1 : ℝ)) * f (M + 1) := by ring
          _ = f (M + 1) := by rw [hsq]; ring
      rw [hsq2]
      ring
    rw [hstep]
    have hle : f M ≤ f (M + 1) := hmono M (Nat.lt_succ_self M)
    constructor <;> linarith

lemma abs_alt_sum_le_of_mono (f : ℕ → ℝ) (M : ℕ)
    (hnn : ∀ m ≤ M, 0 ≤ f m) (hmono : ∀ m < M, f m ≤ f (m + 1)) :
    |∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m| ≤ f M := by
  have hb := alt_sum_mono_bounds f M hnn hmono
  have habs : |∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m| =
      |(-1 : ℝ) ^ M * (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs, abs_of_nonneg hb.1]
  exact hb.2

lemma alt_sum_anti_bounds :
    ∀ M : ℕ, ∀ f : ℕ → ℝ, (∀ m ≤ M, 0 ≤ f m) → (∀ m < M, f (m + 1) ≤ f m) →
      0 ≤ (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m) ∧
      (∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m) ≤ f 0 := by
  intro M
  induction M with
  | zero =>
    intro f hnn _
    simp [hnn 0 le_rfl]
  | succ M ih =>
    intro f hnn hanti
    have ih' := ih (fun m => f (m + 1))
      (fun m hm => hnn (m + 1) (Nat.succ_le_succ hm))
      (fun m hm => hanti (m + 1) (Nat.succ_lt_succ hm))
    have hstep : ∑ m ∈ Finset.range (M + 2), (-1 : ℝ) ^ m * f m =
        f 0 - ∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f (m + 1) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul]
      have hneg : ∑ k ∈ Finset.range (M + 1), (-1 : ℝ) ^ (k + 1) * f (k + 1) =
          -(∑ k ∈ Finset.range (M + 1), (-1 : ℝ) ^ k * f (k + 1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ]; ring
      rw [hneg]; ring
    rw [hstep]
    have hle : f 1 ≤ f 0 := hanti 0 (Nat.succ_pos M)
    constructor <;> linarith

lemma abs_alt_sum_le_of_anti (f : ℕ → ℝ) (M : ℕ)
    (hnn : ∀ m ≤ M, 0 ≤ f m) (hanti : ∀ m < M, f (m + 1) ≤ f m) :
    |∑ m ∈ Finset.range (M + 1), (-1 : ℝ) ^ m * f m| ≤ f 0 := by
  have hb := alt_sum_anti_bounds M f hnn hanti
  rw [abs_of_nonneg hb.1]
  exact hb.2

lemma binomProb_ratio (n : ℕ) (p : ℝ) (m : ℕ) (hm : m < n) :
    binomProb n p (m + 1) * ((m + 1 : ℝ) * (1 - p)) =
      binomProb n p m * ((n - m : ℝ) * p) := by
  unfold binomProb
  have hch : ((Nat.choose n (m + 1) : ℕ) : ℝ) * (m + 1 : ℝ) =
      ((Nat.choose n m : ℕ) : ℝ) * (n - m : ℝ) := by
    have hnat := (Nat.choose_succ_right_eq n m).symm
    have hcast : ((Nat.choose n m * (n - m) : ℕ) : ℝ) = ((Nat.choose n (m + 1) * (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub (le_of_lt hm)] at hcast
    linarith
  have hsub : n - m = (n - (m + 1)) + 1 := by omega
  rw [hsub, pow_succ (1 - p) (n - (m + 1)), pow_succ p m]
  calc ((Nat.choose n (m + 1) : ℝ) * (p ^ m * p) * (1 - p) ^ (n - (m + 1))) * ((m + 1 : ℝ) * (1 - p))
      = ((Nat.choose n (m + 1) : ℝ) * (m + 1 : ℝ)) * (p ^ m * p * ((1 - p) ^ (n - (m + 1)) * (1 - p))) := by ring
    _ = ((Nat.choose n m : ℝ) * (n - m : ℝ)) * (p ^ m * p * ((1 - p) ^ (n - (m + 1)) * (1 - p))) := by rw [hch]
    _ = (Nat.choose n m : ℝ) * p ^ m * ((1 - p) ^ (n - (m + 1)) * (1 - p)) * ((n - m : ℝ) * p) := by ring

lemma binomProb_mono_le_mode {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {m : ℕ} (hm : m < Nat.floor ((n + 1 : ℝ) * p)) :
    binomProb n p m ≤ binomProb n p (m + 1) := by
  have hm1_le : (m + 1 : ℝ) ≤ (n + 1 : ℝ) * p := by
    have h1 : m + 1 ≤ Nat.floor ((n + 1 : ℝ) * p) := Nat.succ_le_of_lt hm
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((Nat.floor ((n + 1 : ℝ) * p) : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((Nat.floor ((n + 1 : ℝ) * p) : ℕ) : ℝ) ≤ (n + 1 : ℝ) * p :=
      Nat.floor_le (by positivity)
    push_cast at h2
    linarith
  have hmn : m < n := by
    by_contra hge
    push Not at hge
    have : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hge
    have : (n + 1 : ℝ) * p < (n + 1 : ℝ) * 1 := mul_lt_mul_of_pos_left hp1 (by positivity)
    linarith
  have hrat := binomProb_ratio n p m hmn
  have hden : 0 < (m + 1 : ℝ) * (1 - p) := by
    have : 0 < 1 - p := by linarith
    positivity
  have hcmp : (m + 1 : ℝ) * (1 - p) ≤ ((n : ℝ) - m) * p := by linarith
  have hnn : 0 ≤ binomProb n p m := binomProb_nonneg (le_of_lt hp0) (le_of_lt hp1) m
  nlinarith

lemma binomProb_anti_ge_mode {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {m : ℕ} (hm : Nat.floor ((n + 1 : ℝ) * p) ≤ m) :
    binomProb n p (m + 1) ≤ binomProb n p m := by
  by_cases hmn : m < n
  · have hgt : (n + 1 : ℝ) * p < (m + 1 : ℝ) := by
      have h1 : (n + 1 : ℝ) * p < (Nat.floor ((n + 1 : ℝ) * p) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (Nat.floor ((n + 1 : ℝ) * p) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hrat := binomProb_ratio n p m hmn
    have hden : 0 < (m + 1 : ℝ) * (1 - p) := by
      have : 0 < 1 - p := by linarith
      positivity
    have hcmp : ((n : ℝ) - m) * p ≤ (m + 1 : ℝ) * (1 - p) := by linarith
    have hnn : 0 ≤ binomProb n p m := binomProb_nonneg (le_of_lt hp0) (le_of_lt hp1) m
    nlinarith
  · have hzero : binomProb n p (m + 1) = 0 := by
      unfold binomProb
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hzero]
    exact binomProb_nonneg (le_of_lt hp0) (le_of_lt hp1) m

lemma abs_alt_sum_binomProb_le_two_peak {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) :
    |∑ m ∈ Finset.range K, (-1 : ℝ) ^ m * binomProb n p m| ≤
      2 * binomProb n p (Nat.floor ((n + 1 : ℝ) * p)) := by
  set mstar := Nat.floor ((n + 1 : ℝ) * p)
  have hnn : ∀ m, 0 ≤ binomProb n p m := binomProb_nonneg (le_of_lt hp0) (le_of_lt hp1)
  have hle_peak : ∀ m, binomProb n p m ≤ binomProb n p mstar := by
    intro m
    by_cases h : m ≤ mstar
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hup : ∀ j ≤ k, binomProb n p m ≤ binomProb n p (m + j) := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ih =>
          exact (ih (Nat.le_of_succ_le hj)).trans
            (binomProb_mono_le_mode hp0 hp1 (by omega))
      simpa [← hk] using hup k le_rfl
    · push Not at h
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_of_lt h)
      have hdn : ∀ j, binomProb n p (mstar + j) ≤ binomProb n p mstar := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have hge : Nat.floor ((n + 1 : ℝ) * p) ≤ mstar + j := Nat.le_add_right _ _
          exact (binomProb_anti_ge_mode hp0 hp1 hge).trans ih
      simpa [← hk] using hdn k
  cases K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    linarith [hnn mstar]
  | succ K' =>
    by_cases hKm : K' ≤ mstar
    · have h1 := abs_alt_sum_le_of_mono (binomProb n p) K' (fun m _ => hnn m)
        (fun m hm => binomProb_mono_le_mode hp0 hp1 (lt_of_lt_of_le hm hKm))
      linarith [hle_peak K', hnn mstar]
    · push Not at hKm
      have hsplit : ∑ m ∈ Finset.range (K' + 1), (-1 : ℝ) ^ m * binomProb n p m =
          (∑ m ∈ Finset.range (mstar + 1), (-1 : ℝ) ^ m * binomProb n p m) +
          (-1 : ℝ) ^ (mstar + 1) *
            (∑ j ∈ Finset.range (K' - mstar), (-1 : ℝ) ^ j * binomProb n p (mstar + 1 + j)) := by
        have hlen : K' + 1 = (mstar + 1) + (K' - mstar) := by omega
        rw [hlen, Finset.sum_range_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_add]; ring
      rw [hsplit]
      have hpart1 : |∑ m ∈ Finset.range (mstar + 1), (-1 : ℝ) ^ m * binomProb n p m| ≤
          binomProb n p mstar :=
        abs_alt_sum_le_of_mono (binomProb n p) mstar (fun m _ => hnn m)
          (fun m hm => binomProb_mono_le_mode hp0 hp1 hm)
      have hpart2 : |(-1 : ℝ) ^ (mstar + 1) *
          (∑ j ∈ Finset.range (K' - mstar), (-1 : ℝ) ^ j * binomProb n p (mstar + 1 + j))| ≤
          binomProb n p (mstar + 1) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have hkm : K' - mstar = (K' - mstar - 1) + 1 := by omega
        rw [hkm]
        simpa using abs_alt_sum_le_of_anti (fun j => binomProb n p (mstar + 1 + j)) (K' - mstar - 1)
          (fun j _ => hnn _) (fun j _ => binomProb_anti_ge_mode hp0 hp1 (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)))
      have htri := abs_add_le
        (∑ m ∈ Finset.range (mstar + 1), (-1 : ℝ) ^ m * binomProb n p m)
        ((-1 : ℝ) ^ (mstar + 1) *
          (∑ j ∈ Finset.range (K' - mstar), (-1 : ℝ) ^ j * binomProb n p (mstar + 1 + j)))
      linarith [hle_peak (mstar + 1)]

lemma bernoulli_sub_le (u : ℝ) (hu1 : u ≤ 1) :
    ∀ k : ℕ, 1 - (k : ℝ) * u ≤ (1 - u) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : 0 ≤ 1 - u := by linarith
    have h2 : (1 - (k : ℝ) * u) * (1 - u) ≤ (1 - u) ^ k * (1 - u) :=
      mul_le_mul_of_nonneg_right ih h1
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg u)]

lemma binomProb_peak_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 10)
    (hmu : 100 ≤ (n : ℝ) * p) :
    binomProb n p (Nat.floor ((n + 1 : ℝ) * p)) ≤ 4 / Real.sqrt ((n : ℝ) * p) := by
  set mu : ℝ := (n : ℝ) * p
  set mstar : ℕ := Nat.floor ((n + 1 : ℝ) * p)
  set J : ℕ := Nat.floor (Real.sqrt mu / 2)
  have hsqrt_ge : 10 ≤ Real.sqrt mu := by
    have : Real.sqrt (10 ^ 2) ≤ Real.sqrt mu := Real.sqrt_le_sqrt (by linarith)
    simpa using this
  have hsqrt_pos : 0 < Real.sqrt mu := by linarith
  have hsqrt_sq : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt (by linarith)
  have hJ_le : (J : ℝ) ≤ Real.sqrt mu / 2 := Nat.floor_le (by positivity)
  have hJ_gt : Real.sqrt mu / 2 - 1 < (J : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt mu / 2)
    linarith
  have hJ_ge4 : 4 ≤ J := by
    have : (4 : ℝ) ≤ Real.sqrt mu / 2 := by linarith
    exact Nat.le_floor this
  have hmstar_le : (mstar : ℝ) ≤ mu + p := by
    have := Nat.floor_le (show 0 ≤ (n + 1 : ℝ) * p by positivity)
    linarith
  have hmstar_gt : mu + p - 1 < (mstar : ℝ) := by
    have := Nat.lt_floor_add_one ((n + 1 : ℝ) * p)
    linarith
  have hmstar_ge_J : J ≤ mstar := by
    have hJlt : (J : ℝ) ≤ mu - 1 := by nlinarith
    have : (J : ℝ) < (mstar : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hmstar_le_n : mstar ≤ n := by
    have hmu_le_n : mu ≤ (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have h2 : (mstar : ℝ) ≤ (n : ℝ) + 1 / 10 := by linarith
    by_contra hgt
    push Not at hgt
    have : (n : ℝ) + 1 ≤ (mstar : ℝ) := by exact_mod_cast hgt
    linarith
  set u : ℝ := ((J : ℝ) + 1) / ((4 / 5 : ℝ) * mu)
  have hu0 : 0 ≤ u := by positivity
  have hJprod : (J : ℝ) * ((J : ℝ) + 1) ≤ (3 / 10 : ℝ) * mu := by
    nlinarith [hJ_le, hsqrt_ge, hsqrt_sq]
  have hJu : (J : ℝ) * u ≤ 1 / 2 := by
    unfold u
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    linarith
  have hu1 : u ≤ 1 := by
    have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : 1 ≤ J)
    nlinarith
  have hstep : ∀ j < J, (1 - u) * binomProb n p (mstar - j) ≤ binomProb n p (mstar - (j + 1)) := by
    intro j hj
    set m := mstar - (j + 1)
    have hm1 : m + 1 = mstar - j := by omega
    have hmn : m < n := by omega
    have hrat := binomProb_ratio n p m hmn
    rw [hm1] at hrat
    have hden_pos : 0 < ((n : ℝ) - m) * p := by
      have : (m : ℝ) ≤ (mstar : ℝ) := by exact_mod_cast (by omega : m ≤ mstar)
      nlinarith
    have hden_ge : (4 / 5 : ℝ) * mu ≤ ((n : ℝ) - m) * p := by
      have : (m : ℝ) ≤ (mstar : ℝ) := by exact_mod_cast (by omega : m ≤ mstar)
      nlinarith
    have hdiff_le : ((n : ℝ) - m) * p - (m + 1 : ℝ) * (1 - p) ≤ (J : ℝ) + 1 := by
      have hm_ge : (mstar : ℝ) - (J : ℝ) ≤ (m : ℝ) := by
        have : mstar - J ≤ m := by omega
        have hcast : ((mstar - J : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub hmstar_ge_J] at hcast
        exact hcast
      linarith
    have hfac : (1 - u) * (((n : ℝ) - m) * p) ≤ (m + 1 : ℝ) * (1 - p) := by
      have hu_mul : u * (((n : ℝ) - m) * p) ≥ (J : ℝ) + 1 := by
        unfold u
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hnn_b : 0 ≤ binomProb n p (mstar - j) := binomProb_nonneg (le_of_lt hp0) (by linarith) _
    have hmul : (1 - u) * binomProb n p (mstar - j) * (((n : ℝ) - m) * p) ≤
        binomProb n p m * (((n : ℝ) - m) * p) := by
      calc (1 - u) * binomProb n p (mstar - j) * (((n : ℝ) - m) * p)
          = binomProb n p (mstar - j) * ((1 - u) * (((n : ℝ) - m) * p)) := by ring
        _ ≤ binomProb n p (mstar - j) * ((m + 1 : ℝ) * (1 - p)) :=
            mul_le_mul_of_nonneg_left hfac hnn_b
        _ = binomProb n p m * (((n : ℝ) - m) * p) := hrat
    exact le_of_mul_le_mul_right hmul hden_pos
  have hlower : ∀ j ≤ J, (1 / 2 : ℝ) * binomProb n p mstar ≤ binomProb n p (mstar - j) := by
    have hpow : ∀ j ≤ J, (1 - u) ^ j * binomProb n p mstar ≤ binomProb n p (mstar - j) := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', mul_assoc]
        exact (mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hj)) (by linarith)).trans
          (hstep j (Nat.lt_of_succ_le hj))
    intro j hj
    have hb1 : (1 - (j : ℝ) * u) ≤ (1 - u) ^ j := bernoulli_sub_le u hu1 j
    have hb2 : (1 / 2 : ℝ) ≤ 1 - (j : ℝ) * u := by
      have hjJ : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
      nlinarith
    have hnn_m : 0 ≤ binomProb n p mstar := binomProb_nonneg (le_of_lt hp0) (by linarith) _
    exact (mul_le_mul_of_nonneg_right (hb2.trans hb1) hnn_m).trans (hpow j hj)
  have hsum_le : ∑ j ∈ Finset.range (J + 1), binomProb n p (mstar - j) ≤ 1 := by
    rw [← sum_binomProb n p]
    let img := (Finset.range (J + 1)).image (fun j => mstar - j)
    have hsub : img ⊆ Finset.range (n + 1) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      rw [Finset.mem_range]; omega
    have hinj : Set.InjOn (fun j => mstar - j) (Finset.range (J + 1) : Set ℕ) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_range] at ha hb
      dsimp only at hab
      omega
    have hsum_eq : ∑ j ∈ Finset.range (J + 1), binomProb n p (mstar - j) =
        ∑ x ∈ img, binomProb n p x := (Finset.sum_image (fun a ha b hb h => hinj ha hb h)).symm
    rw [hsum_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => binomProb_nonneg (le_of_lt hp0) (by linarith) x)
  have hsum_ge : ((J + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * binomProb n p mstar) ≤
      ∑ j ∈ Finset.range (J + 1), binomProb n p (mstar - j) := by
    calc ((J + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * binomProb n p mstar)
        = ∑ _j ∈ Finset.range (J + 1), ((1 / 2 : ℝ) * binomProb n p mstar) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range (J + 1), binomProb n p (mstar - j) :=
            Finset.sum_le_sum fun j hj => hlower j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hJ1_ge : Real.sqrt mu / 2 ≤ ((J + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hnn_m : 0 ≤ binomProb n p mstar := binomProb_nonneg (le_of_lt hp0) (by linarith) _
  rw [le_div_iff₀ hsqrt_pos]
  nlinarith

lemma trig_poly_bounds_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - Real.sin t ∧
    0 ≤ t ^ 2 / 2 - (1 - Real.cos t) ∧
    0 ≤ t ^ 3 / 6 - (t - Real.sin t) ∧
    0 ≤ t ^ 4 / 24 - (t ^ 2 / 2 - (1 - Real.cos t)) := by
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have h1 : ∀ x ≥ 0, 0 ≤ x - Real.sin x := by
    intro x hx
    have hmono : MonotoneOn (fun y => y - Real.sin y) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (continuous_id.sub Real.continuous_sin).continuousOn
      · exact (differentiable_id.sub Real.differentiable_sin).differentiableOn
      · intro y _
        have hd : HasDerivAt (fun y => y - Real.sin y) (1 - Real.cos y) y :=
          (hasDerivAt_id y).sub (Real.hasDerivAt_sin y)
        rw [hd.deriv]
        linarith [Real.cos_le_one y]
    simpa using hmono h0 hx hx
  have h2 : ∀ x ≥ 0, 0 ≤ x ^ 2 / 2 - (1 - Real.cos x) := by
    intro x hx
    have hmono : MonotoneOn (fun y => y ^ 2 / 2 - (1 - Real.cos y)) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((continuous_pow 2).div_const 2 |>.sub (continuous_const.sub Real.continuous_cos)).continuousOn
      · exact (((differentiable_pow 2).div_const 2).sub (differentiable_const 1 |>.sub Real.differentiable_cos)).differentiableOn
      · intro y hy
        have hd : HasDerivAt (fun y => y ^ 2 / 2 - (1 - Real.cos y)) (y - Real.sin y) y := by
          have hd1 : HasDerivAt (fun y => y ^ 2 / 2) y y := by
            convert (hasDerivAt_pow 2 y).div_const 2 using 1; ring
          have hd2 : HasDerivAt (fun y => 1 - Real.cos y) (Real.sin y) y := by
            convert (hasDerivAt_const y (1 : ℝ)).sub (Real.hasDerivAt_cos y) using 1; ring
          exact hd1.sub hd2
        rw [hd.deriv]
        exact h1 y (le_of_lt (by simpa [interior_Ici] using hy))
    simpa using hmono h0 hx hx
  have h3 : ∀ x ≥ 0, 0 ≤ x ^ 3 / 6 - (x - Real.sin x) := by
    intro x hx
    have hmono : MonotoneOn (fun y => y ^ 3 / 6 - (y - Real.sin y)) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((continuous_pow 3).div_const 6 |>.sub (continuous_id.sub Real.continuous_sin)).continuousOn
      · exact (((differentiable_pow 3).div_const 6).sub (differentiable_id.sub Real.differentiable_sin)).differentiableOn
      · intro y hy
        have hd : HasDerivAt (fun y => y ^ 3 / 6 - (y - Real.sin y)) (y ^ 2 / 2 - (1 - Real.cos y)) y := by
          have hd1 : HasDerivAt (fun y => y ^ 3 / 6) (y ^ 2 / 2) y := by
            convert (hasDerivAt_pow 3 y).div_const 6 using 1; ring
          have hd2 : HasDerivAt (fun y => y - Real.sin y) (1 - Real.cos y) y :=
            (hasDerivAt_id y).sub (Real.hasDerivAt_sin y)
          exact hd1.sub hd2
        rw [hd.deriv]
        exact h2 y (le_of_lt (by simpa [interior_Ici] using hy))
    simpa using hmono h0 hx hx
  have h4 : ∀ x ≥ 0, 0 ≤ x ^ 4 / 24 - (x ^ 2 / 2 - (1 - Real.cos x)) := by
    intro x hx
    have hmono : MonotoneOn (fun y => y ^ 4 / 24 - (y ^ 2 / 2 - (1 - Real.cos y))) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((continuous_pow 4).div_const 24 |>.sub ((continuous_pow 2).div_const 2 |>.sub (continuous_const.sub Real.continuous_cos))).continuousOn
      · exact (((differentiable_pow 4).div_const 24).sub (((differentiable_pow 2).div_const 2).sub ((differentiable_const 1).sub Real.differentiable_cos))).differentiableOn
      · intro y hy
        have hd : HasDerivAt (fun y => y ^ 4 / 24 - (y ^ 2 / 2 - (1 - Real.cos y)))
            (y ^ 3 / 6 - (y - Real.sin y)) y := by
          have hd1 : HasDerivAt (fun y => y ^ 4 / 24) (y ^ 3 / 6) y := by
            convert (hasDerivAt_pow 4 y).div_const 24 using 1; ring
          have hd2 : HasDerivAt (fun y => y ^ 2 / 2 - (1 - Real.cos y)) (y - Real.sin y) y := by
            have hd2a : HasDerivAt (fun y => y ^ 2 / 2) y y := by
              convert (hasDerivAt_pow 2 y).div_const 2 using 1; ring
            have hd2b : HasDerivAt (fun y => 1 - Real.cos y) (Real.sin y) y := by
              convert (hasDerivAt_const y (1 : ℝ)).sub (Real.hasDerivAt_cos y) using 1; ring
            exact hd2a.sub hd2b
          exact hd1.sub hd2
        rw [hd.deriv]
        exact h3 y (le_of_lt (by simpa [interior_Ici] using hy))
    simpa using hmono h0 hx hx
  exact ⟨h1 t ht, h2 t ht, h3 t ht, h4 t ht⟩

lemma abs_cos_sub_quadratic_le (t : ℝ) : |Real.cos t - (1 - t ^ 2 / 2)| ≤ t ^ 4 / 24 := by
  have h := trig_poly_bounds_nonneg (abs_nonneg t)
  rw [Real.cos_abs, sq_abs] at h
  have h4 : |t| ^ 4 = t ^ 4 := by
    have : |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
    rw [this, sq_abs]; ring
  rw [h4] at h
  rw [abs_le]
  constructor <;> linarith [h.2.1, h.2.2.2]

lemma abs_sin_sub_self_le (t : ℝ) : |Real.sin t - t| ≤ |t| ^ 3 / 6 := by
  rcases le_total 0 t with ht | ht
  · have h := trig_poly_bounds_nonneg ht
    rw [abs_of_nonneg ht, abs_le]
    constructor <;> linarith [h.1, h.2.2.1]
  · have h := trig_poly_bounds_nonneg (neg_nonneg.mpr ht)
    rw [Real.sin_neg] at h
    rw [abs_of_nonpos ht, abs_le]
    constructor <;> linarith [h.1, h.2.2.1]

lemma norm_exp_I_mul_sub_quadratic_le (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - (1 + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2)‖ ≤
      t ^ 4 / 24 + |t| ^ 3 / 6 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hrew : (↑(Real.cos t) + ↑(Real.sin t) * Complex.I) -
      (1 + ↑t * Complex.I - (↑t : ℂ) ^ 2 / 2) =
      ((Real.cos t - (1 - t ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin t - t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrew]
  calc ‖((Real.cos t - (1 - t ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin t - t : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((Real.cos t - (1 - t ^ 2 / 2) : ℝ) : ℂ)‖ + ‖((Real.sin t - t : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |Real.cos t - (1 - t ^ 2 / 2)| + |Real.sin t - t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ t ^ 4 / 24 + |t| ^ 3 / 6 := add_le_add (abs_cos_sub_quadratic_le t) (abs_sin_sub_self_le t)

lemma finset_sum_measure_apply {ι : Type*} (s : Finset ι) (μ : ι → MeasureTheory.Measure ℝ) (A : Set ℝ) :
    (∑ i ∈ s, μ i) A = ∑ i ∈ s, μ i A := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, FunLike.coe_add, Pi.add_apply, ih]

noncomputable def binomMeasure (n : ℕ) (p : ℝ) : MeasureTheory.Measure ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    ENNReal.ofReal (binomProb n p m) •
      MeasureTheory.Measure.dirac (((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p))

lemma binomMeasure_apply (n : ℕ) (p : ℝ) (s : Set ℝ) :
    binomMeasure n p s =
      ∑ m ∈ Finset.range (n + 1),
        ENNReal.ofReal (binomProb n p m) *
          MeasureTheory.Measure.dirac (((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p)) s := by
  unfold binomMeasure
  rw [finset_sum_measure_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [smul_eq_mul]

lemma binomMeasure_isProb {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (binomMeasure n p) := by
  refine ⟨?_⟩
  rw [binomMeasure_apply]
  have h1 : ∀ m ∈ Finset.range (n + 1),
      ENNReal.ofReal (binomProb n p m) *
        MeasureTheory.Measure.dirac (((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p)) Set.univ =
      ENNReal.ofReal (binomProb n p m) := by
    intro m _
    simp
  rw [Finset.sum_congr rfl h1, ← ENNReal.ofReal_sum_of_nonneg (fun m _ => binomProb_nonneg hp0 hp1 m),
    sum_binomProb, ENNReal.ofReal_one]

lemma binomMeasure_Iic_toReal {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : ℝ) :
    (binomMeasure n p (Set.Iic y)).toReal =
      ∑ m ∈ (Finset.range (n + 1)).filter
        (fun m : ℕ => ((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p) ≤ y), binomProb n p m := by
  rw [binomMeasure_apply, Finset.sum_filter]
  have h1 : ∀ m ∈ Finset.range (n + 1),
      ENNReal.ofReal (binomProb n p m) *
        MeasureTheory.Measure.dirac (((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p)) (Set.Iic y) =
      ENNReal.ofReal (if ((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p) ≤ y then binomProb n p m else 0) := by
    intro m _
    rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_apply]
    by_cases h : ((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p) ≤ y
    · simp only [Set.mem_Iic, ite_eq_left h, Pi.one_apply, mul_one]
    · simp only [Set.mem_Iic, ite_eq_right h, mul_zero, ENNReal.ofReal_zero]
  have hnn : ∀ m ∈ Finset.range (n + 1),
      0 ≤ (if ((m : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p) ≤ y then binomProb n p m else 0) := by
    intro m _
    split_ifs
    · exact binomProb_nonneg hp0 hp1 m
    · exact le_rfl
  rw [Finset.sum_congr rfl h1, ← ENNReal.ofReal_sum_of_nonneg hnn,
    ENNReal.toReal_ofReal (Finset.sum_nonneg hnn)]

lemma integral_finset_sum_smul_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (a : ι → ℝ) (f : ℝ → ℂ) (hf : Continuous f) (hbd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∫ x, f x ∂(∑ i ∈ s, ENNReal.ofReal (w i) • MeasureTheory.Measure.dirac (a i)) =
      ∑ i ∈ s, (w i : ℂ) * f (a i) := by
  obtain ⟨C, hC⟩ := hbd
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hfin1 : MeasureTheory.IsFiniteMeasure (ENNReal.ofReal (w j) • MeasureTheory.Measure.dirac (a j)) := by
      refine ⟨?_⟩
      simp [smul_eq_mul]
    have hfin2 : MeasureTheory.IsFiniteMeasure (∑ i ∈ s, ENNReal.ofReal (w i) • MeasureTheory.Measure.dirac (a i)) := by
      refine ⟨?_⟩
      rw [finset_sum_measure_apply]
      exact ENNReal.sum_lt_top.mpr fun i _ => by simp [smul_eq_mul]
    have hint1 : MeasureTheory.Integrable f (ENNReal.ofReal (w j) • MeasureTheory.Measure.dirac (a j)) :=
      MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    have hint2 : MeasureTheory.Integrable f (∑ i ∈ s, ENNReal.ofReal (w i) • MeasureTheory.Measure.dirac (a i)) :=
      MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    rw [MeasureTheory.integral_add_measure hint1 hint2, MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_dirac, ENNReal.toReal_ofReal (hw j (Finset.mem_insert_self j s)),
      Complex.real_smul, ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))]

lemma charFun_binomMeasure {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hn : 0 < n) (ξ : ℝ) :
    MeasureTheory.charFun (binomMeasure n p) ξ =
      (((1 - p : ℝ) : ℂ) * Complex.exp (((-p * (ξ / Real.sqrt ((n : ℝ) * p)) : ℝ) : ℂ) * Complex.I) +
       ((p : ℝ) : ℂ) * Complex.exp ((((1 - p) * (ξ / Real.sqrt ((n : ℝ) * p)) : ℝ) : ℂ) * Complex.I)) ^ n := by
  rw [MeasureTheory.charFun_apply_real]
  set mu : ℝ := (n : ℝ) * p
  set u : ℝ := ξ / Real.sqrt mu
  have hmu_pos : 0 < mu := mul_pos (Nat.cast_pos.mpr hn) hp0
  have hsq_pos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu_pos
  have hf_cont : Continuous (fun x : ℝ => Complex.exp ((ξ * x : ℝ) * Complex.I)) := by
    fun_prop
  have hf_bd : ∃ C, ∀ x : ℝ, ‖Complex.exp ((ξ * x : ℝ) * Complex.I)‖ ≤ C :=
    ⟨1, fun x => by rw [Complex.norm_exp_ofReal_mul_I]⟩
  have hint := integral_finset_sum_smul_dirac (Finset.range (n + 1)) (binomProb n p)
    (fun m _ => binomProb_nonneg (le_of_lt hp0) hp1 m)
    (fun m => ((m : ℝ) - mu) / Real.sqrt mu)
    (fun x => Complex.exp ((ξ * x : ℝ) * Complex.I)) hf_cont hf_bd
  have heq_int : ∫ x, Complex.exp ((ξ * x : ℂ) * Complex.I) ∂binomMeasure n p =
      ∑ m ∈ Finset.range (n + 1), (binomProb n p m : ℂ) *
        Complex.exp (((ξ * (((m : ℝ) - mu) / Real.sqrt mu) : ℝ) : ℂ) * Complex.I) := by
    have hfun : (fun x : ℝ => Complex.exp ((ξ * x : ℂ) * Complex.I)) =
        (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by
      funext x; push_cast; rfl
    rw [hfun]
    exact hint
  rw [heq_int]
  set a : ℂ := ((p : ℝ) : ℂ) * Complex.exp ((((1 - p) * u : ℝ) : ℂ) * Complex.I)
  set b : ℂ := ((1 - p : ℝ) : ℂ) * Complex.exp (((-p * u : ℝ) : ℂ) * Complex.I)
  rw [add_comm b a, add_pow a b n]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  unfold binomProb
  simp only [a, b, mul_pow, ← Complex.exp_nat_mul]
  have hexp : ((m : ℂ) * ((((1 - p) * u : ℝ) : ℂ) * Complex.I)) +
      (((n - m : ℕ) : ℂ) * (((-p * u : ℝ) : ℂ) * Complex.I)) =
      (((ξ * (((m : ℝ) - mu) / Real.sqrt mu) : ℝ) : ℂ) * Complex.I) := by
    have hreal : (m : ℝ) * ((1 - p) * u) + ((n - m : ℕ) : ℝ) * (-p * u) =
        ξ * (((m : ℝ) - mu) / Real.sqrt mu) := by
      rw [Nat.cast_sub hmn]
      simp only [u, mu]
      field_simp [ne_of_gt hsq_pos]
      ring
    have := congrArg (fun r : ℝ => (r : ℂ) * Complex.I) hreal
    push_cast at this ⊢
    linear_combination this
  rw [show ((((Nat.choose n m : ℝ) * p ^ m * (1 - p) ^ (n - m) : ℝ) : ℂ)) =
      ((p : ℝ) : ℂ) ^ m * ((1 - p : ℝ) : ℂ) ^ (n - m) * (Nat.choose n m : ℂ) by push_cast; ring]
  calc ((p : ℝ) : ℂ) ^ m * ((1 - p : ℝ) : ℂ) ^ (n - m) * (Nat.choose n m : ℂ) *
        Complex.exp (((ξ * (((m : ℝ) - mu) / Real.sqrt mu) : ℝ) : ℂ) * Complex.I)
      = ((p : ℝ) : ℂ) ^ m * ((1 - p : ℝ) : ℂ) ^ (n - m) * (Nat.choose n m : ℂ) *
        (Complex.exp ((m : ℂ) * ((((1 - p) * u : ℝ) : ℂ) * Complex.I)) *
         Complex.exp (((n - m : ℕ) : ℂ) * (((-p * u : ℝ) : ℂ) * Complex.I))) := by
        rw [← Complex.exp_add, hexp]
    _ = ((p : ℝ) : ℂ) ^ m * Complex.exp ((m : ℂ) * ((((1 - p) * u : ℝ) : ℂ) * Complex.I)) *
        (((1 - p : ℝ) : ℂ) ^ (n - m) * Complex.exp (((n - m : ℕ) : ℂ) * (((-p * u : ℝ) : ℂ) * Complex.I))) *
        (Nat.choose n m : ℂ) := by ring

lemma tendsto_pow_of_mul_sub_one_tendsto {n : ℕ → ℕ} {w : ℕ → ℂ} {c : ℂ}
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hw : Filter.Tendsto (fun k => (n k : ℂ) * (w k - 1)) Filter.atTop (nhds c)) :
    Filter.Tendsto (fun k => w k ^ n k) Filter.atTop (nhds (Complex.exp c)) := by
  have hn_real : Filter.Tendsto (fun k => (n k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hinv : Filter.Tendsto (fun k => ((n k : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun k => ‖((n k : ℂ))⁻¹‖) = (fun k => ((n k : ℝ))⁻¹) := by
      funext k
      rw [norm_inv, Complex.norm_natCast]
    rw [hnorm]
    exact tendsto_inv_atTop_zero.comp hn_real
  have hw_sub : Filter.Tendsto (fun k => w k - 1) Filter.atTop (nhds 0) := by
    have hprod := hinv.mul hw
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [hn.eventually (Filter.eventually_ge_atTop 1)] with k hk
    have hne : (n k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hne]
  have hw_one : Filter.Tendsto w Filter.atTop (nhds 1) := by
    simpa using hw_sub.add (tendsto_const_nhds (x := (1 : ℂ)))
  have hlog_deriv : HasDerivAt Complex.log 1 1 := by
    simpa using Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)
  have hlog_slope : Filter.Tendsto (slope Complex.log 1) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) :=
    hlog_deriv.tendsto_slope
  have hlog_ratio : Filter.Tendsto (fun k => (n k : ℂ) * Complex.log (w k)) Filter.atTop (nhds c) := by
    have hq : Filter.Tendsto (fun k => if w k = 1 then (1 : ℂ) else Complex.log (w k) / (w k - 1))
        Filter.atTop (nhds 1) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hmem : {z : ℂ | dist (slope Complex.log 1 z) 1 < ε} ∈ nhdsWithin 1 {(1 : ℂ)}ᶜ :=
        hlog_slope (Metric.ball_mem_nhds 1 hε)
      obtain ⟨δ, hδ, hδspec⟩ := Metric.mem_nhdsWithin_iff.mp hmem
      filter_upwards [Metric.tendsto_nhds.mp hw_one δ hδ] with k hk
      by_cases h1 : w k = 1
      · simp [h1, hε]
      · rw [ite_eq_right h1]
        have hmem_compl : w k ∈ Metric.ball (1 : ℂ) δ ∩ {(1 : ℂ)}ᶜ := ⟨hk, by simp [h1]⟩
        have hval := hδspec hmem_compl
        simpa [slope_def_field, Complex.log_one] using hval
    have hmul := hq.mul hw
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards with k
    by_cases h1 : w k = 1
    · simp [h1, Complex.log_one]
    · rw [ite_eq_right h1]
      have hne : w k - 1 ≠ 0 := sub_ne_zero.mpr h1
      field_simp [hne]
  have hexp := (Complex.continuous_exp.tendsto c).comp hlog_ratio
  refine hexp.congr' ?_
  filter_upwards [Metric.tendsto_nhds.mp hw_one (1 / 2) (by norm_num)] with k hk
  have hwne : w k ≠ 0 := by
    intro h0
    rw [h0, dist_zero_left, norm_one] at hk
    linarith
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log hwne]

lemma tendsto_binom_tail_gaussian {n : ℕ → ℕ} {p : ℕ → ℝ}
    (hp0 : ∀ᶠ k in Filter.atTop, 0 < p k)
    (hp1 : ∀ᶠ k in Filter.atTop, p k < 1)
    (hp_zero : Filter.Tendsto p Filter.atTop (nhds 0))
    (hmu_top : Filter.Tendsto (fun k => (n k : ℝ) * p k) Filter.atTop Filter.atTop)
    (y : ℝ) :
    Filter.Tendsto
      (fun k => ∑ m ∈ (Finset.range (n k + 1)).filter
        (fun m : ℕ => ((m : ℝ) - (n k : ℝ) * p k) / Real.sqrt ((n k : ℝ) * p k) ≤ y),
        binomProb (n k) (p k) m)
      Filter.atTop
      (nhds (((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal)) := by
  have hn_top : Filter.Tendsto n Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop] at hmu_top ⊢
    intro B
    obtain ⟨K1, hK1⟩ := hmu_top (B : ℝ)
    obtain ⟨K2, hK2⟩ := Filter.eventually_atTop.mp hp1
    refine ⟨max K1 K2, fun k hk => ?_⟩
    have h1 := hK1 k (le_trans (le_max_left _ _) hk)
    have h2 := hK2 k (le_trans (le_max_right _ _) hk)
    have hle : (B : ℝ) ≤ (n k : ℝ) := by
      have : (n k : ℝ) * p k ≤ (n k : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt h2) (Nat.cast_nonneg _)
      linarith
    exact_mod_cast hle
  let ν : ℕ → MeasureTheory.ProbabilityMeasure ℝ := fun k =>
    if h : 0 ≤ p k ∧ p k ≤ 1 then
      ⟨binomMeasure (n k) (p k), binomMeasure_isProb h.1 h.2⟩
    else
      ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  let ν₀ : MeasureTheory.ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  have hchar : ∀ ξ : ℝ, Filter.Tendsto (fun k => MeasureTheory.charFun (ν k : MeasureTheory.Measure ℝ) ξ)
      Filter.atTop (nhds (MeasureTheory.charFun (ν₀ : MeasureTheory.Measure ℝ) ξ)) := by
    intro ξ
    have hgauss : MeasureTheory.charFun (ν₀ : MeasureTheory.Measure ℝ) ξ =
        Complex.exp (-((ξ : ℂ) ^ 2 / 2)) := by
      simp only [ν₀, MeasureTheory.ProbabilityMeasure.coe_mk, ProbabilityTheory.charFun_gaussianReal]
      congr 1
      push_cast
      ring
    rw [hgauss]
    let w : ℕ → ℂ := fun k =>
      ((1 - p k : ℝ) : ℂ) * Complex.exp (((-p k * (ξ / Real.sqrt ((n k : ℝ) * p k)) : ℝ) : ℂ) * Complex.I) +
      ((p k : ℝ) : ℂ) * Complex.exp ((((1 - p k) * (ξ / Real.sqrt ((n k : ℝ) * p k)) : ℝ) : ℂ) * Complex.I)
    have hwn : Filter.Tendsto (fun k => w k ^ n k) Filter.atTop (nhds (Complex.exp (-((ξ : ℂ) ^ 2 / 2)))) := by
      apply tendsto_pow_of_mul_sub_one_tendsto hn_top
      have hdiff_zero : Filter.Tendsto
          (fun k => (n k : ℂ) * (w k - 1) - (-((ξ : ℂ) ^ 2 / 2))) Filter.atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hbound_zero : Filter.Tendsto
            (fun k => p k * (ξ ^ 2 / 2) +
              (ξ ^ 4 / (24 * ((n k : ℝ) * p k)) + |ξ| ^ 3 / (6 * Real.sqrt ((n k : ℝ) * p k))))
            Filter.atTop (nhds 0) := by
          have ht1 : Filter.Tendsto (fun k => p k * (ξ ^ 2 / 2)) Filter.atTop (nhds 0) := by
            simpa using hp_zero.mul_const (ξ ^ 2 / 2)
          have hinv_mu : Filter.Tendsto (fun k => ((n k : ℝ) * p k)⁻¹) Filter.atTop (nhds 0) :=
            tendsto_inv_atTop_zero.comp hmu_top
          have hsqrt_top : Filter.Tendsto (fun k => Real.sqrt ((n k : ℝ) * p k)) Filter.atTop Filter.atTop :=
            Real.tendsto_sqrt_atTop.comp hmu_top
          have hinv_sqrt : Filter.Tendsto (fun k => (Real.sqrt ((n k : ℝ) * p k))⁻¹) Filter.atTop (nhds 0) :=
            tendsto_inv_atTop_zero.comp hsqrt_top
          have ht2 : Filter.Tendsto (fun k => ξ ^ 4 / (24 * ((n k : ℝ) * p k))) Filter.atTop (nhds 0) := by
            have : (fun k => ξ ^ 4 / (24 * ((n k : ℝ) * p k))) =
                (fun k => (ξ ^ 4 / 24) * ((n k : ℝ) * p k)⁻¹) := by funext k; ring
            rw [this]
            simpa using hinv_mu.const_mul (ξ ^ 4 / 24)
          have ht3 : Filter.Tendsto (fun k => |ξ| ^ 3 / (6 * Real.sqrt ((n k : ℝ) * p k))) Filter.atTop (nhds 0) := by
            have : (fun k => |ξ| ^ 3 / (6 * Real.sqrt ((n k : ℝ) * p k))) =
                (fun k => (|ξ| ^ 3 / 6) * (Real.sqrt ((n k : ℝ) * p k))⁻¹) := by funext k; ring
            rw [this]
            simpa using hinv_sqrt.const_mul (|ξ| ^ 3 / 6)
          simpa using ht1.add (ht2.add ht3)
        refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hbound_zero
        filter_upwards [hp0, hp1, hmu_top.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
          hn_top.eventually (Filter.eventually_ge_atTop 1)] with k hpk0 hpk1 hmuk hnk
        set pk := p k
        set nk := (n k : ℝ)
        set mu := nk * pk
        set u := ξ / Real.sqrt mu
        have hmu_pos : 0 < mu := by linarith
        have hsq_pos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu_pos
        have hsq_sq : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt (le_of_lt hmu_pos)
        set t1 : ℝ := -pk * u
        set t2 : ℝ := (1 - pk) * u
        set r1 : ℂ := Complex.exp ((t1 : ℂ) * Complex.I) - (1 + (t1 : ℂ) * Complex.I - (t1 : ℂ) ^ 2 / 2)
        set r2 : ℂ := Complex.exp ((t2 : ℂ) * Complex.I) - (1 + (t2 : ℂ) * Complex.I - (t2 : ℂ) ^ 2 / 2)
        have hw_decomp : (n k : ℂ) * (w k - 1) - (-((ξ : ℂ) ^ 2 / 2)) =
            ((pk * (ξ ^ 2 / 2) : ℝ) : ℂ) +
              (n k : ℂ) * (((1 - pk : ℝ) : ℂ) * r1 + ((pk : ℝ) : ℂ) * r2) := by
          have hq : (nk : ℝ) * (-(1 - pk) * t1 ^ 2 / 2 - pk * t2 ^ 2 / 2) + ξ ^ 2 / 2 =
              pk * (ξ ^ 2 / 2) := by
            simp only [t1, t2, u]
            rw [mul_pow, mul_pow, div_pow, hsq_sq]
            have hmu_ne : mu ≠ 0 := ne_of_gt hmu_pos
            field_simp [hmu_ne]
            have : nk * pk = mu := rfl
            nlinarith
          have hqC : (n k : ℂ) * (-((1 - pk : ℝ) : ℂ) * (t1 : ℂ) ^ 2 / 2 - ((pk : ℝ) : ℂ) * (t2 : ℂ) ^ 2 / 2) +
              (ξ : ℂ) ^ 2 / 2 = ((pk * (ξ ^ 2 / 2) : ℝ) : ℂ) := by
            exact_mod_cast hq
          have hlin : ((1 - pk : ℝ) : ℂ) * (t1 : ℂ) + ((pk : ℝ) : ℂ) * (t2 : ℂ) = 0 := by
            simp only [t1, t2]; push_cast; ring
          have hw_eq : w k = ((1 - pk : ℝ) : ℂ) * Complex.exp ((t1 : ℂ) * Complex.I) +
              ((pk : ℝ) : ℂ) * Complex.exp ((t2 : ℂ) * Complex.I) := rfl
          have h1mp_c : ((1 - pk : ℝ) : ℂ) = 1 - ((pk : ℝ) : ℂ) := by push_cast; ring
          rw [hw_eq]
          simp only [r1, r2, h1mp_c] at hqC hlin ⊢
          linear_combination hqC + (n k : ℂ) * Complex.I * hlin
        rw [hw_decomp]
        have hr1 : ‖r1‖ ≤ t1 ^ 4 / 24 + |t1| ^ 3 / 6 := norm_exp_I_mul_sub_quadratic_le t1
        have hr2 : ‖r2‖ ≤ t2 ^ 4 / 24 + |t2| ^ 3 / 6 := norm_exp_I_mul_sub_quadratic_le t2
        have h1mp : 0 ≤ 1 - pk := by linarith
        have h1mp_le : 1 - pk ≤ 1 := by linarith
        have hpk_le : pk ≤ 1 := le_of_lt hpk1
        have ht1_abs : |t1| = pk * |u| := by
          simp only [t1, abs_mul, abs_neg, abs_of_pos hpk0]
        have ht2_abs : |t2| = (1 - pk) * |u| := by
          simp only [t2, abs_mul, abs_of_nonneg h1mp]
        have hrem_comb : (1 - pk) * (t1 ^ 4 / 24 + |t1| ^ 3 / 6) +
            pk * (t2 ^ 4 / 24 + |t2| ^ 3 / 6) ≤ pk * (u ^ 4 / 24 + |u| ^ 3 / 6) := by
          have ht1_4 : t1 ^ 4 = pk ^ 4 * u ^ 4 := by simp only [t1]; ring
          have ht2_4 : t2 ^ 4 = (1 - pk) ^ 4 * u ^ 4 := by simp only [t2]; ring
          have hpow4 : (1 - pk) * pk ^ 4 + pk * (1 - pk) ^ 4 ≤ pk := by
            have ha : pk ^ 3 ≤ pk := by
              have : pk ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hpk0) hpk_le
              nlinarith
            have hb : (1 - pk) ^ 4 ≤ 1 - pk := by
              have : (1 - pk) ^ 3 ≤ 1 := pow_le_one₀ h1mp h1mp_le
              nlinarith
            have hc : (1 - pk) * pk ^ 3 ≤ pk := by nlinarith
            have hd : (1 - pk) * pk ^ 3 + (1 - pk) ^ 4 ≤ 1 := by linarith
            nlinarith
          have hpow3 : (1 - pk) * pk ^ 3 + pk * (1 - pk) ^ 3 ≤ pk := by
            have ha : pk ^ 2 ≤ pk := by nlinarith
            have hb : (1 - pk) ^ 3 ≤ 1 - pk := by
              have : (1 - pk) ^ 2 ≤ 1 := pow_le_one₀ h1mp h1mp_le
              nlinarith
            have hc : (1 - pk) * pk ^ 2 ≤ pk := by nlinarith
            have hd : (1 - pk) * pk ^ 2 + (1 - pk) ^ 3 ≤ 1 := by linarith
            nlinarith
          rw [ht1_4, ht2_4, ht1_abs, ht2_abs, mul_pow, mul_pow]
          have hu4_nn : 0 ≤ u ^ 4 / 24 := by positivity
          have hu3_nn : 0 ≤ |u| ^ 3 / 6 := by positivity
          nlinarith
        have hnk_rem : nk * (pk * (u ^ 4 / 24 + |u| ^ 3 / 6)) =
            ξ ^ 4 / (24 * mu) + |ξ| ^ 3 / (6 * Real.sqrt mu) := by
          have hu4 : u ^ 4 = ξ ^ 4 / mu ^ 2 := by
            simp only [u]
            rw [div_pow]
            have : Real.sqrt mu ^ 4 = mu ^ 2 := by
              calc Real.sqrt mu ^ 4 = (Real.sqrt mu ^ 2) ^ 2 := by ring
                _ = mu ^ 2 := by rw [hsq_sq]
            rw [this]
          have hu3 : |u| ^ 3 = |ξ| ^ 3 / (mu * Real.sqrt mu) := by
            simp only [u, abs_div, abs_of_pos hsq_pos, div_pow]
            have : Real.sqrt mu ^ 3 = mu * Real.sqrt mu := by
              calc Real.sqrt mu ^ 3 = Real.sqrt mu ^ 2 * Real.sqrt mu := by ring
                _ = mu * Real.sqrt mu := by rw [hsq_sq]
            rw [this]
          rw [hu4, hu3]
          have hmu_ne : mu ≠ 0 := ne_of_gt hmu_pos
          have hsq_ne : Real.sqrt mu ≠ 0 := ne_of_gt hsq_pos
          have hnkpk : nk * pk = mu := rfl
          calc nk * (pk * (ξ ^ 4 / mu ^ 2 / 24 + |ξ| ^ 3 / (mu * Real.sqrt mu) / 6))
              = mu * (ξ ^ 4 / mu ^ 2 / 24 + |ξ| ^ 3 / (mu * Real.sqrt mu) / 6) := by
                  rw [← mul_assoc, hnkpk]
            _ = ξ ^ 4 / (24 * mu) + |ξ| ^ 3 / (6 * Real.sqrt mu) := by
                  field_simp [hmu_ne, hsq_ne]
        calc ‖((pk * (ξ ^ 2 / 2) : ℝ) : ℂ) + (n k : ℂ) * (((1 - pk : ℝ) : ℂ) * r1 + ((pk : ℝ) : ℂ) * r2)‖
            ≤ ‖((pk * (ξ ^ 2 / 2) : ℝ) : ℂ)‖ + ‖(n k : ℂ) * (((1 - pk : ℝ) : ℂ) * r1 + ((pk : ℝ) : ℂ) * r2)‖ :=
              norm_add_le _ _
          _ ≤ pk * (ξ ^ 2 / 2) + nk * ((1 - pk) * ‖r1‖ + pk * ‖r2‖) := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
                norm_mul, Complex.norm_natCast]
              gcongr
              calc ‖((1 - pk : ℝ) : ℂ) * r1 + ((pk : ℝ) : ℂ) * r2‖
                  ≤ ‖((1 - pk : ℝ) : ℂ) * r1‖ + ‖((pk : ℝ) : ℂ) * r2‖ := norm_add_le _ _
                _ = (1 - pk) * ‖r1‖ + pk * ‖r2‖ := by
                    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1mp, abs_of_pos hpk0]
          _ ≤ pk * (ξ ^ 2 / 2) + nk * ((1 - pk) * (t1 ^ 4 / 24 + |t1| ^ 3 / 6) +
                pk * (t2 ^ 4 / 24 + |t2| ^ 3 / 6)) := by
              gcongr
          _ ≤ pk * (ξ ^ 2 / 2) + nk * (pk * (u ^ 4 / 24 + |u| ^ 3 / 6)) := by
              gcongr
          _ = pk * (ξ ^ 2 / 2) + (ξ ^ 4 / (24 * mu) + |ξ| ^ 3 / (6 * Real.sqrt mu)) := by
              rw [hnk_rem]
      have hadd := hdiff_zero.add (tendsto_const_nhds (x := -((ξ : ℂ) ^ 2 / 2)))
      simpa only [zero_add, sub_add_cancel] using hadd
    refine hwn.congr' ?_
    filter_upwards [hp0, hp1, hn_top.eventually (Filter.eventually_ge_atTop 1)] with k hpk0 hpk1 hnk
    have hcond : 0 ≤ p k ∧ p k ≤ 1 := ⟨le_of_lt hpk0, le_of_lt hpk1⟩
    have hνk : (ν k : MeasureTheory.Measure ℝ) = binomMeasure (n k) (p k) := by
      change (↑(if h : 0 ≤ p k ∧ p k ≤ 1 then
        (⟨binomMeasure (n k) (p k), binomMeasure_isProb h.1 h.2⟩ : MeasureTheory.ProbabilityMeasure ℝ)
        else ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩) : MeasureTheory.Measure ℝ) = _
      rw [dite_eq_left hcond]
    rw [hνk]
    exact (charFun_binomMeasure hpk0 (le_of_lt hpk1) hnk ξ).symm
  have hconv : Filter.Tendsto ν Filter.atTop (nhds ν₀) :=
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun).mpr hchar
  have hfront : ν₀ (frontier (Set.Iic y)) = 0 := by
    have hsub : frontier (Set.Iic y) ⊆ {y} := frontier_Iic_subset y
    have hsing : ProbabilityTheory.gaussianReal 0 1 {y} = 0 := by
      rw [ProbabilityTheory.gaussianReal_apply 0 one_ne_zero]
      simp
    have hzero : (ν₀ : MeasureTheory.Measure ℝ) (frontier (Set.Iic y)) = 0 :=
      MeasureTheory.measure_mono_null hsub hsing
    rw [MeasureTheory.ProbabilityMeasure.coeFn_def]
    dsimp only
    rw [hzero]
    simp
  have hport := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hconv hfront
  have hreal : Filter.Tendsto (fun k => ((ν k (Set.Iic y) : NNReal) : ℝ))
      Filter.atTop (nhds (((ν₀ (Set.Iic y) : NNReal) : ℝ))) :=
    (NNReal.continuous_coe.tendsto _).comp hport
  have hlim_eq : ((ν₀ (Set.Iic y) : NNReal) : ℝ) = ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal := by
    simp [ν₀, ENNReal.coe_toNNReal_eq_toReal]
  rw [hlim_eq] at hreal
  refine hreal.congr' ?_
  filter_upwards [hp0, hp1] with k hpk0 hpk1
  have hcond : 0 ≤ p k ∧ p k ≤ 1 := ⟨le_of_lt hpk0, le_of_lt hpk1⟩
  have hνk : (ν k : MeasureTheory.Measure ℝ) = binomMeasure (n k) (p k) := by
    change (↑(if h : 0 ≤ p k ∧ p k ≤ 1 then
      (⟨binomMeasure (n k) (p k), binomMeasure_isProb h.1 h.2⟩ : MeasureTheory.ProbabilityMeasure ℝ)
      else ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩) : MeasureTheory.Measure ℝ) = _
    rw [dite_eq_left hcond]
  rw [MeasureTheory.ProbabilityMeasure.coeFn_def]
  dsimp only
  rw [hνk, ENNReal.coe_toNNReal_eq_toReal]
  exact binomMeasure_Iic_toReal hcond.1 hcond.2 y

def defectsSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i ∈ S ↔ nextIdx i ∈ S)

def startsSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i ∉ S ∧ nextIdx i ∈ S)

def nextIdx_equiv (n : ℕ) : Fin n ≃ Fin n :=
  { toFun := nextIdx
    invFun := prevIdx
    left_inv := prevIdx_nextIdx
    right_inv := nextIdx_prevIdx }

lemma startsSet_card_eq_endsSet_card {n : ℕ} (S : Finset (Fin n)) :
    (startsSet S).card = runsCard S := by
  have hsum_zero : ∑ i : Fin n,
      ((if i ∈ S then (1 : ℤ) else 0) - (if nextIdx i ∈ S then (1 : ℤ) else 0)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have heq : ∑ i : Fin n, (if nextIdx i ∈ S then (1 : ℤ) else 0) =
        ∑ i : Fin n, (if i ∈ S then (1 : ℤ) else 0) :=
      Fintype.sum_equiv (nextIdx_equiv n) _ _ (fun _ => rfl)
    rw [heq, sub_self]
  have hsum_split : ∑ i : Fin n,
      ((if i ∈ S then (1 : ℤ) else 0) - (if nextIdx i ∈ S then (1 : ℤ) else 0)) =
      (endsSet S).card - (startsSet S).card := by
    have hterm : ∀ i : Fin n,
        ((if i ∈ S then (1 : ℤ) else 0) - (if nextIdx i ∈ S then (1 : ℤ) else 0)) =
        (if i ∈ endsSet S then (1 : ℤ) else 0) - (if i ∈ startsSet S then (1 : ℤ) else 0) := by
      intro i
      simp only [endsSet, startsSet, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : i ∈ S <;> by_cases h2 : nextIdx i ∈ S <;> simp [h1, h2]
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_boole]
    simp
  have hZ : ((endsSet S).card : ℤ) = ((startsSet S).card : ℤ) := by linarith
  exact (Int.ofNat.inj hZ).symm

lemma defects_card_add_two_runs {n : ℕ} (S : Finset (Fin n)) :
    (defectsSet S).card + 2 * runsCard S = n := by
  have hdisj1 : Disjoint (defectsSet S) (endsSet S) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := Finset.mem_filter.mp h2
    exact b.2 (a.mp b.1)
  have hdisj2 : Disjoint (defectsSet S ∪ endsSet S) (startsSet S) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have c := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with ha | hb
    · exact c.1 ((Finset.mem_filter.mp ha).2.mpr c.2)
    · exact c.1 (Finset.mem_filter.mp hb).1
  have hunion : defectsSet S ∪ endsSet S ∪ startsSet S = Finset.univ := by
    ext i
    simp only [Finset.mem_union, defectsSet, endsSet, startsSet, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    by_cases h1 : i ∈ S <;> by_cases h2 : nextIdx i ∈ S
    · left; left; exact ⟨fun _ => h2, fun _ => h1⟩
    · left; right; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
    · left; left; exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hcard : (defectsSet S).card + (endsSet S).card + (startsSet S).card = n := by
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      hunion, Finset.card_univ, Fintype.card_fin]
  have hs := startsSet_card_eq_endsSet_card S
  unfold runsCard at hs ⊢
  omega

lemma defects_card_even {n : ℕ} (hn : Even n) (S : Finset (Fin n)) :
    Even (defectsSet S).card := by
  have h := defects_card_add_two_runs S
  rcases hn with ⟨m, hm⟩
  refine ⟨m - runsCard S, ?_⟩
  omega

def reconstructSet {n : ℕ} (b : Bool) (D : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n =>
    xor b (decide (Odd ((Finset.range i.val).filter (fun j => ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ D)).card)))

lemma reconstructSet_defects {n : ℕ} (hn : Even n) (D : Finset (Fin n)) (hD : Even D.card) (b : Bool) :
    defectsSet (reconstructSet b D) = D := by
  ext i
  simp only [defectsSet, Finset.mem_filter, Finset.mem_univ, true_and]
  let P : ℕ → Prop := fun j => ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ D
  let c : ℕ → ℕ := fun k => ((Finset.range k).filter P).card
  have hc_succ : ∀ (k : ℕ) (hk : k < n), c (k + 1) = c k + if (⟨k, hk⟩ : Fin n) ∉ D then 1 else 0 := by
    intro k hk
    simp only [c, Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter P := by simp
    by_cases hPk : (⟨k, hk⟩ : Fin n) ∉ D
    · have hP : P k := ⟨hk, hPk⟩
      rw [ite_eq_left hP, ite_eq_left hPk, Finset.card_insert_of_notMem hnot]
    · have hP : ¬ P k := fun ⟨_, h⟩ => hPk h
      rw [ite_eq_right hP, ite_eq_right hPk, add_zero]
  have hcn : Even (c n) := by
    have hcard : c n = (Finset.univ.filter (fun j : Fin n => j ∉ D)).card := by
      refine Finset.card_bij (fun j hj => ⟨j, (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)⟩) ?_ ?_ ?_
      · intro j hj
        obtain ⟨_, hj', hnot⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      · intro a _ b _ h
        exact congrArg Fin.val h
      · intro j hj
        have hnot := (Finset.mem_filter.mp hj).2
        refine ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ⟨j.isLt, hnot⟩⟩, ?_⟩
        ext; rfl
    have hcomp : (Finset.univ.filter (fun j : Fin n => j ∉ D)).card + D.card = n := by
      have h1 : Finset.univ.filter (fun j : Fin n => j ∉ D) = Finset.univ \ D := by
        ext j; simp
      rw [h1, Finset.card_sdiff, Finset.inter_univ]
      have hle : D.card ≤ n := by simpa using Finset.card_le_univ D
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    rw [hcard]
    rcases hn with ⟨m, hm⟩
    rcases hD with ⟨k, hk⟩
    refine ⟨m - k, ?_⟩
    omega
  have hmem : ∀ u : Fin n, u ∈ reconstructSet b D ↔ (xor b (decide (Odd (c u.val))) = true) := by
    intro u
    simp [reconstructSet, c, P]
  rw [hmem i, hmem (nextIdx i)]
  have hxor : ∀ (x y : Bool), (xor b x = true ↔ xor b y = true) ↔ x = y := by
    intro x y; cases b <;> cases x <;> cases y <;> decide
  rw [hxor]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = n
  · have hni : (nextIdx i).val = 0 := by simp [nextIdx, hlast, Nat.mod_self]
    rw [hni]
    have hc0 : c 0 = 0 := by simp [c]
    rw [hc0]
    have hstep := hc_succ i.val hi
    rw [hlast] at hstep
    have hnot0 : ¬ Odd 0 := by decide
    simp only [decide_eq_false hnot0, decide_eq_false_iff_not]
    constructor
    · intro hnotOdd
      by_contra hnotD
      rw [ite_eq_left hnotD] at hstep
      have hodd : Odd (c n) := by
        rw [hstep]
        exact Even.add_one (Nat.not_odd_iff_even.mp hnotOdd)
      exact (Nat.not_odd_iff_even.mpr hcn) hodd
    · intro hiD hodd
      rw [ite_eq_right (not_not.mpr hiD), add_zero] at hstep
      rw [hstep] at hcn
      exact (Nat.not_odd_iff_even.mpr hcn) hodd
  · have hlt : i.val + 1 < n := by omega
    have hni : (nextIdx i).val = i.val + 1 := by simp [nextIdx, Nat.mod_eq_of_lt hlt]
    rw [hni]
    have hstep := hc_succ i.val hi
    by_cases hiD : i ∈ D
    · rw [ite_eq_right (not_not.mpr hiD), add_zero] at hstep
      simp [hstep, hiD]
    · rw [ite_eq_left hiD] at hstep
      have hne : decide (Odd (c i.val)) ≠ decide (Odd (c i.val + 1)) := by
        by_cases ho : Odd (c i.val)
        · have he : Even (c i.val + 1) := Odd.add_one ho
          simp [ho, Nat.not_odd_iff_even.mpr he]
        · have ho1 : Odd (c i.val + 1) := Even.add_one (Nat.not_odd_iff_even.mp ho)
          simp [ho, ho1]
      rw [hstep]
      exact ⟨fun h => False.elim (hne h), fun h => False.elim (hiD h)⟩

lemma eq_reconstructSet_of_defects {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    S = reconstructSet (decide ((⟨0, hn⟩ : Fin n) ∈ S)) (defectsSet S) := by
  let b := decide ((⟨0, hn⟩ : Fin n) ∈ S)
  let D := defectsSet S
  let P : ℕ → Prop := fun j => ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ D
  let c : ℕ → ℕ := fun k => ((Finset.range k).filter P).card
  have hwalk : ∀ k (hk : k < n),
      ((⟨k, hk⟩ : Fin n) ∈ S) ↔ (xor b (decide (Odd (c k))) = true) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hc0 : c 0 = 0 := by simp [c]
      rw [hc0]
      simp [b]
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hih := ih hk'
      have hnext : nextIdx (⟨k, hk'⟩ : Fin n) = ⟨k + 1, hk⟩ := by
        ext; simp [nextIdx, Nat.mod_eq_of_lt hk]
      have hc_succ : c (k + 1) = c k + if (⟨k, hk'⟩ : Fin n) ∉ D then 1 else 0 := by
        simp only [c, Finset.range_add_one, Finset.filter_insert]
        have hnot : k ∉ (Finset.range k).filter P := by simp
        by_cases hPk : (⟨k, hk'⟩ : Fin n) ∉ D
        · rw [ite_eq_left ⟨hk', hPk⟩, ite_eq_left hPk, Finset.card_insert_of_notMem hnot]
        · have hnp : ¬ P k := fun ⟨_, h⟩ => hPk h
          rw [ite_eq_right hnp, ite_eq_right hPk, add_zero]
      rw [hc_succ]
      by_cases hD : (⟨k, hk'⟩ : Fin n) ∈ D
      · have hiff : (⟨k, hk'⟩ : Fin n) ∈ S ↔ (⟨k + 1, hk⟩ : Fin n) ∈ S := by
          have := (Finset.mem_filter.mp hD).2
          rwa [hnext] at this
        rw [ite_eq_right (not_not.mpr hD), add_zero]
        exact hiff.symm.trans hih
      · have hiff : ¬ ((⟨k, hk'⟩ : Fin n) ∈ S ↔ (⟨k + 1, hk⟩ : Fin n) ∈ S) := by
          intro h
          apply hD
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rwa [hnext]
        rw [ite_eq_left hD]
        have hflip : ∀ x : Bool, xor b (!x) = !(xor b x) := by intro x; cases b <;> cases x <;> decide
        have hdec : decide (Odd (c k + 1)) = !(decide (Odd (c k))) := by
          by_cases ho : Odd (c k)
          · simp [ho, Nat.not_odd_iff_even.mpr (Odd.add_one ho)]
          · simp [ho, Even.add_one (Nat.not_odd_iff_even.mp ho)]
        rw [hdec, hflip]
        by_cases hx : xor b (decide (Odd (c k))) = true
        · have h1 : (⟨k, hk'⟩ : Fin n) ∈ S := hih.mpr hx
          have h2 : (⟨k + 1, hk⟩ : Fin n) ∉ S := fun h => hiff ⟨fun _ => h, fun _ => h1⟩
          simp [hx, h2]
        · have hxf : xor b (decide (Odd (c k))) = false := by
            cases hval : xor b (decide (Odd (c k))) <;> simp_all
          have h1 : (⟨k, hk'⟩ : Fin n) ∉ S := fun h => hx (hih.mp h)
          have h2 : (⟨k + 1, hk⟩ : Fin n) ∈ S := by
            by_contra h2
            exact hiff ⟨fun h => absurd h h1, fun h => absurd h h2⟩
          simp [hxf, h2]
  ext i
  simp only [reconstructSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hwalk i.val i.isLt

lemma sum_over_finset_eq_two_mul_even_defects {n : ℕ} (hn : 0 < n) (heven : Even n)
    (g : Finset (Fin n) → ℝ) :
    ∑ S : Finset (Fin n), g (defectsSet S) =
      2 * ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun D => Even D.card), g D := by
  let evenD := (Finset.univ : Finset (Finset (Fin n))).filter (fun D => Even D.card)
  let f : Bool × Finset (Fin n) → Finset (Fin n) := fun p => reconstructSet p.1 p.2
  have hbij : ∑ S : Finset (Fin n), g (defectsSet S) =
      ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ evenD, g (defectsSet (f p)) := by
    symm
    refine Finset.sum_nbij f ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro p₁ hp₁ p₂ hp₂ heq
      have hD1 : Even p₁.2.card := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).2).2
      have hD2 : Even p₂.2.card := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).2).2
      have h2 : p₁.2 = p₂.2 := by
        have := congrArg defectsSet heq
        rwa [reconstructSet_defects heven p₁.2 hD1 p₁.1,
          reconstructSet_defects heven p₂.2 hD2 p₂.1] at this
      have h1 : p₁.1 = p₂.1 := by
        have h0 : (⟨0, hn⟩ : Fin n) ∈ f p₁ ↔ (⟨0, hn⟩ : Fin n) ∈ f p₂ := by rw [heq]
        simp only [f, reconstructSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.range_zero, Finset.filter_empty, Finset.card_empty] at h0
        have hnot0 : ¬ Odd 0 := by decide
        simp only [decide_eq_false hnot0, Bool.xor_false] at h0
        cases hp1 : p₁.1 <;> cases hp2 : p₂.1 <;> simp_all
      exact Prod.ext h1 h2
    · intro S _
      refine ⟨(decide ((⟨0, hn⟩ : Fin n) ∈ S), defectsSet S), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, defects_card_even heven S⟩⟩
      · exact (eq_reconstructSet_of_defects hn S).symm
    · intro _ _; rfl
  rw [hbij]
  have hrew : ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ evenD, g (defectsSet (f p)) =
      ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ evenD, g p.2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hD : Even p.2.card := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    rw [reconstructSet_defects heven p.2 hD p.1]
  rw [hrew, Finset.sum_product]
  simp [two_mul, evenD]

lemma sum_bernoulli_subsets {n : ℕ} (p : ℝ) (Q : ℕ → Prop) :
    ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun D => Q D.card),
        p ^ D.card * (1 - p) ^ (n - D.card) =
      ∑ m ∈ (Finset.range (n + 1)).filter Q,
        (Nat.choose n m : ℝ) * p ^ m * (1 - p) ^ (n - m) := by
  have hpart : (Finset.univ : Finset (Finset (Fin n))).filter (fun D => Q D.card) =
      ((Finset.range (n + 1)).filter Q).biUnion
        (fun m => (Finset.univ : Finset (Fin n)).powersetCard m) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hQ
      refine ⟨D.card, ⟨Nat.lt_succ_of_le (by simpa using Finset.card_le_univ D), hQ⟩, rfl⟩
    · rintro ⟨m, ⟨_, hQ⟩, rfl⟩
      exact hQ
  rw [hpart, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hconst : ∑ D ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        p ^ D.card * (1 - p) ^ (n - D.card) =
        ∑ _D ∈ (Finset.univ : Finset (Fin n)).powersetCard m, p ^ m * (1 - p) ^ (n - m) :=
      Finset.sum_congr rfl fun D hD => by rw [(Finset.mem_powersetCard.mp hD).2]
    rw [hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  · intro m₁ _ m₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro D h1 h2
    exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)

def badDefects {n : ℕ} (D : Finset (Fin n)) : Prop :=
  ∃ i : Fin n, i ∈ D ∧ nextIdx i ∈ D

lemma sum_bernoulli_pair {n : ℕ} (hn : 2 ≤ n) (p : ℝ) (i : Fin n) :
    ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun D => i ∈ D ∧ nextIdx i ∈ D),
        p ^ D.card * (1 - p) ^ (n - D.card) = p ^ 2 := by
  have hne : i ≠ nextIdx i := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [nextIdx] at hv
    have hi := i.isLt
    by_cases hlast : i.val + 1 = n
    · rw [hlast, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
  let rest : Finset (Fin n) := Finset.univ \ {i, nextIdx i}
  have hrest_card : rest.card = n - 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_pair hne]
  have hbij : ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun D => i ∈ D ∧ nextIdx i ∈ D),
        p ^ D.card * (1 - p) ^ (n - D.card) =
      ∑ E ∈ rest.powerset, p ^ 2 * (p ^ E.card * (1 - p) ^ (rest.card - E.card)) := by
    refine Finset.sum_nbij (fun D => D \ {i, nextIdx i}) ?_ ?_ ?_ ?_
    · intro D _
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    · intro D₁ hD₁ D₂ hD₂ heq
      dsimp only at heq
      have h1 := (Finset.mem_filter.mp hD₁).2
      have h2 := (Finset.mem_filter.mp hD₂).2
      ext x
      by_cases hxi : x = i
      · subst hxi; simp [h1.1, h2.1]
      · by_cases hxn : x = nextIdx i
        · subst hxn; simp [h1.2, h2.2]
        · have hx1 : x ∈ D₁ \ {i, nextIdx i} ↔ x ∈ D₁ := by simp [hxi, hxn]
          have hx2 : x ∈ D₂ \ {i, nextIdx i} ↔ x ∈ D₂ := by simp [hxi, hxn]
          rw [← hx1, heq, hx2]
    · intro E hE
      have hEsub : E ⊆ rest := Finset.mem_powerset.mp hE
      refine ⟨E ∪ {i, nextIdx i}, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx | hpair, hnot⟩
          · exact hx
          · exact False.elim (hnot hpair)
        · intro hx
          have hxr := hEsub hx
          rw [Finset.mem_sdiff] at hxr
          exact ⟨Or.inl hx, by simpa using hxr.2⟩
    · intro D hD
      have h1 := (Finset.mem_filter.mp hD).2
      have hsub : ({i, nextIdx i} : Finset (Fin n)) ⊆ D := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact h1.1
        · rw [Finset.mem_singleton.mp hx']; exact h1.2
      have hcardD : (D \ {i, nextIdx i}).card = D.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair hne]
      have hDge2 : 2 ≤ D.card := by
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hne] at this
      have hDle : D.card ≤ n := by simpa using Finset.card_le_univ D
      rw [hcardD, hrest_card]
      have hpow1 : D.card = 2 + (D.card - 2) := by omega
      have hpow2 : n - D.card = n - 2 - (D.card - 2) := by omega
      rw [hpow2, ← mul_assoc, ← pow_add, ← hpow1]
  rw [hbij, ← Finset.mul_sum]
  have hsum1 : ∑ E ∈ rest.powerset, p ^ E.card * (1 - p) ^ (rest.card - E.card) = 1 := by
    have h2 : ∑ E ∈ rest.powerset, p ^ E.card * (1 - p) ^ (rest.card - E.card) =
        ∑ m ∈ Finset.range (rest.card + 1), (Nat.choose rest.card m : ℝ) * p ^ m * (1 - p) ^ (rest.card - m) := by
      have hpart : rest.powerset = (Finset.range (rest.card + 1)).biUnion (fun m => rest.powersetCard m) := by
        ext E
        simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        constructor
        · intro hE; exact ⟨E.card, Nat.lt_succ_of_le (Finset.card_le_card hE), hE, rfl⟩
        · rintro ⟨m, _, hE, _⟩; exact hE
      rw [hpart, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hconst : ∑ E ∈ rest.powersetCard m, p ^ E.card * (1 - p) ^ (rest.card - E.card) =
            ∑ _E ∈ rest.powersetCard m, p ^ m * (1 - p) ^ (rest.card - m) :=
          Finset.sum_congr rfl fun E hE => by rw [(Finset.mem_powersetCard.mp hE).2]
        rw [hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        ring
      · intro m₁ _ m₂ _ hm
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro E h1 h2
        exact hm ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
    rw [h2]
    have hadd := add_pow p (1 - p) rest.card
    rw [show p + (1 - p) = 1 by ring, one_pow] at hadd
    trans (∑ m ∈ Finset.range (rest.card + 1), p ^ m * (1 - p) ^ (rest.card - m) * (Nat.choose rest.card m : ℝ))
    · refine Finset.sum_congr rfl fun m _ => by ring
    · exact hadd.symm
  rw [hsum1, mul_one]

lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun b _ => hf b
    linarith

lemma sum_bernoulli_badDefects_le {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter badDefects,
        p ^ D.card * (1 - p) ^ (n - D.card) ≤ (n : ℝ) * p ^ 2 := by
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter badDefects ⊆
      (Finset.univ : Finset (Fin n)).biUnion
        (fun i => (Finset.univ : Finset (Finset (Fin n))).filter (fun D => i ∈ D ∧ nextIdx i ∈ D)) := by
    intro D hD
    obtain ⟨i, hi1, hi2⟩ := (Finset.mem_filter.mp hD).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi1, hi2⟩⟩
  have hnn : ∀ D : Finset (Fin n), 0 ≤ p ^ D.card * (1 - p) ^ (n - D.card) := fun D => by
    have : 0 ≤ 1 - p := by linarith
    positivity
  calc ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter badDefects,
          p ^ D.card * (1 - p) ^ (n - D.card)
      ≤ ∑ D ∈ (Finset.univ : Finset (Fin n)).biUnion
          (fun i => (Finset.univ : Finset (Finset (Fin n))).filter (fun D => i ∈ D ∧ nextIdx i ∈ D)),
          p ^ D.card * (1 - p) ^ (n - D.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ => hnn D)
    _ ≤ ∑ i : Fin n, ∑ D ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun D => i ∈ D ∧ nextIdx i ∈ D),
          p ^ D.card * (1 - p) ^ (n - D.card) :=
        sum_biUnion_le_nonneg _ _ _ hnn
    _ = ∑ _i : Fin n, p ^ 2 := Finset.sum_congr rfl fun i _ => sum_bernoulli_pair hn p i
    _ = (n : ℝ) * p ^ 2 := by simp

lemma gaussian_Iic_lipschitz (y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
    0 ≤ ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y₂)).toReal -
          ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y₁)).toReal ∧
    ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y₂)).toReal -
          ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y₁)).toReal ≤ y₂ - y₁ := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  have hfin : ∀ s : Set ℝ, μ s ≠ ⊤ := fun s => MeasureTheory.measure_ne_top μ s
  have hsplit : Set.Iic y₂ = Set.Iic y₁ ∪ Set.Ioc y₁ y₂ := (Set.Iic_union_Ioc_eq_Iic h).symm
  have hdisj : Disjoint (Set.Iic y₁) (Set.Ioc y₁ y₂) := Set.Iic_disjoint_Ioc le_rfl
  have hmeas : μ (Set.Iic y₂) = μ (Set.Iic y₁) + μ (Set.Ioc y₁ y₂) := by
    rw [hsplit, MeasureTheory.measure_union hdisj measurableSet_Ioc]
  have hsub : (μ (Set.Iic y₂)).toReal - (μ (Set.Iic y₁)).toReal = (μ (Set.Ioc y₁ y₂)).toReal := by
    rw [hmeas, ENNReal.toReal_add (hfin _) (hfin _)]
    ring
  rw [hsub]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hpdf : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x ≤ 1 := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hpi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
      simpa using Real.sqrt_le_sqrt h1
    have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
    have hinv_nn : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    nlinarith
  have hle_vol : μ (Set.Ioc y₁ y₂) ≤ MeasureTheory.volume (Set.Ioc y₁ y₂) := by
    rw [ProbabilityTheory.gaussianReal_apply 0 one_ne_zero]
    calc ∫⁻ x in Set.Ioc y₁ y₂, ProbabilityTheory.gaussianPDF 0 1 x
        ≤ ∫⁻ _x in Set.Ioc y₁ y₂, (1 : ENNReal) := by
          refine MeasureTheory.setLIntegral_mono_ae measurable_const.aemeasurable ?_
          filter_upwards with x _
          simp only [ProbabilityTheory.gaussianPDF]
          simpa using ENNReal.ofReal_le_ofReal (hpdf x)
      _ = MeasureTheory.volume (Set.Ioc y₁ y₂) := by simp
  have hvol : (MeasureTheory.volume (Set.Ioc y₁ y₂)).toReal = y₂ - y₁ := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  rw [← hvol]
  exact ENNReal.toReal_mono (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hle_vol

lemma continuous_gaussian_Iic :
    Continuous (fun y : ℝ => ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal) := by
  rw [Metric.continuous_iff]
  intro y ε hε
  refine ⟨ε, hε, fun y' hy' => ?_⟩
  rw [Real.dist_eq] at hy' ⊢
  rcases le_total y y' with hle | hle
  · have hb := gaussian_Iic_lipschitz y y' hle
    rw [abs_of_nonneg hb.1]
    have hlt : y' - y < ε := by rwa [abs_of_nonneg (by linarith)] at hy'
    linarith
  · have hb := gaussian_Iic_lipschitz y' y hle
    rw [abs_sub_comm, abs_of_nonneg hb.1]
    have hlt : y - y' < ε := by rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at hy'
    linarith

lemma log_one_add_bounds {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  refine ⟨?_, ?_⟩
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h1
    have h2 : u - u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
      have hne : 1 + u ≠ 0 := ne_of_gt hpos
      have hdiff : 1 - (1 + u)⁻¹ - (u - u ^ 2) = u ^ 3 / (1 + u) := by
        field_simp [hne]; ring
      have hnn : 0 ≤ u ^ 3 / (1 + u) := by positivity
      linarith
    linarith
  · linarith [Real.log_le_sub_one_of_pos hpos]

lemma sum_nonmixed_runs_le {t : ℕ} (_ht : 1 ≤ t) {s : ℝ} (hs : 1 ≤ s) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * t)))).filter
        (fun S => ¬ ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val),
        (s - 1) ^ (runsCard S) ≤ 2 * s ^ (3 * t) := by
  have hsub : (Finset.univ : Finset (Finset (Fin (6 * t)))).filter
      (fun S => ¬ ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val) ⊆
      (laneSet (n := 6 * t) 0).powerset ∪ (laneSet (n := 6 * t) 1).powerset := by
    intro S hS
    have hnm := (Finset.mem_filter.mp hS).2
    push Not at hnm
    obtain ⟨b, hb⟩ := hnm
    rcases Fin.exists_iff.mp ⟨b, rfl⟩ with _
    have hb2 : b = 0 ∨ b = 1 := by
      rcases b with ⟨v, hv⟩
      interval_cases v
      · left; rfl
      · right; rfl
    rcases hb2 with rfl | rfl
    · refine Finset.mem_union_right _ (Finset.mem_powerset.mpr fun i hi => ?_)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h0 : i.val % 2 ≠ 0 := hb i hi
      change i.val % 2 = 1
      omega
    · refine Finset.mem_union_left _ (Finset.mem_powerset.mpr fun i hi => ?_)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 : i.val % 2 ≠ 1 := hb i hi
      change i.val % 2 = 0
      omega
  have hlane_runs : ∀ (b : Fin 2) (S : Finset (Fin (6 * t))),
      S ⊆ laneSet b → runsCard S = S.card := by
    intro b S hSl
    unfold runsCard endsSet
    congr 1
    rw [Finset.filter_eq_self]
    intro i hi hni
    have hi_mod := (Finset.mem_filter.mp (hSl hi)).2
    have hni_mod := (Finset.mem_filter.mp (hSl hni)).2
    have hnext_mod : (nextIdx i).val % 2 = (i.val + 1) % 2 := by
      simp only [nextIdx]
      have hdvd : 2 ∣ 6 * t := ⟨3 * t, by ring⟩
      exact Nat.mod_mod_of_dvd (i.val + 1) hdvd
    omega
  have hlane_card : ∀ b : Fin 2, (laneSet (n := 6 * t) b).card = 3 * t := by
    intro b
    have hbij : (laneSet (n := 6 * t) b).card = (Finset.univ : Finset (Fin (3 * t))).card := by
      symm
      refine Finset.card_bij (fun j _ => ⟨2 * j.val + b.val, by omega⟩) ?_ ?_ ?_
      · intro j _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have := b.isLt
        dsimp only
        omega
      · intro j₁ _ j₂ _ h
        ext
        have hv := congrArg Fin.val h
        dsimp only at hv
        omega
      · intro i hi
        have hmod := (Finset.mem_filter.mp hi).2
        refine ⟨⟨i.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
        ext
        dsimp only
        omega
    simpa using hbij
  have hlane_sum : ∀ b : Fin 2,
      ∑ S ∈ (laneSet (n := 6 * t) b).powerset, (s - 1) ^ (runsCard S) = s ^ (3 * t) := by
    intro b
    have h1 : ∑ S ∈ (laneSet (n := 6 * t) b).powerset, (s - 1) ^ (runsCard S) =
        ∑ S ∈ (laneSet (n := 6 * t) b).powerset, (s - 1) ^ S.card :=
      Finset.sum_congr rfl fun S hS => by rw [hlane_runs b S (Finset.mem_powerset.mp hS)]
    rw [h1]
    have hpart : (laneSet (n := 6 * t) b).powerset =
        (Finset.range ((laneSet (n := 6 * t) b).card + 1)).biUnion
          (fun m => (laneSet (n := 6 * t) b).powersetCard m) := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro hS; exact ⟨S.card, Nat.lt_succ_of_le (Finset.card_le_card hS), hS, rfl⟩
      · rintro ⟨m, _, hS, _⟩; exact hS
    rw [hpart, Finset.sum_biUnion]
    · have h2 : ∑ m ∈ Finset.range ((laneSet (n := 6 * t) b).card + 1),
          ∑ S ∈ (laneSet (n := 6 * t) b).powersetCard m, (s - 1) ^ S.card =
          ∑ m ∈ Finset.range (3 * t + 1),
            (s - 1) ^ m * 1 ^ (3 * t - m) * (Nat.choose (3 * t) m : ℝ) := by
        rw [hlane_card b]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hc : ∑ S ∈ (laneSet (n := 6 * t) b).powersetCard m, (s - 1) ^ S.card =
            ∑ _S ∈ (laneSet (n := 6 * t) b).powersetCard m, (s - 1) ^ m :=
          Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
        rw [hc, Finset.sum_const, Finset.card_powersetCard, hlane_card b, nsmul_eq_mul, one_pow, mul_one]
        ring
      rw [h2, ← add_pow (s - 1) 1 (3 * t)]
      ring
    · intro m₁ _ m₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro S h1 h2
      exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  have hnn : ∀ S : Finset (Fin (6 * t)), 0 ≤ (s - 1) ^ (runsCard S) :=
    fun S => pow_nonneg (by linarith) _
  have hunion := Finset.sum_union_inter (s₁ := (laneSet (n := 6 * t) 0).powerset)
    (s₂ := (laneSet (n := 6 * t) 1).powerset) (f := fun S => (s - 1) ^ (runsCard S))
  have hinter : 0 ≤ ∑ S ∈ (laneSet (n := 6 * t) 0).powerset ∩ (laneSet (n := 6 * t) 1).powerset,
      (s - 1) ^ (runsCard S) := Finset.sum_nonneg fun S _ => hnn S
  have hle1 : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * t)))).filter
      (fun S => ¬ ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val), (s - 1) ^ (runsCard S) ≤
      ∑ S ∈ (laneSet (n := 6 * t) 0).powerset ∪ (laneSet (n := 6 * t) 1).powerset,
        (s - 1) ^ (runsCard S) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun S _ _ => hnn S)
  rw [hlane_sum 0, hlane_sum 1] at hunion
  linarith

lemma asymp_params (T D : ℕ → ℕ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hD2 : ∀ k, 2 ≤ D k)
    (x : ℝ)
    (hx : Filter.Tendsto (fun k => 6 * (T k : ℝ) / Real.sqrt ((2 : ℝ) ^ (D k))
      - 2 * Real.log ((2 : ℝ) ^ (D k))) Filter.atTop (nhds x)) :
    let n : ℕ → ℕ := fun k => 6 * T k
    let a : ℕ → ℕ := fun k => 3 * T k
    let s : ℕ → ℝ := fun k => (2 : ℝ) ^ (D k)
    let r : ℕ → ℝ := fun k => Real.sqrt (s k - 1)
    let L : ℕ → ℝ := fun k => 1 + r k
    let p : ℕ → ℝ := fun k => 1 / L k
    let mu : ℕ → ℝ := fun k => (n k : ℝ) / L k
    Filter.Tendsto D Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => (n k : ℝ) / s k) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (D k : ℝ) / (n k : ℝ)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto p Filter.atTop (nhds 0) ∧
    Filter.Tendsto mu Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => (n k : ℝ) * (p k) ^ 2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (L k) ^ (n k) / ((s k) ^ 4 * (s k) ^ (a k - 2))) Filter.atTop (nhds (Real.exp x)) ∧
    Filter.Tendsto (fun k => ((r k - 1) / (L k)) ^ (n k)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (s k)⁻¹) Filter.atTop (nhds 0) := by
  intro n a s r L p mu
  have hT_real : Filter.Tendsto (fun k => (T k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hT
  have hx_ub : ∀ᶠ k in Filter.atTop,
      6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k) ≤ x + 1 :=
    hx.eventually (ge_mem_nhds (show x < x + 1 by linarith))
  have hx_lb : ∀ᶠ k in Filter.atTop,
      x - 1 ≤ 6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k) :=
    hx.eventually (le_mem_nhds (show x - 1 < x by linarith))
  have hD_top : Filter.Tendsto D Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro M
    let C : ℝ := Real.sqrt ((2 : ℝ) ^ M) * (2 * Real.log ((2 : ℝ) ^ M) + |x| + 2)
    have hT_big : ∀ᶠ k in Filter.atTop, C / 6 < (T k : ℝ) :=
      hT_real.eventually (Filter.eventually_gt_atTop (C / 6))
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hx_ub.and hT_big)
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨hub, htb⟩ := hK k hk
    by_contra hlt
    push Not at hlt
    have hs_le : s k ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) (le_of_lt hlt)
    have hs_pos : 0 < s k := by positivity
    have hsq_le : Real.sqrt (s k) ≤ Real.sqrt ((2 : ℝ) ^ M) := Real.sqrt_le_sqrt hs_le
    have hlog_le : Real.log (s k) ≤ Real.log ((2 : ℝ) ^ M) := Real.log_le_log hs_pos hs_le
    have hlog_nn : 0 ≤ Real.log ((2 : ℝ) ^ M) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    have h1 : 6 * (T k : ℝ) ≤ Real.sqrt (s k) * (2 * Real.log (s k) + x + 1) := by
      have hsq_pos : 0 < Real.sqrt (s k) := Real.sqrt_pos.mpr hs_pos
      have hdiv : 6 * (T k : ℝ) / Real.sqrt (s k) ≤ 2 * Real.log (s k) + x + 1 := by linarith
      have hmul := (div_le_iff₀ hsq_pos).mp hdiv
      linarith
    have h2 : 2 * Real.log (s k) + x + 1 ≤ 2 * Real.log ((2 : ℝ) ^ M) + |x| + 2 := by
      linarith [le_abs_self x]
    have h3 : Real.sqrt (s k) * (2 * Real.log (s k) + x + 1) ≤ C := by
      have hsq_nn : 0 ≤ Real.sqrt (s k) := Real.sqrt_nonneg _
      have hrhs_nn : 0 ≤ 2 * Real.log ((2 : ℝ) ^ M) + |x| + 2 := by linarith [abs_nonneg x]
      calc Real.sqrt (s k) * (2 * Real.log (s k) + x + 1)
          ≤ Real.sqrt (s k) * (2 * Real.log ((2 : ℝ) ^ M) + |x| + 2) :=
            mul_le_mul_of_nonneg_left h2 hsq_nn
        _ ≤ Real.sqrt ((2 : ℝ) ^ M) * (2 * Real.log ((2 : ℝ) ^ M) + |x| + 2) :=
            mul_le_mul_of_nonneg_right hsq_le hrhs_nn
    linarith
  have hs_top : Filter.Tendsto s Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hD_top
  have hs_inv : Filter.Tendsto (fun k => (s k)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hs_top
  have hsq_top : Filter.Tendsto (fun k => Real.sqrt (s k)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hs_top
  have hsq_inv : Filter.Tendsto (fun k => (Real.sqrt (s k))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsq_top
  have hqsq_top : Filter.Tendsto (fun k => Real.sqrt (Real.sqrt (s k))) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hsq_top
  have hlog_div_sqrt : Filter.Tendsto (fun k => Real.log (s k) / Real.sqrt (s k)) Filter.atTop (nhds 0) := by
    have hbd : Filter.Tendsto (fun k => 4 * (Real.sqrt (Real.sqrt (s k)))⁻¹) Filter.atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hqsq_top).const_mul (4 : ℝ)
    refine squeeze_zero' ?_ ?_ hbd
    · filter_upwards with k
      have hs1 : (1 : ℝ) ≤ s k := one_le_pow₀ (by norm_num)
      exact div_nonneg (Real.log_nonneg hs1) (Real.sqrt_nonneg _)
    · filter_upwards with k
      have hs_pos : 0 < s k := by positivity
      set q := Real.sqrt (Real.sqrt (s k))
      have hq_pos : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hs_pos)
      have hq2 : q ^ 2 = Real.sqrt (s k) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have hq4 : q ^ 4 = s k := by
        calc q ^ 4 = (q ^ 2) ^ 2 := by ring
          _ = Real.sqrt (s k) ^ 2 := by rw [hq2]
          _ = s k := Real.sq_sqrt (le_of_lt hs_pos)
      have hlog_eq : Real.log (s k) = 4 * Real.log q := by
        rw [← hq4, Real.log_pow]; ring
      have hlog_le : Real.log q ≤ q := by linarith [Real.log_le_sub_one_of_pos hq_pos]
      rw [hlog_eq, ← hq2]
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      calc 4 * Real.log q / q ^ 2 ≤ 4 * q / q ^ 2 := by gcongr
        _ = 4 * q⁻¹ := by field_simp [hq_ne]
  have hn_div_s : Filter.Tendsto (fun k => (n k : ℝ) / s k) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun k => (6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k)) * (Real.sqrt (s k))⁻¹
          + 2 * (Real.log (s k) / Real.sqrt (s k))) Filter.atTop (nhds 0) := by
      have ha := hx.mul hsq_inv
      have hb := hlog_div_sqrt.const_mul (2 : ℝ)
      have hab := ha.add hb
      rw [mul_zero, mul_zero, add_zero] at hab
      exact hab
    refine h1.congr' ?_
    filter_upwards with k
    have hs_pos : 0 < s k := by positivity
    have hsq_pos : 0 < Real.sqrt (s k) := Real.sqrt_pos.mpr hs_pos
    have hsq_ne : Real.sqrt (s k) ≠ 0 := ne_of_gt hsq_pos
    have hsq_sq : Real.sqrt (s k) ^ 2 = s k := Real.sq_sqrt (le_of_lt hs_pos)
    have hn_eq : (n k : ℝ) = 6 * (T k : ℝ) := by simp [n]
    calc (6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k)) * (Real.sqrt (s k))⁻¹ +
            2 * (Real.log (s k) / Real.sqrt (s k))
        = 6 * (T k : ℝ) / Real.sqrt (s k) ^ 2 := by field_simp [hsq_ne]; ring
      _ = (n k : ℝ) / s k := by rw [hsq_sq, hn_eq]
  have hlog_top : Filter.Tendsto (fun k => Real.log (s k)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hs_top
  have hD_div_n : Filter.Tendsto (fun k => (D k : ℝ) / (n k : ℝ)) Filter.atTop (nhds 0) := by
    have hbd : Filter.Tendsto (fun k => (Real.log 2)⁻¹ * (Real.sqrt (s k))⁻¹) Filter.atTop (nhds 0) := by
      simpa using hsq_inv.const_mul (Real.log 2)⁻¹
    refine squeeze_zero' (Filter.Eventually.of_forall fun k => by positivity) ?_ hbd
    filter_upwards [hx_lb, hlog_top.eventually (Filter.eventually_ge_atTop (|x| + 2))] with k hlb hlg
    have hs_pos : 0 < s k := by positivity
    have hsq_pos : 0 < Real.sqrt (s k) := Real.sqrt_pos.mpr hs_pos
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_s : Real.log (s k) = (D k : ℝ) * Real.log 2 := by
      simp only [s, Real.log_pow]
    have hge1 : Real.log (s k) ≤ 6 * (T k : ℝ) / Real.sqrt (s k) := by
      linarith [neg_abs_le x]
    have hge2 : Real.sqrt (s k) * ((D k : ℝ) * Real.log 2) ≤ (n k : ℝ) := by
      have hn_eq : (n k : ℝ) = 6 * (T k : ℝ) := by simp [n]
      rw [hn_eq, ← hlog_s]
      have := (le_div_iff₀ hsq_pos).mp hge1
      linarith
    have hD_pos : (0 : ℝ) < (D k : ℝ) := by
      have : (2 : ℝ) ≤ (D k : ℝ) := by exact_mod_cast hD2 k
      linarith
    have hn_pos : (0 : ℝ) < (n k : ℝ) := lt_of_lt_of_le (by positivity) hge2
    rw [div_le_iff₀ hn_pos]
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
    have hsq_ne : Real.sqrt (s k) ≠ 0 := ne_of_gt hsq_pos
    have hmul : (Real.log 2)⁻¹ * (Real.sqrt (s k))⁻¹ * (Real.sqrt (s k) * ((D k : ℝ) * Real.log 2)) = (D k : ℝ) := by
      field_simp [hlog2_ne, hsq_ne]
    calc (D k : ℝ) = (Real.log 2)⁻¹ * (Real.sqrt (s k))⁻¹ * (Real.sqrt (s k) * ((D k : ℝ) * Real.log 2)) := hmul.symm
      _ ≤ (Real.log 2)⁻¹ * (Real.sqrt (s k))⁻¹ * (n k : ℝ) := by
          gcongr
  have hr_top : Filter.Tendsto r Filter.atTop Filter.atTop := by
    have hs1 : Filter.Tendsto (fun k => s k - 1) Filter.atTop Filter.atTop :=
      hs_top.atTop_add tendsto_const_nhds
    exact Real.tendsto_sqrt_atTop.comp hs1
  have hL_top : Filter.Tendsto L Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => by simp only [L]; linarith) hr_top
  have hp_zero : Filter.Tendsto p Filter.atTop (nhds 0) := by
    have : p = fun k => (L k)⁻¹ := by funext k; simp [p]
    rw [this]
    exact tendsto_inv_atTop_zero.comp hL_top
  have hmu_top : Filter.Tendsto mu Filter.atTop Filter.atTop := by
    have hhalf_log : Filter.Tendsto (fun k => Real.log (s k) / 2) Filter.atTop Filter.atTop :=
      hlog_top.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hhalf_log
    filter_upwards [hx_lb, hlog_top.eventually (Filter.eventually_ge_atTop (|x| + 2)),
      hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hlb hlg hs4
    have hs_pos : 0 < s k := by linarith
    have hsq_ge2 : 2 ≤ Real.sqrt (s k) := by
      have : Real.sqrt (2 ^ 2) ≤ Real.sqrt (s k) := Real.sqrt_le_sqrt (by linarith)
      simpa using this
    have hr_le : r k ≤ Real.sqrt (s k) := Real.sqrt_le_sqrt (by linarith)
    have hL_le : L k ≤ 2 * Real.sqrt (s k) := by simp only [L]; linarith
    have hL_pos : 0 < L k := by
      have : 0 ≤ r k := Real.sqrt_nonneg _
      simp only [L]; linarith
    have hge1 : Real.log (s k) ≤ 6 * (T k : ℝ) / Real.sqrt (s k) := by
      linarith [neg_abs_le x]
    have hge2 : Real.log (s k) * Real.sqrt (s k) ≤ (n k : ℝ) := by
      have hn_eq : (n k : ℝ) = 6 * (T k : ℝ) := by simp [n]
      rw [hn_eq]
      exact (le_div_iff₀ (by linarith)).mp hge1
    simp only [mu]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hL_pos]
    have hlg_nn : 0 ≤ Real.log (s k) := by linarith [abs_nonneg x]
    nlinarith
  have hn_div_Lsq : Filter.Tendsto (fun k => (n k : ℝ) * (p k) ^ 2) Filter.atTop (nhds 0) := by
    have hbd : Filter.Tendsto (fun k => 2 * ((n k : ℝ) / s k)) Filter.atTop (nhds 0) := by
      simpa using hn_div_s.const_mul (2 : ℝ)
    refine squeeze_zero' (Filter.Eventually.of_forall fun k => by positivity) ?_ hbd
    filter_upwards [hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hs4
    have hL_ge : Real.sqrt (s k - 1) ≤ L k := by simp only [L]; linarith
    have hL_pos : 0 < L k := by
      have : 0 < Real.sqrt (s k - 1) := Real.sqrt_pos.mpr (by linarith)
      linarith
    have hL2 : s k / 2 ≤ (L k) ^ 2 := by
      have h1 : s k - 1 ≤ (L k) ^ 2 := by
        calc s k - 1 = Real.sqrt (s k - 1) ^ 2 := (Real.sq_sqrt (by linarith)).symm
          _ ≤ (L k) ^ 2 := by nlinarith [Real.sqrt_nonneg (s k - 1)]
      linarith
    simp only [p, one_div, inv_pow, ← div_eq_mul_inv]
    rw [show 2 * ((n k : ℝ) / s k) = (n k : ℝ) / (s k / 2) by ring]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) hL2
  have h_thresh : Filter.Tendsto (fun k => (L k) ^ (n k) / ((s k) ^ 4 * (s k) ^ (a k - 2)))
      Filter.atTop (nhds (Real.exp x)) := by
    have hexp_arg : Filter.Tendsto
        (fun k => (n k : ℝ) * Real.log (L k / Real.sqrt (s k)) - 2 * Real.log (s k))
        Filter.atTop (nhds x) := by
      have hdiff_zero : Filter.Tendsto
          (fun k => ((n k : ℝ) * Real.log (L k / Real.sqrt (s k)) - 2 * Real.log (s k)) -
            (6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k))) Filter.atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hbd : Filter.Tendsto (fun k => 2 * ((n k : ℝ) / s k)) Filter.atTop (nhds 0) := by
          simpa using hn_div_s.const_mul (2 : ℝ)
        refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hbd
        filter_upwards [hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hs4
        have hs_pos : 0 < s k := by linarith
        have hsq_pos : 0 < Real.sqrt (s k) := Real.sqrt_pos.mpr hs_pos
        have hr_pos : 0 < r k := Real.sqrt_pos.mpr (by linarith)
        have hsq_sq : Real.sqrt (s k) ^ 2 = s k := Real.sq_sqrt (le_of_lt hs_pos)
        have hr_sq : r k ^ 2 = s k - 1 := Real.sq_sqrt (by linarith)
        have hconj : Real.sqrt (s k) - r k = 1 / (Real.sqrt (s k) + r k) := by
          have hne : Real.sqrt (s k) + r k ≠ 0 := by linarith
          field_simp [hne]
          nlinarith
        set u : ℝ := L k / Real.sqrt (s k) - 1
        have hu_eq : u = 1 / Real.sqrt (s k) - 1 / (Real.sqrt (s k) * (Real.sqrt (s k) + r k)) := by
          simp only [u, L]
          have hsq_ne : Real.sqrt (s k) ≠ 0 := ne_of_gt hsq_pos
          have hsum_ne : Real.sqrt (s k) + r k ≠ 0 := by linarith
          have : (1 + r k) / Real.sqrt (s k) - 1 = (1 - (Real.sqrt (s k) - r k)) / Real.sqrt (s k) := by
            field_simp [hsq_ne]; ring
          rw [this, hconj]
          field_simp [hsq_ne, hsum_ne]
        have hu_nn : 0 ≤ u := by
          rw [hu_eq]
          have : Real.sqrt (s k) ≤ Real.sqrt (s k) * (Real.sqrt (s k) + r k) := by
            have hge1 : 1 ≤ Real.sqrt (s k) + r k := by
              have : 2 ≤ Real.sqrt (s k) := by
                have h := Real.sqrt_le_sqrt (show (2 : ℝ) ^ 2 ≤ s k by linarith)
                simpa using h
              linarith
            nlinarith
          have := one_div_le_one_div_of_le hsq_pos this
          linarith
        have hu_le : u ≤ 1 / Real.sqrt (s k) := by
          rw [hu_eq]
          have : 0 ≤ 1 / (Real.sqrt (s k) * (Real.sqrt (s k) + r k)) := by positivity
          linarith
        have hu_diff : 1 / Real.sqrt (s k) - u ≤ 1 / s k := by
          rw [hu_eq]
          have h1 : s k ≤ Real.sqrt (s k) * (Real.sqrt (s k) + r k) := by nlinarith
          have := one_div_le_one_div_of_le hs_pos h1
          linarith
        have hu2 : u ^ 2 ≤ 1 / s k := by
          calc u ^ 2 ≤ (1 / Real.sqrt (s k)) ^ 2 := by nlinarith
            _ = 1 / s k := by rw [div_pow, one_pow, hsq_sq]
        have hlog_b := log_one_add_bounds hu_nn
        have h1u : 1 + u = L k / Real.sqrt (s k) := by simp [u]
        rw [h1u] at hlog_b
        have habs_log : |Real.log (L k / Real.sqrt (s k)) - 1 / Real.sqrt (s k)| ≤ 2 / s k := by
          have h1s_nn : 0 ≤ 1 / s k := by positivity
          have h2s : 2 / s k = 1 / s k + 1 / s k := by ring
          rw [abs_le, h2s]
          constructor <;> linarith [hlog_b.1, hlog_b.2]
        have hrew : ((n k : ℝ) * Real.log (L k / Real.sqrt (s k)) - 2 * Real.log (s k)) -
            (6 * (T k : ℝ) / Real.sqrt (s k) - 2 * Real.log (s k)) =
            (n k : ℝ) * (Real.log (L k / Real.sqrt (s k)) - 1 / Real.sqrt (s k)) := by
          have hn_eq : (n k : ℝ) = 6 * (T k : ℝ) := by simp [n]
          rw [hn_eq]; ring
        rw [hrew, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        calc (n k : ℝ) * |Real.log (L k / Real.sqrt (s k)) - 1 / Real.sqrt (s k)|
            ≤ (n k : ℝ) * (2 / s k) := mul_le_mul_of_nonneg_left habs_log (Nat.cast_nonneg _)
          _ = 2 * ((n k : ℝ) / s k) := by ring
      have hadd := hdiff_zero.add hx
      rw [zero_add] at hadd
      refine hadd.congr' (Filter.Eventually.of_forall fun k => ?_)
      simp only [s]; ring
    have hexp := (Real.continuous_exp.tendsto x).comp hexp_arg
    refine hexp.congr' ?_
    filter_upwards [hT.eventually (Filter.eventually_ge_atTop 2),
      hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k ht2 hs4
    have hs_pos : 0 < s k := by linarith
    have hsq_pos : 0 < Real.sqrt (s k) := Real.sqrt_pos.mpr hs_pos
    have hL_pos : 0 < L k := by
      have : 0 ≤ r k := Real.sqrt_nonneg _
      simp only [L]; linarith
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (div_pos hL_pos hsq_pos),
      show (2 : ℝ) * Real.log (s k) = ((2 : ℕ) : ℝ) * Real.log (s k) by norm_num,
      Real.exp_nat_mul, Real.exp_log hs_pos, div_pow]
    have hsq_pow : Real.sqrt (s k) ^ n k = s k ^ a k := by
      have hn2a : n k = 2 * a k := by simp only [n, a]; omega
      rw [hn2a, pow_mul, Real.sq_sqrt (le_of_lt hs_pos)]
    rw [hsq_pow]
    have ha2 : 2 ≤ a k := by simp only [a]; omega
    have hpow_eq : s k ^ 4 * s k ^ (a k - 2) = s k ^ a k * s k ^ 2 := by
      rw [← pow_add, ← pow_add]
      congr 1; omega
    rw [hpow_eq, div_div]
  have h_ratio_pow : Filter.Tendsto (fun k => ((r k - 1) / (L k)) ^ (n k)) Filter.atTop (nhds 0) := by
    have hexp_zero : Filter.Tendsto (fun k => Real.exp (-(2 * mu k))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp (hmu_top.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    refine squeeze_zero' ?_ ?_ hexp_zero
    · filter_upwards [hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hs4
      have hr1 : 1 ≤ r k := by
        have : Real.sqrt (1 ^ 2) ≤ Real.sqrt (s k - 1) := Real.sqrt_le_sqrt (by linarith)
        simpa [r] using this
      have hL_pos : 0 < L k := by simp only [L]; linarith
      exact pow_nonneg (div_nonneg (by linarith) (le_of_lt hL_pos)) _
    · filter_upwards [hs_top.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hs4
      have hr1 : 1 ≤ r k := by
        have : Real.sqrt (1 ^ 2) ≤ Real.sqrt (s k - 1) := Real.sqrt_le_sqrt (by linarith)
        simpa [r] using this
      have hL_pos : 0 < L k := by simp only [L]; linarith
      have hL_ne : L k ≠ 0 := ne_of_gt hL_pos
      have hle1 : (r k - 1) / L k ≤ Real.exp (-(2 / L k)) := by
        have hrew : (r k - 1) / L k = -(2 / L k) + 1 := by
          simp only [L] at hL_ne ⊢
          field_simp [hL_ne]; ring
        rw [hrew]
        exact Real.add_one_le_exp _
      calc ((r k - 1) / L k) ^ n k
          ≤ (Real.exp (-(2 / L k))) ^ n k := pow_le_pow_left₀ (div_nonneg (by linarith) (le_of_lt hL_pos)) hle1 _
        _ = Real.exp (-(2 * mu k)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            simp only [mu]; ring
  exact ⟨hD_top, hn_div_s, hD_div_n, hp_zero, hmu_top, hn_div_Lsq, h_thresh, h_ratio_pow, hs_inv⟩

lemma remOdd_empty_of_not_badDefects {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hgood : ¬ badDefects (defectsSet S)) : remOdd S hS = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hge3 : 3 ≤ zdist S hS j := (Finset.mem_filter.mp hj).2.1
  have hj0 : j ∉ S := by simpa using zdist_lt S hS (show 0 < zdist S hS j by omega)
  have hj1 : prevIdx j ∉ S := by simpa using zdist_lt S hS (show 1 < zdist S hS j by omega)
  have hj2 : prevIdx (prevIdx j) ∉ S := by
    have := zdist_lt S hS (show 2 < zdist S hS j by omega)
    simpa [Function.iterate_succ_apply'] using this
  let i : Fin n := prevIdx (prevIdx j)
  have hni : nextIdx i = prevIdx j := nextIdx_prevIdx (prevIdx j)
  have hnni : nextIdx (nextIdx i) = j := by rw [hni, nextIdx_prevIdx]
  apply hgood
  refine ⟨i, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hni]
    exact ⟨fun h => absurd h hj2, fun h => absurd h hj1⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hni, nextIdx_prevIdx]
    exact ⟨fun h => absurd h hj1, fun h => absurd h hj0⟩

lemma runs_weight_eq_bernoulli {n : ℕ} {s : ℝ} (hs : 1 < s) (S : Finset (Fin n)) :
    let r := Real.sqrt (s - 1)
    let L := 1 + r
    let p := 1 / L
    (s - 1) ^ (runsCard S) / L ^ n = p ^ (defectsSet S).card * (1 - p) ^ (n - (defectsSet S).card) := by
  intro r L p
  have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
  have hL_pos : 0 < L := by simp only [L]; linarith
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have h1mp : 1 - p = r / L := by
    simp only [p, L] at hL_ne ⊢
    field_simp [hL_ne]
    ring
  have hcard := defects_card_add_two_runs S
  have hsub : n - (defectsSet S).card = 2 * runsCard S := by omega
  have hkle : (defectsSet S).card ≤ n := by omega
  have hr_pow : r ^ (n - (defectsSet S).card) = (s - 1) ^ (runsCard S) := by
    rw [hsub, pow_mul, Real.sq_sqrt (by linarith)]
  rw [h1mp]
  simp only [p]
  rw [div_pow, div_pow, one_pow, hr_pow]
  have hden : L ^ (defectsSet S).card * L ^ (n - (defectsSet S).card) = L ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkle]
  calc (s - 1) ^ runsCard S / L ^ n
      = 1 * (s - 1) ^ runsCard S / (L ^ (defectsSet S).card * L ^ (n - (defectsSet S).card)) := by
          rw [one_mul, hden]
    _ = 1 / L ^ (defectsSet S).card * ((s - 1) ^ runsCard S / L ^ (n - (defectsSet S).card)) := by
          rw [div_mul_div_comm]

lemma sum_runs_filter_defects_card {t : ℕ} (ht : 1 ≤ t) {s : ℝ} (hs : 1 < s) (Q : ℕ → Prop) :
    let n := 6 * t
    let r := Real.sqrt (s - 1)
    let L := 1 + r
    let p := 1 / L
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => Q (defectsSet S).card),
        (s - 1) ^ (runsCard S) / L ^ n =
      2 * ∑ m ∈ (Finset.range (n + 1)).filter (fun m => Even m ∧ Q m), binomProb n p m := by
  intro n r L p
  have hn_pos : 0 < n := by simp only [n]; omega
  have hn_even : Even n := ⟨3 * t, by simp only [n]; ring⟩
  rw [Finset.sum_filter]
  have hterm : ∑ S : Finset (Fin n),
        (if Q (defectsSet S).card then (s - 1) ^ (runsCard S) / L ^ n else 0) =
      ∑ S : Finset (Fin n),
        (if Q (defectsSet S).card then p ^ (defectsSet S).card * (1 - p) ^ (n - (defectsSet S).card) else 0) :=
    Finset.sum_congr rfl fun S _ => by rw [runs_weight_eq_bernoulli hs S]
  rw [hterm]
  have h2 := sum_over_finset_eq_two_mul_even_defects hn_pos hn_even
    (fun D => if Q D.card then p ^ D.card * (1 - p) ^ (n - D.card) else 0)
  rw [h2]
  congr 1
  rw [← Finset.sum_filter]
  have hf_eq : ((Finset.univ : Finset (Finset (Fin n))).filter (fun D => Even D.card)).filter (fun D => Q D.card) =
      (Finset.univ : Finset (Finset (Fin n))).filter (fun D => Even D.card ∧ Q D.card) := by
    ext D; simp [and_comm]
  rw [hf_eq]
  have hsub := sum_bernoulli_subsets (n := n) p (fun m => Even m ∧ Q m)
  refine (Finset.sum_congr (by ext D; simp) fun _ _ => rfl).trans
    (hsub.trans (Finset.sum_congr (by ext m; simp) fun m _ => by unfold binomProb; rfl))

lemma sum_runs_badDefects_le {t : ℕ} (ht : 1 ≤ t) {s : ℝ} (hs : 1 < s) :
    let n := 6 * t
    let r := Real.sqrt (s - 1)
    let L := 1 + r
    let p := 1 / L
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => badDefects (defectsSet S)),
        (s - 1) ^ (runsCard S) / L ^ n ≤ 2 * (n : ℝ) * p ^ 2 := by
  intro n r L p
  have hn_pos : 0 < n := by simp only [n]; omega
  have hn_ge2 : 2 ≤ n := by simp only [n]; omega
  have hn_even : Even n := ⟨3 * t, by simp only [n]; ring⟩
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hp0 : 0 ≤ p := by simp only [p, L]; positivity
  have hp1 : p ≤ 1 := by
    simp only [p, L]
    rw [div_le_one (by linarith)]
    linarith
  rw [Finset.sum_filter]
  have hterm : ∑ S : Finset (Fin n),
        (if badDefects (defectsSet S) then (s - 1) ^ (runsCard S) / L ^ n else 0) =
      ∑ S : Finset (Fin n),
        (if badDefects (defectsSet S) then p ^ (defectsSet S).card * (1 - p) ^ (n - (defectsSet S).card) else 0) :=
    Finset.sum_congr rfl fun S _ => by rw [runs_weight_eq_bernoulli hs S]
  rw [hterm]
  have h2 := sum_over_finset_eq_two_mul_even_defects hn_pos hn_even
    (fun D => if badDefects D then p ^ D.card * (1 - p) ^ (n - D.card) else 0)
  rw [h2, ← Finset.sum_filter]
  have hsub : ((Finset.univ : Finset (Finset (Fin n))).filter (fun D => Even D.card)).filter badDefects ⊆
      (Finset.univ : Finset (Finset (Fin n))).filter badDefects := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    exact hD.2
  have hnn : ∀ D : Finset (Fin n), 0 ≤ p ^ D.card * (1 - p) ^ (n - D.card) := fun D => by
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hle1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ => hnn D)
  have hle2 := sum_bernoulli_badDefects_le hn_ge2 hp0 hp1
  linarith

lemma filter_tail_eq_range (n : ℕ) {mu : ℝ} (hmu : 0 < mu) (y : ℝ) :
    ∃ K ≤ n + 1,
      (Finset.range (n + 1)).filter (fun m : ℕ => ((m : ℝ) - mu) / Real.sqrt mu ≤ y) =
        Finset.range K := by
  have hsq : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  set X : ℝ := mu + y * Real.sqrt mu
  have hiff : ∀ m : ℕ, (((m : ℝ) - mu) / Real.sqrt mu ≤ y) ↔ (m : ℝ) ≤ X := by
    intro m
    rw [div_le_iff₀ hsq]
    simp only [X]
    constructor <;> intro h <;> linarith
  by_cases hX : X < 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Nat.not_lt_zero, iff_false, not_and]
    intro _ hm
    have h1 := (hiff m).mp hm
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  · push Not at hX
    refine ⟨min (n + 1) (Nat.floor X + 1), min_le_left _ _, ?_⟩
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff, Nat.lt_succ_iff, hiff,
      Nat.le_floor_iff hX]

lemma tendsto_even_defects_tail (T D : ℕ → ℕ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hD2 : ∀ k, 2 ≤ D k)
    (x : ℝ)
    (hx : Filter.Tendsto (fun k => 6 * (T k : ℝ) / Real.sqrt ((2 : ℝ) ^ (D k))
      - 2 * Real.log ((2 : ℝ) ^ (D k))) Filter.atTop (nhds x))
    (y : ℝ) :
    Filter.Tendsto
      (fun k =>
        let n := 6 * T k
        let s := (2 : ℝ) ^ (D k)
        let L := 1 + Real.sqrt (s - 1)
        let mu := (n : ℝ) / L
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => (((defectsSet S).card : ℝ) - mu) / Real.sqrt mu ≤ y),
          (s - 1) ^ (runsCard S) / L ^ n)
      Filter.atTop
      (nhds (((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal)) := by
  have hasymp := asymp_params T D hT hD2 x hx
  rcases hasymp with ⟨hD_top, _, _, hp_zero, hmu_top, _, _, _, hs_inv⟩
  let n : ℕ → ℕ := fun k => 6 * T k
  let s : ℕ → ℝ := fun k => (2 : ℝ) ^ (D k)
  let L : ℕ → ℝ := fun k => 1 + Real.sqrt (s k - 1)
  let p : ℕ → ℝ := fun k => 1 / L k
  have hp0 : ∀ᶠ k in Filter.atTop, 0 < p k := by
    filter_upwards with k
    have : 0 ≤ Real.sqrt (s k - 1) := Real.sqrt_nonneg _
    simp only [p, L]; positivity
  have hp10 : ∀ᶠ k in Filter.atTop, p k ≤ 1 / 10 :=
    hp_zero.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  have hp1 : ∀ᶠ k in Filter.atTop, p k < 1 := by
    filter_upwards [hp10] with k hk; linarith
  have hmu_eq : ∀ k, (n k : ℝ) / L k = (n k : ℝ) * p k := fun k => by simp [p, div_eq_mul_inv]
  have hmu_top' : Filter.Tendsto (fun k => (n k : ℝ) * p k) Filter.atTop Filter.atTop := by
    simpa only [← hmu_eq] using hmu_top
  have hclt := tendsto_binom_tail_gaussian hp0 hp1 hp_zero hmu_top' y
  have hdiff_zero : Filter.Tendsto
      (fun k =>
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (n k)))).filter
            (fun S => (((defectsSet S).card : ℝ) - (n k : ℝ) / L k) / Real.sqrt ((n k : ℝ) / L k) ≤ y),
          (s k - 1) ^ (runsCard S) / (L k) ^ (n k)) -
        (∑ m ∈ (Finset.range (n k + 1)).filter
            (fun m : ℕ => ((m : ℝ) - (n k : ℝ) * p k) / Real.sqrt ((n k : ℝ) * p k) ≤ y),
          binomProb (n k) (p k) m))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : Filter.Tendsto (fun k => 8 / Real.sqrt ((n k : ℝ) * p k)) Filter.atTop (nhds 0) := by
      have hsq := Real.tendsto_sqrt_atTop.comp hmu_top'
      have hinv := tendsto_inv_atTop_zero.comp hsq
      have : (fun k => 8 / Real.sqrt ((n k : ℝ) * p k)) = (fun k => 8 * (Real.sqrt ((n k : ℝ) * p k))⁻¹) := by
        funext k; ring
      rw [this]
      simpa using hinv.const_mul (8 : ℝ)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hbd
    filter_upwards [hT.eventually (Filter.eventually_ge_atTop 1), hp0, hp10,
      hmu_top'.eventually (Filter.eventually_ge_atTop (100 : ℝ))] with k ht1 hpk0 hpk10 hmu100
    have hs1 : (1 : ℝ) < s k := by
      have : (2 : ℝ) ^ 2 ≤ s k := pow_le_pow_right₀ (by norm_num) (hD2 k)
      linarith
    have heq1 := sum_runs_filter_defects_card ht1 hs1
      (fun m => ((m : ℝ) - (n k : ℝ) / L k) / Real.sqrt ((n k : ℝ) / L k) ≤ y)
    dsimp only at heq1
    rw [heq1]
    simp_rw [hmu_eq k]
    obtain ⟨K, _, hK⟩ := filter_tail_eq_range (n k) (by linarith : 0 < (n k : ℝ) * p k) y
    have hfilt_ev : (Finset.range (n k + 1)).filter
        (fun m : ℕ => Even m ∧ ((m : ℝ) - (n k : ℝ) * p k) / Real.sqrt ((n k : ℝ) * p k) ≤ y) =
        (Finset.range K).filter Even := by
      rw [← hK]
      ext m
      simp only [Finset.mem_filter]
      tauto
    rw [hfilt_ev, hK, two_mul_sum_even_sub_sum, Real.norm_eq_abs]
    have h1 := abs_alt_sum_binomProb_le_two_peak (n := n k) hpk0 (by linarith) K
    have h2 := binomProb_peak_le hpk0 hpk10 hmu100
    have h8 : 8 / Real.sqrt ((n k : ℝ) * p k) = 2 * (4 / Real.sqrt ((n k : ℝ) * p k)) := by ring
    linarith
  have hadd := hdiff_zero.add hclt
  simpa only [zero_add, sub_add_cancel] using hadd

lemma sum_runs_total_asymptotic (T D : ℕ → ℕ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hD2 : ∀ k, 2 ≤ D k)
    (x : ℝ)
    (hx : Filter.Tendsto (fun k => 6 * (T k : ℝ) / Real.sqrt ((2 : ℝ) ^ (D k))
      - 2 * Real.log ((2 : ℝ) ^ (D k))) Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun k =>
        let n := 6 * T k
        let a := 3 * T k
        let s := (2 : ℝ) ^ (D k)
        (∑ S : Finset (Fin n), (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2))
      Filter.atTop (nhds (Real.exp x)) := by
  have hasymp := asymp_params T D hT hD2 x hx
  rcases hasymp with ⟨_, _, _, _, _, _, h_thresh, h_ratio_pow, _⟩
  have hprod : Filter.Tendsto
      (fun k =>
        let n := 6 * T k
        let a := 3 * T k
        let s := (2 : ℝ) ^ (D k)
        let r := Real.sqrt (s - 1)
        let L := 1 + r
        (L ^ n / (s ^ 4 * s ^ (a - 2))) * (1 + ((r - 1) / L) ^ n))
      Filter.atTop (nhds (Real.exp x)) := by
    simpa using h_thresh.mul ((tendsto_const_nhds (x := (1 : ℝ))).add h_ratio_pow)
  refine hprod.congr' ?_
  filter_upwards [hT.eventually (Filter.eventually_ge_atTop 1)] with k ht1
  set n := 6 * T k
  set a := 3 * T k
  set s := (2 : ℝ) ^ (D k)
  set r := Real.sqrt (s - 1)
  set L := 1 + r
  have hs1 : (1 : ℝ) < s := by
    have : (2 : ℝ) ^ 2 ≤ s := pow_le_pow_right₀ (by norm_num) (hD2 k)
    linarith
  have hn1 : 1 ≤ n := by simp only [n]; omega
  have hsum : ∑ S : Finset (Fin n), (s - 1) ^ (runsCard S) = L ^ n + (1 - r) ^ n := by
    rw [sum_runs_eq_trace_A n hn1 s, trace_matA_pow_eq s hs1 n]
  have hneg : (1 - r) ^ n = (r - 1) ^ n := by
    have hev : n = 2 * a := by simp only [n, a]; omega
    have hsq : (1 - r) ^ 2 = (r - 1) ^ 2 := by ring
    calc (1 - r) ^ n = ((1 - r) ^ 2) ^ a := by rw [hev]; exact pow_mul (1 - r) 2 a
      _ = ((r - 1) ^ 2) ^ a := by rw [hsq]
      _ = (r - 1) ^ n := by rw [hev]; exact (pow_mul (r - 1) 2 a).symm
  have hL_pos : 0 < L := by
    have : 0 ≤ r := Real.sqrt_nonneg _
    simp only [L]; linarith
  have hL_ne : L ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
  change (L ^ n / (s ^ 4 * s ^ (a - 2))) * (1 + ((r - 1) / L) ^ n) =
    (∑ S : Finset (Fin n), (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2)
  rw [← Finset.sum_div, hsum, hneg, div_div, div_pow]
  field_simp [hL_ne]

noncomputable def instFinSub (n : ℕ) : Fintype (Submodule F2 (Space n)) :=
  Fintype.ofFinite _

lemma ratio_bound_for_aux (t d : ℕ) (ht : 10 ≤ t) (hd : 40 ≤ d)
    (hds : 6 * (t : ℝ) ≤ (2 : ℝ) ^ d / 100) (hdt : 12 * d ≤ t) :
    let good := fun U : Submodule F2 (Space (6 * t)) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
    let spaces := (@Finset.univ (Submodule F2 (Space (6 * t))) (instFinSub (6 * t))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Space (6 * t)) => Module.finrank F2 U = d)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    let s := (2 : ℝ) ^ d
    let a := 3 * t
    let model := fun S : Finset (Fin (6 * t)) =>
      (if S = laneSet 0 then s ^ (a - 2) else 0) +
      (if S = laneSet 1 then s ^ (a - 2) else 0) +
      (s - 1) ^ (runsCard S) / s ^ 4
    let actual := fun S : Finset (Fin (6 * t)) =>
      (B : ℝ) * ((layer.filter (fun U => supportSub U = S)).card : ℝ)
    (∑ S : Finset (Fin (6 * t)), |actual S - model S|) / (∑ S : Finset (Fin (6 * t)), model S) ≤
      60 * ((6 * (t : ℝ)) / (2 : ℝ) ^ d) + 40 / (2 : ℝ) ^ d + 300 * ((1 : ℝ) / 2) ^ t := by
  have hmain := @main_ratio_bound t d ht hd hds hdt (instFinSub (6 * t))
  have hfilt : ∀ {α : Type} {s₁ s₂ : Finset α} {p q : α → Prop}
      {d₁ : DecidablePred p} {d₂ : DecidablePred q},
      s₁ = s₂ → (∀ u, p u ↔ q u) → @Finset.filter α p d₁ s₁ = @Finset.filter α q d₂ s₂ := by
    intro α s₁ s₂ p q d₁ d₂ hs hpq
    subst hs; ext u; simp only [Finset.mem_filter, hpq]
  have heq_actual : ∀ S : Finset (Fin (6 * t)),
      ((∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ) : ℕ) : ℝ) *
        ((((((@Finset.univ (Submodule F2 (Space (6 * t))) (instFinSub (6 * t))).filter
            (fun U : Submodule F2 (Space (6 * t)) =>
              (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U)).filter
            (fun U : Submodule F2 (Space (6 * t)) => Module.finrank F2 U = d)).filter
            (fun U : Submodule F2 (Space (6 * t)) => supportSub U = S)).card) : ℝ) =
      ((∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ) : ℕ) : ℝ) *
        ((((((@Finset.univ (Submodule (ZMod 2) (Fin (6 * t) → ZMod 2)) (instFinSub (6 * t))).filter
            (fun U : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2) =>
              (∀ x ∈ U, ∀ b : Fin 4, (∑ i, (if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0) * x i) = 0) ∧
              (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (nextIdx i) = x (nextIdx i) * y i))).filter
            (fun U : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2) => Module.finrank (ZMod 2) U = d)).filter
            (fun U : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2) => Finset.univ.filter (fun i : Fin (6 * t) => ∃ x ∈ U, x i ≠ 0) = S)).card) : ℝ) := by
    intro S
    congr 2
    refine congrArg Finset.card ?_
    refine hfilt (hfilt (hfilt rfl fun _ => Iff.rfl) fun _ => Iff.rfl) fun U => ?_
    exact iff_of_eq (congrArg (· = S) (hfilt rfl fun _ => Iff.rfl))
  have heq_model : ∀ S : Finset (Fin (6 * t)),
      ((if S = laneSet 0 then ((2 : ℝ) ^ d) ^ (3 * t - 2) else 0) +
       (if S = laneSet 1 then ((2 : ℝ) ^ d) ^ (3 * t - 2) else 0) +
       ((2 : ℝ) ^ d - 1) ^ (runsCard S) / ((2 : ℝ) ^ d) ^ 4) =
      ((if S = Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = (0 : Fin 2).val) then ((2 : ℝ) ^ d) ^ (3 * t - 2) else 0) +
       (if S = Finset.univ.filter (fun i : Fin (6 * t) => i.val % 2 = (1 : Fin 2).val) then ((2 : ℝ) ^ d) ^ (3 * t - 2) else 0) +
       ((2 : ℝ) ^ d - 1) ^ ((S.filter (fun i => nextIdx i ∉ S)).card) / ((2 : ℝ) ^ d) ^ 4) := by
    intro S
    rfl
  dsimp only
  calc _ = _ := congrArg₂ (· / ·)
          (Finset.sum_congr rfl fun S _ => congrArg abs (congrArg₂ (· - ·) (heq_actual S) (heq_model S)))
          (Finset.sum_congr rfl fun S _ => heq_model S)
    _ ≤ _ := hmain

set_option maxHeartbeats 800000 in
lemma main_L_lib_941_core (T D : ℕ → ℕ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hD2 : ∀ k, 2 ≤ D k)
    (x : ℝ)
    (hx : Filter.Tendsto (fun k => 6 * (T k : ℝ) / Real.sqrt ((2 : ℝ) ^ (D k))
      - 2 * Real.log ((2 : ℝ) ^ (D k))) Filter.atTop (nhds x))
    (z : Option ℝ) :
    Filter.Tendsto (fun k : ℕ =>
      let t := T k
      let d := D k
      let n := 6 * t
      let a := 3 * t
      let good := fun U : Submodule F2 (Space n) =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
      let spaces := (@Finset.univ (Submodule F2 (Space n)) (instFinSub n)).filter good
      let layer := spaces.filter (fun U : Submodule F2 (Space n) => Module.finrank F2 U = d)
      let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supportSub U, i.val % 2 = b.val)
      let s := (2 : ℝ) ^ d
      let mu := (n : ℝ) / (1 + Real.sqrt (s - 1))
      let host := fun U : Submodule F2 (Space n) =>
        (spaces.filter (fun E : Submodule F2 (Space n) => U ≤ E)).sup (fun E => Module.finrank F2 E)
      let event : Finset (Submodule F2 (Space n)) := match z with
        | none => mixed
        | some y => mixed.filter (fun U =>
            (2 * ((a - host U : ℕ) : ℝ) - mu) / Real.sqrt mu ≤ y)
      (event.card : ℝ) / (layer.card : ℝ))
      Filter.atTop
      (nhds ((Real.exp x / (2 + Real.exp x)) * (match z with
        | none => 1
        | some y => ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal))) := by
  have hasymp := asymp_params T D hT hD2 x hx
  rcases hasymp with ⟨hD_top, hn_div_s, hD_div_n, hp_zero, hmu_top, hn_div_Lsq, h_thresh, h_ratio_pow, hs_inv⟩
  have htot := sum_runs_total_asymptotic T D hT hD2 x hx
  have hT_ev10 : ∀ᶠ k in Filter.atTop, 10 ≤ T k := hT.eventually (Filter.eventually_ge_atTop 10)
  have hD_ev40 : ∀ᶠ k in Filter.atTop, 40 ≤ D k := hD_top.eventually (Filter.eventually_ge_atTop 40)
  have hn_div_s' : Filter.Tendsto (fun k => (6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) Filter.atTop (nhds 0) := by
    simpa [Nat.cast_mul] using hn_div_s
  have hD_div_n' : Filter.Tendsto (fun k => (D k : ℝ) / (6 * (T k : ℝ))) Filter.atTop (nhds 0) := by
    simpa [Nat.cast_mul] using hD_div_n
  have hSmall_ev : ∀ᶠ k in Filter.atTop, (6 * (T k : ℝ)) / (2 : ℝ) ^ (D k) < 1 / 100 :=
    hn_div_s'.eventually (gt_mem_nhds (by norm_num))
  have hDsmall_ev : ∀ᶠ k in Filter.atTop, (D k : ℝ) / (6 * (T k : ℝ)) < 1 / 72 :=
    hD_div_n'.eventually (gt_mem_nhds (by norm_num))
  have hHalf_zero : Filter.Tendsto (fun k => ((1 : ℝ) / 2) ^ (T k)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hT
  have hRatio_rhs : Filter.Tendsto
      (fun k => 60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((2 : ℝ) ^ (D k))⁻¹ +
        300 * ((1 : ℝ) / 2) ^ (T k)) Filter.atTop (nhds 0) := by
    have h1 := hn_div_s'.const_mul (60 : ℝ)
    have h2 := hs_inv.const_mul (40 : ℝ)
    have h3 := hHalf_zero.const_mul (300 : ℝ)
    simpa using (h1.add h2).add h3
  let mixedSupp : ∀ {n : ℕ}, Finset (Fin n) → Prop :=
    fun S => ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val
  let modelFn : ∀ (k : ℕ), Finset (Fin (6 * T k)) → ℝ := fun k S =>
    let s := (2 : ℝ) ^ (D k)
    let a := 3 * T k
    (if S = laneSet 0 then s ^ (a - 2) else 0) +
    (if S = laneSet 1 then s ^ (a - 2) else 0) +
    (s - 1) ^ (runsCard S) / s ^ 4
  let actualFn : ∀ (k : ℕ), Finset (Fin (6 * T k)) → ℝ := fun k S =>
    let good := fun U : Submodule F2 (Space (6 * T k)) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
    let spaces := (@Finset.univ (Submodule F2 (Space (6 * T k))) (instFinSub (6 * T k))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
    let B := ∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ)
    (B : ℝ) * ((layer.filter (fun U => supportSub U = S)).card : ℝ)
  let Zmod : ℕ → ℝ := fun k => ∑ S : Finset (Fin (6 * T k)), modelFn k S
  let Zact : ℕ → ℝ := fun k => ∑ S : Finset (Fin (6 * T k)), actualFn k S
  let Err : ℕ → ℝ := fun k => ∑ S : Finset (Fin (6 * T k)), |actualFn k S - modelFn k S|
  have hZmod_lim : Filter.Tendsto (fun k => Zmod k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
      Filter.atTop (nhds (2 + Real.exp x)) := by
    have hsum : Filter.Tendsto
        (fun k => 2 + (∑ S : Finset (Fin (6 * T k)), ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) /
          ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) Filter.atTop (nhds (2 + Real.exp x)) :=
      tendsto_const_nhds.add htot
    refine hsum.congr' ?_
    filter_upwards [hT_ev10] with k ht10
    have hZeq : Zmod k = 2 * ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
        ∑ S : Finset (Fin (6 * T k)), ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4 := by
      simp only [Zmod, modelFn, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    rw [hZeq, add_div]
    have hne : ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) ≠ 0 := by positivity
    field_simp [hne]
  have hErr_lim : Filter.Tendsto (fun k => Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
      Filter.atTop (nhds 0) := by
    have hprod : Filter.Tendsto
        (fun k => (60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((2 : ℝ) ^ (D k))⁻¹ +
          300 * ((1 : ℝ) / 2) ^ (T k)) * (Zmod k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)))
        Filter.atTop (nhds 0) := by
      simpa using hRatio_rhs.mul hZmod_lim
    refine squeeze_zero' (Filter.Eventually.of_forall fun k => by
        exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) ?_ hprod
    filter_upwards [hT_ev10, hD_ev40, hSmall_ev, hDsmall_ev] with k ht10 hd40 hsm hdsm
    have hds : 6 * (T k : ℝ) ≤ (2 : ℝ) ^ (D k) / 100 := by
      have hspos : (0 : ℝ) < (2 : ℝ) ^ (D k) := by positivity
      rw [div_lt_iff₀ hspos] at hsm; linarith
    have hdt : 12 * D k ≤ T k := by
      have htpos : (0 : ℝ) < 6 * (T k : ℝ) := by
        have : (10 : ℝ) ≤ (T k : ℝ) := by exact_mod_cast ht10
        linarith
      rw [div_lt_iff₀ htpos] at hdsm
      have hreal : (12 * D k : ℝ) ≤ (T k : ℝ) := by linarith
      exact_mod_cast hreal
    have hbound := ratio_bound_for_aux (T k) (D k) ht10 hd40 hds hdt
    have hZpos : 0 < Zmod k := by
      have hterm0 : ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) ≤ modelFn k (laneSet 0) := by
        simp only [modelFn, ite_true]
        have h1 : (0 : ℝ) ≤ if laneSet (n := 6 * T k) 0 = laneSet 1 then ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) else 0 := by
          split_ifs <;> positivity
        have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D k) := one_le_pow₀ (by norm_num)
        have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (D k) - 1) ^ (runsCard (laneSet (n := 6 * T k) 0)) / ((2 : ℝ) ^ (D k)) ^ 4 :=
          div_nonneg (pow_nonneg (by linarith) _) (by positivity)
        linarith
      have hnn : ∀ S : Finset (Fin (6 * T k)), 0 ≤ modelFn k S := fun S => by
        simp only [modelFn]
        have h1 : (0 : ℝ) ≤ if S = laneSet 0 then ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) else 0 := by split_ifs <;> positivity
        have h2 : (0 : ℝ) ≤ if S = laneSet 1 then ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) else 0 := by split_ifs <;> positivity
        have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D k) := one_le_pow₀ (by norm_num)
        have h3 : (0 : ℝ) ≤ ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4 :=
          div_nonneg (pow_nonneg (by linarith) _) (by positivity)
        linarith
      have hle := Finset.single_le_sum (fun S _ => hnn S) (Finset.mem_univ (laneSet (n := 6 * T k) 0))
      have hpos0 : (0 : ℝ) < ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) := by positivity
      linarith
    have hbound' : Err k / Zmod k ≤
        60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((2 : ℝ) ^ (D k))⁻¹ + 300 * ((1 : ℝ) / 2) ^ (T k) := by
      have h40 : 40 / (2 : ℝ) ^ (D k) = 40 * ((2 : ℝ) ^ (D k))⁻¹ := by ring
      rw [← h40]
      exact hbound
    have hErr_le := (div_le_iff₀ hZpos).mp hbound'
    have hden_pos : (0 : ℝ) < ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) := by positivity
    rw [div_le_iff₀ hden_pos]
    calc Err k ≤ (60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((2 : ℝ) ^ (D k))⁻¹ +
            300 * ((1 : ℝ) / 2) ^ (T k)) * Zmod k := hErr_le
      _ = (60 * ((6 * (T k : ℝ)) / (2 : ℝ) ^ (D k)) + 40 * ((2 : ℝ) ^ (D k))⁻¹ +
            300 * ((1 : ℝ) / 2) ^ (T k)) * (Zmod k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) *
            ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) := by
            have hne : ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) ≠ 0 := ne_of_gt hden_pos
            field_simp [hne]
  have hZact_lim : Filter.Tendsto (fun k => Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
      Filter.atTop (nhds (2 + Real.exp x)) := by
    have hdiff : Filter.Tendsto
        (fun k => (Zact k - Zmod k) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hErr_lim
      filter_upwards with k
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))]
      gcongr
      simp only [Zact, Zmod, Err, ← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    have hadd := hdiff.add hZmod_lim
    rw [zero_add] at hadd
    refine hadd.congr' ?_
    filter_upwards with k
    ring
  have hNonMix_lim : Filter.Tendsto
      (fun k =>
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => ¬ mixedSupp S),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) /
        ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
      Filter.atTop (nhds 0) := by
    have hbd : Filter.Tendsto (fun k => 2 * (((2 : ℝ) ^ (D k))⁻¹) ^ 2) Filter.atTop (nhds 0) := by
      simpa using (hs_inv.pow 2).const_mul (2 : ℝ)
    refine squeeze_zero' ?_ ?_ hbd
    · filter_upwards with k
      refine div_nonneg (Finset.sum_nonneg fun S _ => ?_) (by positivity)
      have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D k) := one_le_pow₀ (by norm_num)
      exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
    · filter_upwards [hT_ev10] with k ht10
      have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D k) := one_le_pow₀ (by norm_num)
      have hle := sum_nonmixed_runs_le (by omega : 1 ≤ T k) hs1
      rw [← Finset.sum_div, div_div]
      have hs_pos : (0 : ℝ) < (2 : ℝ) ^ (D k) := by positivity
      have hs_ne : (2 : ℝ) ^ (D k) ≠ 0 := ne_of_gt hs_pos
      have hpow_eq : ((2 : ℝ) ^ (D k)) ^ 4 * ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) =
          ((2 : ℝ) ^ (D k)) ^ (3 * T k) * ((2 : ℝ) ^ (D k)) ^ 2 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [hpow_eq]
      calc (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => ¬ mixedSupp S),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S)) /
              (((2 : ℝ) ^ (D k)) ^ (3 * T k) * ((2 : ℝ) ^ (D k)) ^ 2)
          ≤ (2 * ((2 : ℝ) ^ (D k)) ^ (3 * T k)) /
              (((2 : ℝ) ^ (D k)) ^ (3 * T k) * ((2 : ℝ) ^ (D k)) ^ 2) :=
            div_le_div_of_nonneg_right hle (by positivity)
        _ = 2 * (((2 : ℝ) ^ (D k))⁻¹) ^ 2 := by
            have hne3 : ((2 : ℝ) ^ (D k)) ^ (3 * T k) ≠ 0 := by positivity
            field_simp [hs_ne, hne3]
  have hBad_lim : Filter.Tendsto
      (fun k =>
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) /
        ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
      Filter.atTop (nhds 0) := by
    have hbd : Filter.Tendsto
        (fun k =>
          let n := 6 * T k
          let a := 3 * T k
          let s := (2 : ℝ) ^ (D k)
          let L := 1 + Real.sqrt (s - 1)
          let p := 1 / L
          (L ^ n / (s ^ 4 * s ^ (a - 2))) * (2 * (n : ℝ) * p ^ 2))
        Filter.atTop (nhds 0) := by
      have h2 := hn_div_Lsq.const_mul (2 : ℝ)
      have h2' : Filter.Tendsto (fun k => 2 * ((6 * T k : ℕ) : ℝ) * (1 / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ^ 2)
          Filter.atTop (nhds 0) := by
        simpa [mul_assoc] using h2
      simpa using h_thresh.mul h2'
    refine squeeze_zero' ?_ ?_ hbd
    · filter_upwards with k
      refine div_nonneg (Finset.sum_nonneg fun S _ => ?_) (by positivity)
      have hs1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D k) := one_le_pow₀ (by norm_num)
      exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
    · filter_upwards [hT_ev10] with k ht10
      set n := 6 * T k
      set a := 3 * T k
      set s := (2 : ℝ) ^ (D k)
      set L := 1 + Real.sqrt (s - 1)
      set p := 1 / L
      have hs1 : (1 : ℝ) < s := by
        have : (2 : ℝ) ^ 2 ≤ s := pow_le_pow_right₀ (by norm_num) (hD2 k)
        linarith
      have hL_pos : 0 < L := by
        have : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
        simp only [L]; linarith
      have hle := sum_runs_badDefects_le (by omega : 1 ≤ T k) hs1
      dsimp only at hle
      have hrew : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => badDefects (defectsSet S)),
            (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) =
          (L ^ n / (s ^ 4 * s ^ (a - 2))) *
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => badDefects (defectsSet S)),
              (s - 1) ^ (runsCard S) / L ^ n) := by
        rw [← Finset.sum_div, ← Finset.sum_div, div_div]
        have hL_ne : L ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
        have hs_ne : s ^ 4 * s ^ (a - 2) ≠ 0 := by positivity
        field_simp [hL_ne, hs_ne]
      rw [hrew]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hlayer_eq : ∀ k,
      let good := fun U : Submodule F2 (Space (6 * T k)) =>
        (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
      let spaces := (@Finset.univ (Submodule F2 (Space (6 * T k))) (instFinSub (6 * T k))).filter good
      let layer := spaces.filter (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
      let B := ∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ)
      (B : ℝ) * (layer.card : ℝ) = Zact k := by
    intro k
    let good := fun U : Submodule F2 (Space (6 * T k)) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
    let spaces := (@Finset.univ (Submodule F2 (Space (6 * T k))) (instFinSub (6 * T k))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
    let B := ∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ)
    have hfib : layer.card = ∑ S : Finset (Fin (6 * T k)), (layer.filter (fun U => supportSub U = S)).card :=
      Finset.card_eq_sum_card_fiberwise (f := supportSub) (fun _ _ => Finset.mem_univ _)
    simp only [Zact, actualFn, ← Finset.mul_sum]
    congr 1
    exact_mod_cast hfib
  have hB_pos : ∀ k, (0 : ℝ) < ((∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ) : ℕ) : ℝ) := by
    intro k
    have hnat : 0 < ∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ) :=
      Finset.prod_pos fun i hi => by
        have hlt : i < D k := Finset.mem_range.mp hi
        have hpow : 2 ^ i < 2 ^ D k := Nat.pow_lt_pow_right (by norm_num) hlt
        omega
    exact_mod_cast hnat
  have hmodel_mixed : ∀ (k : ℕ) (S : Finset (Fin (6 * T k))), mixedSupp S →
      modelFn k S = ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4 := by
    intro k S hSm
    have hne0 : S ≠ laneSet 0 := by
      intro heq
      obtain ⟨i, hi, hmod⟩ := hSm 1
      rw [heq] at hi
      have h0 := (Finset.mem_filter.mp hi).2
      change i.val % 2 = 0 at h0
      change i.val % 2 = 1 at hmod
      omega
    have hne1 : S ≠ laneSet 1 := by
      intro heq
      obtain ⟨i, hi, hmod⟩ := hSm 0
      rw [heq] at hi
      have h1 := (Finset.mem_filter.mp hi).2
      change i.val % 2 = 1 at h1
      change i.val % 2 = 0 at hmod
      omega
    simp [modelFn, hne0, hne1]
  have hden_pos_lim : (0 : ℝ) < 2 + Real.exp x := by positivity
  cases z with
  | none =>
    simp only [mul_one]
    have hmix_mod : Filter.Tendsto
        (fun k => (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, modelFn k S) /
          ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) Filter.atTop (nhds (Real.exp x)) := by
      have hsub := htot.sub hNonMix_lim
      rw [sub_zero] at hsub
      refine hsub.congr' ?_
      filter_upwards with k
      have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin (6 * T k))))
        mixedSupp (fun S => ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4)
      have hcongr : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, modelFn k S =
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp,
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4 :=
        Finset.sum_congr rfl fun S hS => hmodel_mixed k S (Finset.mem_filter.mp hS).2
      rw [hcongr, ← sub_div]
      congr 1
      linarith
    have hmix_act : Filter.Tendsto
        (fun k => (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, actualFn k S) /
          ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) Filter.atTop (nhds (Real.exp x)) := by
      have hdiff : Filter.Tendsto
          (fun k =>
            ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, actualFn k S) -
             (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, modelFn k S)) /
            ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) Filter.atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hErr_lim
        filter_upwards with k
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))]
        gcongr
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _)
      have hadd := hdiff.add hmix_mod
      rw [zero_add] at hadd
      refine hadd.congr' ?_
      filter_upwards with k
      ring
    have hdiv := hmix_act.div hZact_lim (ne_of_gt hden_pos_lim)
    refine hdiv.congr' ?_
    filter_upwards [hZact_lim.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < 2 + Real.exp x))] with k _
    let good := fun U : Submodule F2 (Space (6 * T k)) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
    let spaces := (@Finset.univ (Submodule F2 (Space (6 * T k))) (instFinSub (6 * T k))).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supportSub U, i.val % 2 = b.val)
    let B := ∏ i ∈ Finset.range (D k), (2 ^ D k - 2 ^ i : ℕ)
    have hmix_eq : (B : ℝ) * (mixed.card : ℝ) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, actualFn k S := by
      have hfib : mixed.card =
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp,
            (layer.filter (fun U => supportSub U = S)).card := by
        have h1 : mixed.card = ∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp,
            (mixed.filter (fun U => supportSub U = S)).card :=
          Finset.card_eq_sum_card_fiberwise (f := supportSub) fun U hU =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hU).2⟩
        rw [h1]
        refine Finset.sum_congr rfl fun S hS => congrArg Finset.card ?_
        have hSm := (Finset.mem_filter.mp hS).2
        ext U
        simp only [mixed, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hU, _⟩, rfl⟩; exact ⟨hU, rfl⟩
        · rintro ⟨hU, rfl⟩; exact ⟨⟨hU, hSm⟩, rfl⟩
      simp only [actualFn, ← Finset.mul_sum]
      congr 1
      exact_mod_cast hfib
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt (hB_pos k)
    have hpow_ne : ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) ≠ 0 := by positivity
    change ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter mixedSupp, actualFn k S) /
        ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) / (Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) =
      (mixed.card : ℝ) / (layer.card : ℝ)
    rw [← hmix_eq, ← hlayer_eq k, div_div_div_cancel_right₀ hpow_ne, mul_div_mul_left _ _ hBne]
  | some y =>
    let Φ : ℝ → ℝ := fun u => ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic u)).toReal
    let c : ℝ := Real.exp x / (2 + Real.exp x)
    have hc_nn : 0 ≤ c := by positivity
    have hc_le1 : c ≤ 1 := by
      simp only [c]
      rw [div_le_one hden_pos_lim]
      linarith
    have htail_lim : ∀ y' : ℝ, Filter.Tendsto
        (fun k =>
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
              (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
                Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y'),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) /
          ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
        Filter.atTop (nhds (Real.exp x * Φ y')) := by
      intro y'
      have hev := tendsto_even_defects_tail T D hT hD2 x hx y'
      have hprod := h_thresh.mul hev
      refine hprod.congr' ?_
      filter_upwards with k
      set n := 6 * T k
      set a := 3 * T k
      set s := (2 : ℝ) ^ (D k)
      set L := 1 + Real.sqrt (s - 1)
      have hL_pos : 0 < L := by
        have : 0 ≤ Real.sqrt (s - 1) := Real.sqrt_nonneg _
        simp only [L]; linarith
      have hL_ne : L ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hL_pos)
      have hs_ne : s ^ 4 * s ^ (a - 2) ≠ 0 := by positivity
      change (L ^ n / (s ^ 4 * s ^ (a - 2))) *
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
              (fun S => (((defectsSet S).card : ℝ) - (n : ℝ) / L) / Real.sqrt ((n : ℝ) / L) ≤ y'),
            (s - 1) ^ (runsCard S) / L ^ n) =
        (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => (((defectsSet S).card : ℝ) - (n : ℝ) / L) / Real.sqrt ((n : ℝ) / L) ≤ y'),
          (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2)
      rw [← Finset.sum_div, ← Finset.sum_div, div_div]
      set Ssum := ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => (((defectsSet S).card : ℝ) - (n : ℝ) / L) / Real.sqrt ((n : ℝ) / L) ≤ y'),
        (s - 1) ^ (runsCard S)
      rw [div_mul_div_comm, mul_comm (L ^ n) Ssum, mul_div_mul_right _ _ hL_ne]
    rw [Metric.tendsto_atTop]
    intro ε hε
    set η : ℝ := ε / 2
    have hη_pos : 0 < η := by positivity
    have hΦ_diff : Φ y - Φ (y - η) ≤ η := by
      linarith [(gaussian_Iic_lipschitz (y - η) y (by linarith)).2]
    have hupper_lim : Filter.Tendsto
        (fun k =>
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
              (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
                Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
           (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
           Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) /
          (Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)))
        Filter.atTop (nhds (c * Φ y)) := by
      have hnum : Filter.Tendsto
          (fun k =>
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
              (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
                Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
            Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
          Filter.atTop (nhds (Real.exp x * Φ y)) := by
        simpa using ((htail_lim y).add hBad_lim).add hErr_lim
      have hdiv := hnum.div hZact_lim (ne_of_gt hden_pos_lim)
      have hlim : (Real.exp x * Φ y) / (2 + Real.exp x) = c * Φ y := by simp only [c]; ring
      rw [hlim] at hdiv
      exact hdiv
    have hlower_lim : Filter.Tendsto
        (fun k =>
          ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
              (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
                Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y - η),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
           (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => ¬ mixedSupp S),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
           (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
            ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
           Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) /
          (Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)))
        Filter.atTop (nhds (c * Φ (y - η))) := by
      have hnum : Filter.Tendsto
          (fun k =>
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
              (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
                Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y - η),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => ¬ mixedSupp S),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
            (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
              ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
            Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2))
          Filter.atTop (nhds (Real.exp x * Φ (y - η))) := by
        simpa using (((htail_lim (y - η)).sub hNonMix_lim).sub hBad_lim).sub hErr_lim
      have hdiv := hnum.div hZact_lim (ne_of_gt hden_pos_lim)
      have hlim : (Real.exp x * Φ (y - η)) / (2 + Real.exp x) = c * Φ (y - η) := by simp only [c]; ring
      rw [hlim] at hdiv
      exact hdiv
    have hev_up : ∀ᶠ k in Filter.atTop,
        ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
            (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
              Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
         (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) +
         Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) /
        (Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) < c * Φ y + ε :=
      hupper_lim.eventually (gt_mem_nhds (show c * Φ y < c * Φ y + ε by linarith))
    have hev_lo : ∀ᶠ k in Filter.atTop,
        c * Φ (y - η) - ε / 2 <
        ((∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter
            (fun S => (((defectsSet S).card : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
              Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y - η),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
         (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => ¬ mixedSupp S),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
         (∑ S ∈ (Finset.univ : Finset (Finset (Fin (6 * T k)))).filter (fun S => badDefects (defectsSet S)),
          ((2 : ℝ) ^ (D k) - 1) ^ (runsCard S) / ((2 : ℝ) ^ (D k)) ^ 4) / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) -
         Err k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) /
        (Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2)) :=
      hlower_lim.eventually (lt_mem_nhds (show c * Φ (y - η) - ε / 2 < c * Φ (y - η) by linarith))
    have hev_mu : ∀ᶠ k in Filter.atTop, (8 / η) ^ 2 + 1 ≤ ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1)) :=
      hmu_top.eventually (Filter.eventually_ge_atTop _)
    have hev_zpos : ∀ᶠ k in Filter.atTop, 0 < Zact k / ((2 : ℝ) ^ (D k)) ^ (3 * T k - 2) :=
      hZact_lim.eventually (lt_mem_nhds hden_pos_lim)
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      (hT_ev10.and (hev_up.and (hev_lo.and (hev_mu.and hev_zpos))))
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨ht10, hup_k, hlo_k, hmu_k, hzpos_k⟩ := hK k hk
    set t := T k
    set d := D k
    set n := 6 * t
    set a := 3 * t
    set s := (2 : ℝ) ^ d
    set mu := (n : ℝ) / (1 + Real.sqrt (s - 1))
    let good := fun U : Submodule F2 (Space n) =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U
    let spaces := (@Finset.univ (Submodule F2 (Space n)) (instFinSub n)).filter good
    let layer := spaces.filter (fun U : Submodule F2 (Space n) => Module.finrank F2 U = d)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supportSub U, i.val % 2 = b.val)
    let host := fun U : Submodule F2 (Space n) =>
      (spaces.filter (fun E : Submodule F2 (Space n) => U ≤ E)).sup (fun E => Module.finrank F2 E)
    let event := mixed.filter (fun U => (2 * ((a - host U : ℕ) : ℝ) - mu) / Real.sqrt mu ≤ y)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    have hmu_pos : 0 < mu := by
      have : 0 ≤ (8 / η) ^ 2 := sq_nonneg _
      linarith
    have hsq_pos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu_pos
    have h8_le : 8 / Real.sqrt mu ≤ η := by
      have hsq_ge : 8 / η ≤ Real.sqrt mu := by
        have h1 : (8 / η) ^ 2 ≤ mu := by linarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by positivity)] at h2
      rw [div_le_iff₀ hsq_pos]
      have := (div_le_iff₀ hη_pos).mp hsq_ge
      linarith
    have hhost_sand : ∀ U ∈ mixed, ¬ badDefects (defectsSet (supportSub U)) →
        ((defectsSet (supportSub U)).card : ℝ) ≤ 2 * ((a - host U : ℕ) : ℝ) ∧
        2 * ((a - host U : ℕ) : ℝ) ≤ ((defectsSet (supportSub U)).card : ℝ) + 8 := by
      intro U hU hgoodU
      have hU_layer : U ∈ layer := (Finset.mem_filter.mp hU).1
      have hU_mix : mixedSupp (supportSub U) := (Finset.mem_filter.mp hU).2
      have hU_sp : U ∈ spaces := (Finset.mem_filter.mp hU_layer).1
      have hU_rk : Module.finrank F2 U = d := (Finset.mem_filter.mp hU_layer).2
      have hU_gd : good U := (Finset.mem_filter.mp hU_sp).2
      have hS_ne : (supportSub U).Nonempty := by
        obtain ⟨i, hi, _⟩ := hU_mix 0
        exact ⟨i, hi⟩
      have hb := @host_bounds n d (hD2 k) (fun i b => hMat i b) U hU_rk hU_gd.1 hU_gd.2 hS_ne (instFinSub n)
      dsimp only at hb
      have hodd := oddZSet_card_eq (supportSub U) hS_ne
      have hrem := remOdd_empty_of_not_badDefects (supportSub U) hS_ne hgoodU
      rw [hrem, Finset.card_empty, add_zero] at hodd
      rw [hodd] at hb
      have hhost_eq_hb : host U =
          (((@Finset.univ (Submodule F2 (Space n)) (instFinSub n)).filter
            (fun E => (∀ x ∈ E, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub E)).filter
            (fun E => U ≤ E)).sup (fun E => Module.finrank F2 E) := rfl
      rw [← hhost_eq_hb] at hb
      have hdef := defects_card_add_two_runs (supportSub U)
      have hn2a : n = 2 * a := by simp only [n, a]; omega
      have hlo_nat : (defectsSet (supportSub U)).card ≤ 2 * (a - host U) := by omega
      have hhi_nat : 2 * (a - host U) ≤ (defectsSet (supportSub U)).card + 8 := by omega
      exact ⟨by exact_mod_cast hlo_nat, by exact_mod_cast hhi_nat⟩
    let tailSet : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => (((defectsSet S).card : ℝ) - mu) / Real.sqrt mu ≤ y)
    let tailSetLo : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => (((defectsSet S).card : ℝ) - mu) / Real.sqrt mu ≤ y - η)
    let badSet : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => badDefects (defectsSet S))
    let mixSet : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter mixedSupp
    let nonMixSet : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ mixedSupp S)
    have hact_nn : ∀ S : Finset (Fin n), 0 ≤ actualFn k S := fun S => by
      simp only [actualFn]; positivity
    have hrun_nn : ∀ S : Finset (Fin n), 0 ≤ (s - 1) ^ (runsCard S) / s ^ 4 := fun S => by
      have hs1 : (1 : ℝ) ≤ s := one_le_pow₀ (by norm_num)
      exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
    have hev_card_up : (B : ℝ) * (event.card : ℝ) ≤
        (∑ S ∈ tailSet, (s - 1) ^ (runsCard S) / s ^ 4) +
        (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) + Err k := by
      let goodSupps := (tailSet ∪ badSet) ∩ mixSet
      have hfib_le : event.card ≤ ∑ S ∈ goodSupps, (layer.filter (fun U => supportSub U = S)).card := by
        have h1 : event.card = ∑ S ∈ goodSupps, (event.filter (fun U => supportSub U = S)).card := by
          refine Finset.card_eq_sum_card_fiberwise (f := supportSub) fun U hU => ?_
          have hUmix : U ∈ mixed := (Finset.mem_filter.mp hU).1
          have hUcond : (2 * ((a - host U : ℕ) : ℝ) - mu) / Real.sqrt mu ≤ y := (Finset.mem_filter.mp hU).2
          have hSmix : supportSub U ∈ mixSet :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hUmix).2⟩
          refine Finset.mem_inter.mpr ⟨?_, hSmix⟩
          by_cases hbad : badDefects (defectsSet (supportSub U))
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
            have hsand := (hhost_sand U hUmix hbad).1
            have hle : (((defectsSet (supportSub U)).card : ℝ) - mu) / Real.sqrt mu ≤
                (2 * ((a - host U : ℕ) : ℝ) - mu) / Real.sqrt mu :=
              div_le_div_of_nonneg_right (by linarith) (le_of_lt hsq_pos)
            linarith
        rw [h1]
        refine Finset.sum_le_sum fun S _ => Finset.card_le_card fun U hU => ?_
        simp only [event, mixed, Finset.mem_filter] at hU ⊢
        exact ⟨hU.1.1.1, hU.2⟩
      have hmul_le : (B : ℝ) * (event.card : ℝ) ≤ ∑ S ∈ goodSupps, actualFn k S := by
        simp only [actualFn, ← Finset.mul_sum]
        have hcast : (event.card : ℝ) ≤ ∑ S ∈ goodSupps, ((layer.filter (fun U => supportSub U = S)).card : ℝ) := by
          exact_mod_cast hfib_le
        exact mul_le_mul_of_nonneg_left hcast (le_of_lt (hB_pos k))
      have hact_mod : ∑ S ∈ goodSupps, actualFn k S ≤ (∑ S ∈ goodSupps, modelFn k S) + Err k := by
        have h1 : (∑ S ∈ goodSupps, actualFn k S) - (∑ S ∈ goodSupps, modelFn k S) ≤ Err k := by
          rw [← Finset.sum_sub_distrib]
          calc ∑ S ∈ goodSupps, (actualFn k S - modelFn k S)
              ≤ ∑ S ∈ goodSupps, |actualFn k S - modelFn k S| :=
                Finset.sum_le_sum fun S _ => le_abs_self _
            _ ≤ Err k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
        linarith
      have hmod_run : ∑ S ∈ goodSupps, modelFn k S =
          ∑ S ∈ goodSupps, (s - 1) ^ (runsCard S) / s ^ 4 :=
        Finset.sum_congr rfl fun S hS => hmodel_mixed k S (Finset.mem_filter.mp (Finset.mem_inter.mp hS).2).2
      have hsub_u : ∑ S ∈ goodSupps, (s - 1) ^ (runsCard S) / s ^ 4 ≤
          (∑ S ∈ tailSet, (s - 1) ^ (runsCard S) / s ^ 4) +
          (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) := by
        have h1 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left : goodSupps ⊆ tailSet ∪ badSet)
          (fun S _ _ => hrun_nn S)
        have h2 := Finset.sum_union_inter (s₁ := tailSet) (s₂ := badSet) (f := fun S => (s - 1) ^ (runsCard S) / s ^ 4)
        have h3 : 0 ≤ ∑ S ∈ tailSet ∩ badSet, (s - 1) ^ (runsCard S) / s ^ 4 :=
          Finset.sum_nonneg fun S _ => hrun_nn S
        linarith
      linarith
    have hev_card_lo :
        (∑ S ∈ tailSetLo, (s - 1) ^ (runsCard S) / s ^ 4) -
        (∑ S ∈ nonMixSet, (s - 1) ^ (runsCard S) / s ^ 4) -
        (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) - Err k ≤ (B : ℝ) * (event.card : ℝ) := by
      let goodLo := (tailSetLo \ badSet) ∩ mixSet
      have hfib_ge : ∑ S ∈ goodLo, (layer.filter (fun U => supportSub U = S)).card ≤ event.card := by
        have h1 : ∑ S ∈ goodLo, (layer.filter (fun U => supportSub U = S)).card =
            ∑ S ∈ goodLo, (event.filter (fun U => supportSub U = S)).card := by
          refine Finset.sum_congr rfl fun S hS => congrArg Finset.card ?_
          have hS1 := (Finset.mem_inter.mp hS).1
          have hSlo : (((defectsSet S).card : ℝ) - mu) / Real.sqrt mu ≤ y - η :=
            (Finset.mem_filter.mp (Finset.mem_sdiff.mp hS1).1).2
          have hSnbad : ¬ badDefects (defectsSet S) := by
            intro hbad
            exact (Finset.mem_sdiff.mp hS1).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
          have hSmix : mixedSupp S := (Finset.mem_filter.mp (Finset.mem_inter.mp hS).2).2
          ext U
          simp only [event, mixed, Finset.mem_filter]
          constructor
          · rintro ⟨hU, rfl⟩
            have hUmix : U ∈ mixed := Finset.mem_filter.mpr ⟨hU, hSmix⟩
            have hsand := (hhost_sand U hUmix hSnbad).2
            have hle : (2 * ((a - host U : ℕ) : ℝ) - mu) / Real.sqrt mu ≤
                (((defectsSet (supportSub U)).card : ℝ) - mu) / Real.sqrt mu + 8 / Real.sqrt mu := by
              rw [← add_div]
              exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hsq_pos)
            exact ⟨⟨⟨hU, hSmix⟩, by linarith⟩, rfl⟩
          · rintro ⟨⟨⟨hU, _⟩, _⟩, rfl⟩
            exact ⟨hU, rfl⟩
        rw [h1]
        have htot_fib : event.card = ∑ S : Finset (Fin n), (event.filter (fun U => supportSub U = S)).card :=
          Finset.card_eq_sum_card_fiberwise (f := supportSub) fun _ _ => Finset.mem_univ _
        rw [htot_fib]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hmul_ge : ∑ S ∈ goodLo, actualFn k S ≤ (B : ℝ) * (event.card : ℝ) := by
        simp only [actualFn, ← Finset.mul_sum]
        have hcast : ∑ S ∈ goodLo, ((layer.filter (fun U => supportSub U = S)).card : ℝ) ≤ (event.card : ℝ) := by
          exact_mod_cast hfib_ge
        exact mul_le_mul_of_nonneg_left hcast (le_of_lt (hB_pos k))
      have hact_mod : (∑ S ∈ goodLo, modelFn k S) - Err k ≤ ∑ S ∈ goodLo, actualFn k S := by
        have h1 : (∑ S ∈ goodLo, modelFn k S) - (∑ S ∈ goodLo, actualFn k S) ≤ Err k := by
          rw [← Finset.sum_sub_distrib]
          calc ∑ S ∈ goodLo, (modelFn k S - actualFn k S)
              ≤ ∑ S ∈ goodLo, |actualFn k S - modelFn k S| :=
                Finset.sum_le_sum fun S _ => by rw [abs_sub_comm]; exact le_abs_self _
            _ ≤ Err k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
        linarith
      have hmod_run : ∑ S ∈ goodLo, modelFn k S =
          ∑ S ∈ goodLo, (s - 1) ^ (runsCard S) / s ^ 4 :=
        Finset.sum_congr rfl fun S hS => hmodel_mixed k S (Finset.mem_filter.mp (Finset.mem_inter.mp hS).2).2
      have hcover : tailSetLo ⊆ goodLo ∪ nonMixSet ∪ badSet := by
        intro S hS
        by_cases hbad : badDefects (defectsSet S)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
        · by_cases hmix : mixedSupp S
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmix⟩⟩
            intro hb; exact hbad (Finset.mem_filter.mp hb).2
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmix⟩))
      have hsum_cov : ∑ S ∈ tailSetLo, (s - 1) ^ (runsCard S) / s ^ 4 ≤
          (∑ S ∈ goodLo, (s - 1) ^ (runsCard S) / s ^ 4) +
          (∑ S ∈ nonMixSet, (s - 1) ^ (runsCard S) / s ^ 4) +
          (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) := by
        have h1 := Finset.sum_le_sum_of_subset_of_nonneg hcover (fun S _ _ => hrun_nn S)
        have h2 := Finset.sum_union_inter (s₁ := goodLo ∪ nonMixSet) (s₂ := badSet)
          (f := fun S => (s - 1) ^ (runsCard S) / s ^ 4)
        have h3 := Finset.sum_union_inter (s₁ := goodLo) (s₂ := nonMixSet)
          (f := fun S => (s - 1) ^ (runsCard S) / s ^ 4)
        have h4 : 0 ≤ ∑ S ∈ (goodLo ∪ nonMixSet) ∩ badSet, (s - 1) ^ (runsCard S) / s ^ 4 :=
          Finset.sum_nonneg fun S _ => hrun_nn S
        have h5 : 0 ≤ ∑ S ∈ goodLo ∩ nonMixSet, (s - 1) ^ (runsCard S) / s ^ 4 :=
          Finset.sum_nonneg fun S _ => hrun_nn S
        linarith
      linarith
    have hpow_pos : (0 : ℝ) < s ^ (a - 2) := by positivity
    have hpow_ne : s ^ (a - 2) ≠ 0 := ne_of_gt hpow_pos
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt (hB_pos k)
    have hrat_eq : (event.card : ℝ) / (layer.card : ℝ) =
        (((B : ℝ) * (event.card : ℝ)) / s ^ (a - 2)) / (Zact k / s ^ (a - 2)) := by
      rw [← hlayer_eq k, div_div_div_cancel_right₀ hpow_ne, mul_div_mul_left _ _ hBne]
    rw [Real.dist_eq, hrat_eq]
    have hup_div : (((B : ℝ) * (event.card : ℝ)) / s ^ (a - 2)) / (Zact k / s ^ (a - 2)) < c * Φ y + ε := by
      have h1 : ((B : ℝ) * (event.card : ℝ)) / s ^ (a - 2) ≤
          (∑ S ∈ tailSet, (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) +
          (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) + Err k / s ^ (a - 2) := by
        rw [← add_div, ← add_div]
        exact div_le_div_of_nonneg_right hev_card_up (le_of_lt hpow_pos)
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt hzpos_k)
      simp only [tailSet, badSet, mu, n, a, s, t, d] at h2
      linarith
    have hlo_div : c * Φ y - ε < (((B : ℝ) * (event.card : ℝ)) / s ^ (a - 2)) / (Zact k / s ^ (a - 2)) := by
      have h1 :
          (∑ S ∈ tailSetLo, (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) -
          (∑ S ∈ nonMixSet, (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) -
          (∑ S ∈ badSet, (s - 1) ^ (runsCard S) / s ^ 4) / s ^ (a - 2) - Err k / s ^ (a - 2) ≤
          ((B : ℝ) * (event.card : ℝ)) / s ^ (a - 2) := by
        rw [← sub_div, ← sub_div, ← sub_div]
        exact div_le_div_of_nonneg_right hev_card_lo (le_of_lt hpow_pos)
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt hzpos_k)
      simp only [tailSetLo, nonMixSet, badSet, mu, n, a, s, t, d] at h2 ⊢
      have hη_eq : η = ε / 2 := rfl
      have hΦ_mul : c * Φ y - c * Φ (y - η) ≤ η := by nlinarith
      linarith
    rw [abs_lt]
    constructor <;> linarith

lemma main_L_lib_941_proof : (∀ T D : ℕ → ℕ, Filter.Tendsto T Filter.atTop Filter.atTop →
  (∀ k, 2 ≤ D k) →
  ∀ x : ℝ, Filter.Tendsto (fun k => 6*(T k : ℝ)/Real.sqrt ((2 : ℝ)^(D k))
    - 2*Real.log ((2 : ℝ)^(D k))) Filter.atTop (nhds x) →
  ∀ z : Option ℝ, Filter.Tendsto (fun k : ℕ =>
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let t := T k
  let d := D k
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
  let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
  let s := (2 : ℝ)^d
  let mu := (n : ℝ)/(1+Real.sqrt (s-1))
  let host := fun U : Submodule F W =>
    (spaces.filter (fun E : Submodule F W => U ≤ E)).sup (fun E => Module.finrank F E)
  let event : Finset (Submodule F W) := match z with
    | none => mixed
    | some y => mixed.filter (fun U =>
        (2*((a-host U : ℕ) : ℝ)-mu)/Real.sqrt mu ≤ y)
  (event.card : ℝ)/(layer.card : ℝ)) Filter.atTop
    (nhds ((Real.exp x/(2+Real.exp x)) * (match z with
      | none => 1
      | some y => ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal)))) := by
  intro T D hT hD2 x hx z
  have hcore := main_L_lib_941_core T D hT hD2 x hx z
  refine hcore.congr fun k => ?_
  have hfilt : ∀ {α : Type} {s₁ s₂ : Finset α} {p q : α → Prop}
      {d₁ : DecidablePred p} {d₂ : DecidablePred q},
      s₁ = s₂ → (∀ u, p u ↔ q u) → @Finset.filter α p d₁ s₁ = @Finset.filter α q d₂ s₂ := by
    intro α s₁ s₂ p q d₁ d₂ hs hpq
    subst hs; ext u; simp only [Finset.mem_filter, hpq]
  have hite : ∀ {α : Type} {p q : Prop} {d₁ : Decidable p} {d₂ : Decidable q} {u v : α},
      (p ↔ q) → @ite α p d₁ u v = @ite α q d₂ u v := by
    intro α p q d₁ d₂ u v hpq
    by_cases hp : p
    · have hq : q := hpq.mp hp; rw [ite_eq_left hp, ite_eq_left hq]
    · have hq : ¬ q := fun h => hp (hpq.mpr h); rw [ite_eq_right hp, ite_eq_right hq]
  have huniv_eq : ∀ {α : Type} (inst1 inst2 : Fintype α),
      @Finset.univ α inst1 = @Finset.univ α inst2 := by
    intro α inst1 inst2; ext u; simp
  have hsupp_eq : ∀ U : Submodule F2 (Space (6 * T k)),
      supportSub U = @Finset.filter _ (fun i : Fin (6 * T k) => ∃ x ∈ U, x i ≠ 0)
        (fun i => Classical.propDecidable _) Finset.univ := fun U => hfilt rfl fun _ => Iff.rfl
  have hgood_iff : ∀ U : Submodule F2 (Space (6 * T k)),
      ((∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U) ↔
      ((∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin (6 * T k),
        (@ite F2 (i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2))
          (Classical.propDecidable _) 1 0) * x i) = 0) ∧
       (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (6 * T k), x i * y (nextIdx i) = x (nextIdx i) * y i)) := by
    intro U
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun x hx b => ?_, h2⟩
    · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).symm.trans (h1 x hx b)
    · exact (Finset.sum_congr rfl fun i _ => congrArg (· * x i) (hite Iff.rfl)).trans (h1 x hx b)
  have hspaces_eq :
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
          (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U) _
        (@Finset.univ _ (instFinSub (6 * T k))) =
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
          (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin (6 * T k),
            (@ite F2 (i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2))
              (Classical.propDecidable _) 1 0) * x i) = 0) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (6 * T k), x i * y (nextIdx i) = x (nextIdx i) * y i))
        (fun _ => Classical.propDecidable _) (@Finset.univ _ (Fintype.ofFinite _)) :=
    hfilt (huniv_eq _ _) hgood_iff
  have hlayer_eq :
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k) _
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
            (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U) _
          (@Finset.univ _ (instFinSub (6 * T k)))) =
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
        (fun _ => Classical.propDecidable _)
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
            (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin (6 * T k),
              (@ite F2 (i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2))
                (Classical.propDecidable _) 1 0) * x i) = 0) ∧
            (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (6 * T k), x i * y (nextIdx i) = x (nextIdx i) * y i))
          (fun _ => Classical.propDecidable _) (@Finset.univ _ (Fintype.ofFinite _))) :=
    hfilt hspaces_eq fun _ => Iff.rfl
  have hmixed_eq :
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
          ∀ b : Fin 2, ∃ i ∈ supportSub U, i.val % 2 = b.val) _
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k) _
          (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
              (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U) _
            (@Finset.univ _ (instFinSub (6 * T k))))) =
      @Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
          ∀ b : Fin 2, ∃ i ∈ @Finset.filter _ (fun i : Fin (6 * T k) => ∃ x ∈ U, x i ≠ 0)
            (fun _ => Classical.propDecidable _) Finset.univ, i.val % 2 = b.val)
        (fun _ => Classical.propDecidable _)
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) => Module.finrank F2 U = D k)
          (fun _ => Classical.propDecidable _)
          (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
              (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin (6 * T k),
                (@ite F2 (i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2))
                  (Classical.propDecidable _) 1 0) * x i) = 0) ∧
              (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (6 * T k), x i * y (nextIdx i) = x (nextIdx i) * y i))
            (fun _ => Classical.propDecidable _) (@Finset.univ _ (Fintype.ofFinite _)))) :=
    hfilt hlayer_eq fun U => by rw [hsupp_eq U]
  have hhost_eq : ∀ U : Submodule F2 (Space (6 * T k)),
      (@Finset.filter _ (fun E => U ≤ E) _
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
            (∀ x ∈ U, ∀ b : Fin 4, (∑ i, hMat i b * x i) = 0) ∧ adjacentSub U) _
          (@Finset.univ _ (instFinSub (6 * T k))))).sup (fun E => Module.finrank F2 E) =
      (@Finset.filter _ (fun E => U ≤ E) (fun _ => Classical.propDecidable _)
        (@Finset.filter _ (fun U : Submodule F2 (Space (6 * T k)) =>
            (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin (6 * T k),
              (@ite F2 (i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2))
                (Classical.propDecidable _) 1 0) * x i) = 0) ∧
            (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin (6 * T k), x i * y (nextIdx i) = x (nextIdx i) * y i))
          (fun _ => Classical.propDecidable _) (@Finset.univ _ (Fintype.ofFinite _)))).sup
        (fun E => Module.finrank F2 E) := fun U =>
    congrArg (fun s => s.sup (fun E => Module.finrank F2 E)) (hfilt hspaces_eq fun _ => Iff.rfl)
  dsimp only
  cases z with
  | none =>
    dsimp only
    refine congrArg₂ (· / ·) (congrArg (fun s : Finset _ => (s.card : ℝ)) ?_)
      (congrArg (fun s : Finset _ => (s.card : ℝ)) ?_)
    · exact hmixed_eq
    · exact hlayer_eq
  | some y =>
    dsimp only
    refine congrArg₂ (· / ·) (congrArg (fun s : Finset _ => (s.card : ℝ)) ?_)
      (congrArg (fun s : Finset _ => (s.card : ℝ)) ?_)
    · exact hfilt hmixed_eq (fun U => by
        have hh := hhost_eq U
        exact iff_of_eq (congrArg (fun v : ℕ =>
          (2 * ((3 * T k - v : ℕ) : ℝ) - ((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) /
            Real.sqrt (((6 * T k : ℕ) : ℝ) / (1 + Real.sqrt ((2 : ℝ) ^ (D k) - 1))) ≤ y) hh))
    · exact hlayer_eq

end PEqualNP.Outside.L_lib_941_aux

theorem PEqualNP.Outside.L_lib_941 : (∀ T D : ℕ → ℕ, Filter.Tendsto T Filter.atTop Filter.atTop →
  (∀ k, 2 ≤ D k) →
  ∀ x : ℝ, Filter.Tendsto (fun k => 6*(T k : ℝ)/Real.sqrt ((2 : ℝ)^(D k))
    - 2*Real.log ((2 : ℝ)^(D k))) Filter.atTop (nhds x) →
  ∀ z : Option ℝ, Filter.Tendsto (fun k : ℕ =>
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let t := T k
  let d := D k
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
  let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
  let s := (2 : ℝ)^d
  let mu := (n : ℝ)/(1+Real.sqrt (s-1))
  let host := fun U : Submodule F W =>
    (spaces.filter (fun E : Submodule F W => U ≤ E)).sup (fun E => Module.finrank F E)
  let event : Finset (Submodule F W) := match z with
    | none => mixed
    | some y => mixed.filter (fun U =>
        (2*((a-host U : ℕ) : ℝ)-mu)/Real.sqrt mu ≤ y)
  (event.card : ℝ)/(layer.card : ℝ)) Filter.atTop
    (nhds ((Real.exp x/(2+Real.exp x)) * (match z with
      | none => 1
      | some y => ((ProbabilityTheory.gaussianReal 0 1) (Set.Iic y)).toReal)))) := by
  exact PEqualNP.Outside.L_lib_941_aux.main_L_lib_941_proof
