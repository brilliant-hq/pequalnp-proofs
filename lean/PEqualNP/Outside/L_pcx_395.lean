import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_395
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open PEqualNP.Expanders
def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)
def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial
def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open PEqualNP.Expanders
theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.LeftDegLe (permGraph σ) b := by
  intro i
  have hsub : (permGraph σ i).map Fin.castSuccEmb ⊆ Finset.univ.image (fun k => σ k i) := by
    intro x hx
    simp only [Finset.mem_map, permGraph, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb] at hx
    obtain ⟨j, ⟨k, hk⟩, rfl⟩ := hx
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  calc (permGraph σ i).card = ((permGraph σ i).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.image (fun k => σ k i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp
theorem permGraph_rightDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.RightDegLe (permGraph σ) b := by
  intro j
  have hsub : rightNbrs (permGraph σ) j ⊆
      Finset.univ.image (fun k => (σ k).symm j.castSucc) := by
    intro i hi
    simp only [rightNbrs, permGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [← hk]; simp⟩
  calc (rightNbrs (permGraph σ) j).card
      ≤ (Finset.univ.image (fun k => (σ k).symm j.castSucc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp
theorem permGraph_trap {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1)))
    (hT : 5 * T.card ≤ n + 1)
    (hbad : (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
    ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y := by
  set G := permGraph σ with hG
  set N := T.biUnion G with hN
  set U := uniqueNbrs G T with hU
  have he : ∑ i ∈ T, (G i).card = ∑ j ∈ N, (T.filter (fun i => j ∈ G i)).card := by
    have h1 : ∀ i ∈ T, (G i).card = ∑ j ∈ N, if j ∈ G i then 1 else 0 := by
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨i, hi, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  have hle8 : ∑ i ∈ T, (G i).card ≤ 8 * T.card := by
    have := Finset.sum_le_card_nsmul T (fun i => (G i).card) 8
      (fun i _ => permGraph_leftDegLe σ i)
    simpa [mul_comm] using this
  have hpt : ∀ j ∈ N, 2 ≤ (T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0 := by
    intro j hj
    have hpos : 0 < (T.filter (fun i => j ∈ G i)).card := by
      rw [hN, Finset.mem_biUnion] at hj
      obtain ⟨i, hi, hji⟩ := hj
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hji⟩⟩
    by_cases h1 : (T.filter (fun i => j ∈ G i)).card = 1
    · have : j ∈ U := by
        simp only [hU, uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      simp [this, h1]
    · split_ifs <;> omega
  have hsum : 2 * N.card ≤ ∑ i ∈ T, (G i).card + U.card := by
    have h2 : ∑ j ∈ N, 2 ≤ ∑ j ∈ N,
        ((T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← he] at h2
    have h3 : (N.filter (fun j => j ∈ U)).card ≤ U.card :=
      Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hNc : N.card + 1 ≤ 5 * T.card := by omega
  set Y0 := N.map Fin.castSuccEmb ∪ {Fin.last n} with hY0
  have hY0c : Y0.card ≤ 5 * T.card := by
    calc Y0.card ≤ (N.map Fin.castSuccEmb).card + ({Fin.last n} : Finset _).card :=
          Finset.card_union_le _ _
      _ = N.card + 1 := by simp
      _ ≤ 5 * T.card := hNc
  obtain ⟨Y, hY0Y, hYc⟩ := Finset.exists_superset_card_eq hY0c (by simpa using hT)
  refine ⟨Y, hYc, fun k x hx => hY0Y ?_⟩
  induction h : σ k x using Fin.lastCases with
  | last => simp [hY0]
  | cast j =>
    have hj : j ∈ N := by
      rw [hN, Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      simp only [hG, permGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, h⟩
    simp only [hY0, Finset.mem_union, Finset.mem_map, Fin.coe_castSuccEmb]
    exact Or.inl ⟨j, hj, rfl⟩
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open Finset
theorem permCount : PermCountStmt := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, mem_filter, mem_univ, true_and] at hσ
    simp only [t, mem_filter, mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)
  have ht : #t ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this
  have hfib : ∀ g ∈ t, #{σ ∈ S | f σ = g} ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty {σ ∈ S | f σ = g} with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ ({σ ∈ S | f σ = g} : Finset _)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (mem_filter.mp σ.2).2
        have h2 : σ.1 a = σ₀ a := by
          have e := congrFun (h1.trans hσ₀g.symm) ⟨a, ha'⟩
          simpa [f] using e
        simp [Equiv.Perm.mul_apply, h2]⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [F] using this
    have := Fintype.card_le_of_injective F hF
    rw [hcardP, Fintype.card_coe] at this
    exact this
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  calc #S ≤ (Fintype.card α - T.card).factorial * #t := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open Finset
lemma arith_choose_le (N r : ℕ) (hr : 0 < r) : (N.choose r : ℝ) ≤ (3 * N / r) ^ r := by
  have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r N
  have h2 : (r : ℝ) ^ r / r.factorial ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
  have h3 : Real.exp r ≤ 3 ^ r := by
    have : Real.exp (r : ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
    rw [this]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hrr : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := h1
    _ = (N : ℝ) ^ r / (r : ℝ) ^ r * ((r : ℝ) ^ r / r.factorial) := by field_simp
    _ ≤ (N : ℝ) ^ r / (r : ℝ) ^ r * 3 ^ r := by gcongr; exact h2.trans h3
    _ = (3 * N / r) ^ r := by rw [div_pow, mul_pow]; ring
lemma arith_ratio_le (N t : ℕ) (ht : 1 ≤ t) (hN : 2 * t ≤ N) :
    ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ) ≤ (10 * t / N) ^ t := by
  have hnum : ((5 * t).descFactorial t : ℝ) ≤ ((5 * t : ℕ) : ℝ) ^ t := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hden0 : ((N + 1 - t : ℕ) : ℝ) ^ t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsub : (N : ℝ) / 2 ≤ ((N + 1 - t : ℕ) : ℝ) := by
    have hle : t ≤ N + 1 := by omega
    rw [Nat.cast_sub hle]
    have : (2 * t : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hden : ((N : ℝ) / 2) ^ t ≤ (N.descFactorial t : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hsub t).trans hden0
  calc ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ)
      ≤ ((5 * t : ℕ) : ℝ) ^ t / ((N : ℝ) / 2) ^ t :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (10 * t / N) ^ t := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
        ring
lemma arith_term_le (n t : ℕ) (ht : 1 ≤ t) (hts : t * 100000 ≤ n) :
    ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 ≤
      (1 / 4 : ℝ) ^ t := by
  have htpos : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hN : ((n + 1 : ℕ) : ℝ) ≥ 100000 * t := by
    have : t * 100000 ≤ n + 1 := by omega
    have h : ((t * 100000 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := arith_choose_le (n + 1) t (by omega)
  have h2 := arith_choose_le (n + 1) (5 * t) (by omega)
  have h3 := arith_ratio_le (n + 1) t ht (by omega)
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hratio0 : (0 : ℝ) ≤ ((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ) := by
    positivity
  have h5 : ((5 * t : ℕ) : ℝ) = 5 * (t : ℝ) := by push_cast; ring
  rw [h5] at h2
  have hbase : (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 = 23328000 * t ^ 2 / N ^ 2 := by
    field_simp
    ring
  have hq : (23328000 : ℝ) * t ^ 2 / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) ≤ (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 := by positivity
  calc ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ (3 * N / t) ^ t * (3 * N / (5 * t)) ^ (5 * t) * ((10 * t / N) ^ t) ^ 8 := by
        gcongr
    _ = ((3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8) ^ t := by
        rw [pow_mul (3 * N / (5 * t)) 5 t, ← pow_mul (10 * t / N) t 8, mul_comm t 8,
          pow_mul (10 * t / N) 8 t, mul_pow, mul_pow]
    _ ≤ (1 / 4 : ℝ) ^ t := by
        rw [hbase] at hq0 ⊢
        exact pow_le_pow_left₀ hq0 hq t
theorem arith : ArithStmt := by
  refine ⟨100000, 0, by norm_num, fun n _ => ?_⟩
  calc ∑ t ∈ Finset.Icc 1 (n / 100000),
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ ∑ t ∈ Finset.Icc 1 (n / 100000), (1 / 4 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Icc] at ht
        exact arith_term_le n t ht.1 ((Nat.le_div_iff_mul_le (by norm_num)).1 ht.2)
    _ = ∑ t ∈ Finset.Ico 1 (n / 100000 + 1), (1 / 4 : ℝ) ^ t := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 / 4 : ℝ) ^ 1 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ < 1 := by norm_num
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open PEqualNP.Expanders
theorem expander_of_parts (hP : PermCountStmt) (hA : ArithStmt)
    (hL : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.LeftDegLe (permGraph σ) b)
    (hR : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.RightDegLe (permGraph σ) b)
    (hT : ∀ {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1))),
      5 * T.card ≤ n + 1 →
      (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card →
      ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y) :
    ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
        PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 := by
  classical
  obtain ⟨s₀, n₀, h5, hsum⟩ := hA
  refine ⟨8, s₀, n₀, by omega, ?_⟩
  intro n hn
  have hs1 := hsum n hn
  have hsn : 5 * (n / s₀) ≤ n := by
    have h1 := Nat.div_mul_le_self n s₀
    have h2 : 5 * (n / s₀) ≤ n / s₀ * s₀ := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (n / s₀) h5
    omega
  set s := n / s₀ with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, hL σ, hR σ, hσ⟩
  by_contra hno
  push Not at hno
  let A : Finset (Fin (n + 1)) → Finset (Fin (n + 1)) → Finset (Equiv.Perm (Fin (n + 1))) :=
    fun T Y => Finset.univ.filter (fun τ => ∀ x ∈ T, τ x ∈ Y)
  let U : Finset (Fin 8 → Equiv.Perm (Fin (n + 1))) :=
    (Finset.Icc 1 s).biUnion (fun t =>
      (Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun T =>
        (Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun Y =>
          Fintype.piFinset (fun _ : Fin 8 => A T Y))))
  have hsub : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))) ⊆ U := by
    intro σ _
    have hbad := hno σ
    unfold IsBdryExpander at hbad
    push Not at hbad
    obtain ⟨T, hTs, hTlt⟩ := hbad
    have ht1 : 1 ≤ T.card := by
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · rw [h0] at hTlt; omega
      · exact h0
    obtain ⟨Y, hYc, hY⟩ := hT σ T (by omega) hTlt
    simp only [U, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Fintype.mem_piFinset]
    refine ⟨T.card, ⟨ht1, hTs⟩, T, ⟨Finset.subset_univ _, rfl⟩, Y,
      ⟨Finset.subset_univ _, hYc⟩, ?_⟩
    intro k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun x hx => hY k x hx
  have hAcard : ∀ t, ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
      ∀ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
      (A T Y).card ≤ (5 * t).descFactorial t * (n + 1 - t).factorial := by
    intro t T hT' Y hY'
    rw [Finset.mem_powersetCard] at hT' hY'
    have h := hP (Fin (n + 1)) T Y
    rw [hT'.2, hY'.2, Fintype.card_fin] at h
    convert h
  have hUcard : U.card ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t * ((n + 1).choose (5 * t) *
      ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
          (n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
          apply Finset.sum_le_sum
          intro T hT'
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
                ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
                apply Finset.sum_le_sum
                intro Y hY'
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                exact Nat.pow_le_pow_left (hAcard t T hT' Y hY') 8
            _ = _ := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  have hcardΩ : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))).card =
      ((n + 1).factorial) ^ 8 := by
    rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  have hle : ((n + 1).factorial) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t *
      ((n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) :=
    hcardΩ ▸ (Finset.card_le_card hsub).trans hUcard
  have hleR : (((n + 1).factorial : ℕ) : ℝ) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) := by
    exact_mod_cast hle
  have hid : ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) =
      (((n + 1).factorial : ℕ) : ℝ) ^ 8 * ∑ t ∈ Finset.Icc 1 s,
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htn : t ≤ n + 1 := by omega
    have hEF : ((n + 1 - t).factorial : ℝ) * ((n + 1).descFactorial t : ℝ) =
        (((n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial htn
    have hE : ((n + 1).descFactorial t : ℝ) ≠ 0 := by
      have : (n + 1).descFactorial t ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    rw [← hEF]
    field_simp
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) ^ 8 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  have hlt := mul_lt_mul_of_pos_left hs1 hpos
  rw [hid] at hleR
  linarith
end PCXLib.Helpers
end
section
namespace PCXLib
open PEqualNP.ProofComplexity
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)
end PCXLib
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
variable {σ τ : Type}
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)
theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]
theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this
theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)
theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this
theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide
theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers.BoolVanish
open MvPolynomial PEqualNP.ProofComplexity PCXLib.Helpers
variable {σ : Type}
noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v
noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a
theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]
theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this
theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]
theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v
end PCXLib.Helpers.BoolVanish
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
variable {σ : Type} [Countable σ]
noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)
def MonoLt (b a : σ →₀ ℕ) : Prop := monoKey b < monoKey a
theorem monoKey_injective : Function.Injective (monoKey (σ := σ)) := by
  intro a b h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [monoKey, ofLex_toLex] at h2
  exact Classical.choose_spec (Countable.exists_injective_nat (σ →₀ ℕ)) h2
theorem monoLt_of_degree_lt {a b : σ →₀ ℕ} (h : b.degree < a.degree) : MonoLt b a := by
  unfold MonoLt monoKey
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
theorem degree_le_of_monoLt {a b : σ →₀ ℕ} (h : MonoLt b a) : b.degree ≤ a.degree := by
  unfold MonoLt monoKey at h
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le
theorem monoLt_wellFounded : WellFounded (MonoLt (σ := σ)) :=
  InvImage.wf monoKey wellFounded_lt
theorem monoLt_trans {a b c : σ →₀ ℕ} (h1 : MonoLt a b) (h2 : MonoLt b c) : MonoLt a c :=
  lt_trans (α := ℕ ×ₗ ℕ) h1 h2
def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}
noncomputable def echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {a | IsStd U a}
omit [Countable σ] in
theorem echelon_restrictSupport_le {s : Set (σ →₀ ℕ)}
    {P : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    (h : ∀ b ∈ s, monomial b (1 : ZMod 2) ∈ P) : restrictSupport (ZMod 2) s ≤ P := by
  rw [restrictSupport_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb
theorem echelon_disjoint (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Disjoint (echelonStd U) U := by
  classical
  rw [Submodule.disjoint_def]
  intro h hS hU
  by_contra hne
  have hsupp : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image h.support monoKey hsupp
  have hstd : IsStd U a := ((mem_restrictSupport_iff (R := ZMod 2)).1 hS) ha
  apply hstd
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hc : h.coeff a = 1 := key _ (mem_support_iff.1 ha)
  have hw : h - monomial a 1 ∈ restrictSupport (ZMod 2) {b | MonoLt b a} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    have hb' : (h - monomial a 1).coeff b ≠ 0 := mem_support_iff.1 hb
    rw [coeff_sub, coeff_monomial] at hb'
    by_cases hab : a = b
    · subst hab
      simp [hc] at hb'
    · rw [if_neg hab, sub_zero] at hb'
      have hbS : b ∈ h.support := mem_support_iff.2 hb'
      exact lt_of_le_of_ne (hmax b hbS) (fun e => hab (monoKey_injective e).symm)
  have heq : monomial a (1 : ZMod 2) = h - (h - monomial a 1) := (sub_sub_cancel _ _).symm
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hU) (Submodule.mem_sup_right hw)
theorem echelon_monomial_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) :
    monomial a (1 : ZMod 2) ∈
      U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
  induction a using (monoLt_wellFounded (σ := σ)).induction
  rename_i a ih
  by_cases hs : IsStd U a
  · apply Submodule.mem_sup_right
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl hs)
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  · have hmem : monomial a (1 : ZMod 2) ∈ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} :=
      Classical.byContradiction fun h => hs h
    have hle : U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} ≤
        U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
      refine sup_le le_sup_left ?_
      refine echelon_restrictSupport_le ?_
      intro b hb
      refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
        (ih b hb)
      intro c hc
      rcases hc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr (monoLt_trans hc hb)
    exact hle hmem
theorem echelon_le_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s) :
    restrictSupport (ZMod 2) s ≤ U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) s) := by
  refine echelon_restrictSupport_le ?_
  intro a ha
  refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
    (echelon_monomial_mem U a)
  intro b hb
  rcases hb with hb | hb
  · rw [hb]; exact ha
  · exact hs a ha b hb
theorem echelon_isCompl (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    IsCompl (echelonStd U) U := by
  refine ⟨echelon_disjoint U, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro f _
  have hf : f ∈ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ)) := by
    rw [mem_restrictSupport_iff]
    exact Set.subset_univ _
  have h := echelon_le_of_downClosed U (s := Set.univ) (fun _ _ _ _ => trivial) hf
  have hle : U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ))) ≤
      echelonStd U ⊔ U :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  exact hle h
noncomputable def nf (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Submodule.projection (echelonStd U) U (echelon_isCompl U)
theorem nf_mem_echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f ∈ echelonStd U :=
  Submodule.projection_apply_mem (echelon_isCompl U) f
theorem nf_sub_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : f - nf U f ∈ U :=
  Submodule.sub_projection_mem (echelon_isCompl U) f
theorem nf_support_isStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : ∀ a ∈ (nf U f).support, IsStd U a :=
  fun _ ha => ((mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_echelonStd U f)) ha
theorem nf_unique (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {f g : MvPolynomial σ (ZMod 2)} (hg : ∀ a ∈ g.support, IsStd U a) (hfg : f - g ∈ U) :
    nf U f = g := by
  have hgS : g ∈ echelonStd U := (mem_restrictSupport_iff (R := ZMod 2)).2 fun a ha => hg a ha
  have h1 : nf U f - g ∈ echelonStd U := Submodule.sub_mem _ (nf_mem_echelonStd U f) hgS
  have h2 : nf U f - g ∈ U := by
    have h3 := Submodule.sub_mem _ hfg (nf_sub_mem U f)
    rwa [sub_sub_sub_cancel_left] at h3
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (echelon_disjoint U)) _ h1 h2)
theorem nf_eq_zero_iff (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f = 0 ↔ f ∈ U := by
  constructor
  · intro h
    have h3 := nf_sub_mem U f
    rwa [h, sub_zero] at h3
  · intro h
    exact nf_unique U (by simp) (by rwa [sub_zero])
theorem nf_mem_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s)
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ restrictSupport (ZMod 2) s) :
    nf U f ∈ restrictSupport (ZMod 2) s := by
  obtain ⟨u, hu, g, hg, hug⟩ := Submodule.mem_sup.1 (echelon_le_of_downClosed U hs hf)
  have hgs := Submodule.mem_inf.1 hg
  have hnf : nf U f = g := by
    refine nf_unique U (fun c hc => (mem_restrictSupport_iff (R := ZMod 2)).1 hgs.1 hc) ?_
    rw [← hug, add_sub_cancel_right]
    exact hu
  rw [hnf]
  exact hgs.2
theorem nf_monomial_support (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) : ∀ b ∈ (nf U (monomial a 1)).support, b = a ∨ MonoLt b a := by
  have hd : ∀ c ∈ {b | b = a ∨ MonoLt b a}, ∀ b, MonoLt b c → b ∈ {b | b = a ∨ MonoLt b a} := by
    intro c hc b hb
    rcases hc with hc | hc
    · rw [hc] at hb
      exact Or.inr hb
    · exact Or.inr (monoLt_trans hb hc)
  have hm : monomial a (1 : ZMod 2) ∈ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a} :=
    (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  intro b hb
  exact (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hm) hb
omit [Countable σ] in
theorem echelon_sum_eq_degree (b : σ →₀ ℕ) : (b.sum fun _ e => e) = b.degree := by
  rw [Finsupp.degree_apply]
  rfl
theorem totalDegree_nf_le (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : (nf U f).totalDegree ≤ f.totalDegree := by
  have hd : ∀ c ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree}, ∀ b, MonoLt b c →
      b ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} :=
    fun _ hc _ hb => le_trans (degree_le_of_monoLt hb) hc
  have hf : f ∈ restrictSupport (ZMod 2) {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    exact (echelon_sum_eq_degree b).symm.trans_le (le_totalDegree hb)
  have hg := (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hf)
  unfold totalDegree
  exact Finset.sup_le fun b hb => (echelon_sum_eq_degree b).trans_le (hg hb)
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H
open Classical in
noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)
open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]
def SuppClosed (s : ℕ) (K : Finset (Fin N)) (S : Finset (Fin m)) : Prop :=
  ∀ T : Finset (Fin m), S ⊂ T → T.card ≤ s → ¬ uniqueNbrs G T ⊆ K ∪ S.biUnion G
lemma mem_uniqueNbrs {T : Finset (Fin m)} {j : Fin N} :
    j ∈ uniqueNbrs G T ↔ (T.filter (fun i => j ∈ G i)).card = 1 := by
  simp [uniqueNbrs]
theorem uniqueNbrs_union_subset (A B : Finset (Fin m)) :
    uniqueNbrs G (A ∪ B) ⊆ uniqueNbrs G A ∪ uniqueNbrs G B := by
  intro j hj
  rw [mem_uniqueNbrs, Finset.filter_union] at hj
  rw [Finset.mem_union, mem_uniqueNbrs, mem_uniqueNbrs]
  by_cases hA : (A.filter (fun i => j ∈ G i)).card = 0
  · right
    rw [Finset.card_eq_zero] at hA
    rw [hA, Finset.empty_union] at hj
    exact hj
  · left
    have h1 : (A.filter (fun i => j ∈ G i)).card ≤ 1 :=
      hj ▸ Finset.card_le_card Finset.subset_union_left
    omega
lemma two_mul_card_le_of_containedIn {s : ℕ} (hG : IsBdryExpander G s 2)
    {H : Finset (Fin N)} {T : Finset (Fin m)} (hT : ContainedIn G s H T) :
    2 * T.card ≤ H.card :=
  (hG T hT.1).trans (Finset.card_le_card hT.2)
lemma containedIn_union {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) {A B : Finset (Fin m)} (hA : ContainedIn G s H A)
    (hB : ContainedIn G s H B) : ContainedIn G s H (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · have h1 := two_mul_card_le_of_containedIn G hG hA
    have h2 := two_mul_card_le_of_containedIn G hG hB
    have h3 := Finset.card_union_le A B
    omega
  · exact (uniqueNbrs_union_subset G A B).trans (Finset.union_subset hA.2 hB.2)
lemma containedIn_empty (s : ℕ) (H : Finset (Fin N)) :
    ContainedIn G s H (∅ : Finset (Fin m)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [uniqueNbrs] at hj
theorem supp_containedIn {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : ContainedIn G s H (supp G s H) := by
  have key : ∀ U : Finset (Fin m), U ⊆ supp G s H →
      ∃ T, U ⊆ T ∧ T ⊆ supp G s H ∧ ContainedIn G s H T := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _, containedIn_empty G s H⟩
    | insert i U _ ih =>
      intro hU
      obtain ⟨T, hUT, hTS, hT⟩ := ih ((Finset.subset_insert i U).trans hU)
      have hi : i ∈ supp G s H := hU (Finset.mem_insert_self i U)
      obtain ⟨Ti, hiTi, hTi⟩ := (mem_supp G).mp hi
      have hTiS : Ti ⊆ supp G s H := fun k hk =>
        (mem_supp G).mpr ⟨Ti, hk, hTi⟩
      refine ⟨Ti ∪ T, ?_, Finset.union_subset hTiS hTS, containedIn_union G hG hH hTi hT⟩
      exact Finset.insert_subset (Finset.mem_union_left _ hiTi)
        (hUT.trans Finset.subset_union_right)
  obtain ⟨T, h1, h2, hT⟩ := key (supp G s H) (Finset.Subset.refl _)
  rw [← Finset.Subset.antisymm h2 h1]
  exact hT
theorem two_mul_card_supp_le {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : 2 * (supp G s H).card ≤ H.card :=
  two_mul_card_le_of_containedIn G hG (supp_containedIn G hG hH)
lemma mem_uniqueNbrs_of_subset {S T : Finset (Fin m)} (hST : S ⊆ T) {j : Fin N}
    (hj : j ∈ uniqueNbrs G T) (hjS : j ∈ S.biUnion G) : j ∈ uniqueNbrs G S := by
  rw [mem_uniqueNbrs] at hj ⊢
  obtain ⟨i, hiS, hji⟩ := Finset.mem_biUnion.mp hjS
  have h1 : (S.filter (fun i => j ∈ G i)).card ≤ 1 :=
    hj ▸ Finset.card_le_card (Finset.filter_subset_filter _ hST)
  have h2 : 0 < (S.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hji⟩⟩
  omega
theorem suppClosed_supp {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : SuppClosed G s H (supp G s H) := by
  intro T hST hT hsub
  have hS := supp_containedIn G hG hH
  have hTH : uniqueNbrs G T ⊆ H := by
    intro j hj
    rcases Finset.mem_union.mp (hsub hj) with h | h
    · exact h
    · exact hS.2 (mem_uniqueNbrs_of_subset G hST.subset hj h)
  have hTS : T ⊆ supp G s H := fun k hk =>
    (mem_supp G).mpr ⟨T, hk, hT, hTH⟩
  exact (Finset.not_subset.mp hST.2).elim fun k ⟨hkT, hkS⟩ => hkS (hTS hkT)
theorem SuppClosed.mono {s : ℕ} {K K' : Finset (Fin N)} {S : Finset (Fin m)}
    (h : SuppClosed G s K S) (hK : K' ⊆ K ∪ S.biUnion G) : SuppClosed G s K' S := by
  intro T hST hT hsub
  apply h T hST hT
  intro j hj
  rcases Finset.mem_union.mp (hsub hj) with h1 | h1
  · exact hK h1
  · exact Finset.mem_union_right _ h1
theorem SuppClosed.peel {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (h : SuppClosed G s K S) (hST : S ⊂ T) (hT : T.card ≤ s) :
    ∃ p ∈ T, p ∉ S ∧ ∃ j ∈ G p, j ∉ K ∧ j ∉ (T.erase p).biUnion G := by
  obtain ⟨j, hj, hjK⟩ := Finset.not_subset.mp (h T hST hT)
  rw [Finset.mem_union, not_or] at hjK
  obtain ⟨hjK, hjS⟩ := hjK
  rw [mem_uniqueNbrs, Finset.card_eq_one] at hj
  obtain ⟨p, hp⟩ := hj
  have hpmem : p ∈ T.filter (fun i => j ∈ G i) := hp ▸ Finset.mem_singleton_self p
  obtain ⟨hpT, hjp⟩ := Finset.mem_filter.mp hpmem
  refine ⟨p, hpT, ?_, j, hjp, hjK, ?_⟩
  · intro hpS
    exact hjS (Finset.mem_biUnion.mpr ⟨p, hpS, hjp⟩)
  · intro hj'
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj'
    obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
    have : q ∈ T.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hqT, hjq⟩
    rw [hp, Finset.mem_singleton] at this
    exact hqp this
lemma uniqueNbrs_singleton (i : Fin m) : uniqueNbrs G {i} = G i := by
  ext j
  rw [mem_uniqueNbrs]
  by_cases hj : j ∈ G i
  · simp [Finset.filter_singleton, hj]
  · simp [Finset.filter_singleton, hj]
theorem mem_supp_self {s : ℕ} (hs : 1 ≤ s) (i : Fin m) {H : Finset (Fin N)}
    (hi : G i ⊆ H) : i ∈ supp G s H :=
  (mem_supp G).mpr ⟨{i}, Finset.mem_singleton_self i,
    by simpa using hs, by rw [uniqueNbrs_singleton]; exact hi⟩
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1
noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap
theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl
def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)
def pigeonClause (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)
theorem locIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') : locIdeal G S ≤ locIdeal G S' := by
  intro f hf
  rw [mem_locIdeal] at hf ⊢
  exact fun α hα => hf α ⟨hα.1, fun i hi => hα.2 i (h hi)⟩
theorem X_mul_mem_locIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) : X v * f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]
theorem bool_mem_locIdeal (S : Finset (Fin m)) (v : GEdge G) :
    X v * X v + X v ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α _
  have h : ∀ x : ZMod 2, x * x + x = 0 := by decide
  simpa using h (α v)
theorem hole_mem_locIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.2 = e'.1.2) (h2 : e.1.1 ≠ e'.1.1) : X e * X e' ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  simpa using hα.1 e e' h1 h2
theorem pigeon_mem_locIdeal {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    clausePoly (pigeonClause G i) ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  obtain ⟨e, he, hαe⟩ := hα.2 i hi
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [clausePoly, map_prod]
  refine Finset.prod_eq_zero (i := ((e, true) : Literal (GEdge G))) ?_ ?_
  · simp [pigeonClause, he]
  · simp [hαe, h2]
theorem one_not_mem_locIdeal_empty : (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ locIdeal G ∅ := by
  rw [mem_locIdeal]
  intro h
  have h0 := h (fun _ => 0) ⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩
  rw [map_one] at h0
  exact one_ne_zero h0
theorem card_monoHoles_le (a : GEdge G →₀ ℕ) : (monoHoles G a).card ≤ a.degree := by
  refine Finset.card_image_le.trans ?_
  rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]
theorem localSat_card_pigeonClause (i : Fin m) : (pigeonClause G i).card = (G i).card := by
  refine Finset.card_bij (fun l _ => l.1.1.2) ?_ ?_ ?_
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2.1
    have := l.1.2
    rwa [h] at this
  · rintro ⟨⟨⟨p, j⟩, hpj⟩, b⟩ hl ⟨⟨⟨p', j'⟩, hpj'⟩, b'⟩ hl' hjj
    have h := (Finset.mem_filter.mp hl).2
    have h' := (Finset.mem_filter.mp hl').2
    simp only at h h' hjj
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    subst hjj
    rfl
  · intro j hj
    exact ⟨((⟨(i, j), hj⟩ : GEdge G), true), by simp [pigeonClause], rfl⟩
theorem totalDegree_pigeonClause (i : Fin m) :
    (clausePoly (pigeonClause G i)).totalDegree = (G i).card := by
  classical
  have hdeg : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 1 := by
    intro v
    rw [totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_X]; exact Nat.zero_lt_one), totalDegree_X]
  have hne : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)) ≠ 0 := by
    intro v h0
    have := hdeg v
    rw [h0, totalDegree_zero] at this
    exact Nat.zero_ne_one this
  rw [localSat_clausePoly_pigeonClause, ← localSat_card_pigeonClause]
  generalize pigeonClause G i = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (hne _) (Finset.prod_ne_zero_iff.mpr fun l _ => hne _),
      ih, hdeg, add_comm]
theorem monoHoles_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoHoles G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  have := l.1.2
  rwa [h] at this
theorem cnfSystem_graphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (graphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    ∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · refine Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩)
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]
theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]
noncomputable def localNF_zeroOut (K : Finset (Fin N)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 ∈ K then X e else 0
theorem localNF_zeroOut_monomial (K : Finset (Fin N)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (localNF_zeroOut G K) (monomial b c)
      = if monoHoles G b ⊆ K then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, localNF_zeroOut G K e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [localNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxK⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [localNF_zeroOut, ite_eq_right hxK, zero_pow (Finsupp.mem_support_iff.mp he)]
theorem localNF_zeroOut_mem {S : Finset (Fin m)} {K : Finset (Fin N)} (hK : S.biUnion G ⊆ K)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) :
    bind₁ (localNF_zeroOut G K) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_zeroOut G K e) * eval α (localNF_zeroOut G K e') = 0
    by_cases h : e.1.2 ∈ K
    · by_cases h' : e'.1.2 ∈ K
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact hα.1 e e' h1 h2
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [localNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.2 i hi
    have hmem : e.1.2 ∈ K := by
      refine hK (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [← he]
      exact e.2
    refine ⟨e, he, ?_⟩
    show eval α (localNF_zeroOut G K e) = 1
    rw [localNF_zeroOut, ite_eq_left hmem, eval_X, h1]
theorem localNF_zeroOut_eq (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (localNF_zeroOut G K) r
      = ∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => localNF_zeroOut_monomial G K b _
theorem localNF_support_sum_filter (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoHoles G b ⊆ K) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc
theorem nf_locIdeal_holes (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (locIdeal G S) (monomial a 1)).support,
      monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G := by
  have hsub := localNF_support_sum_filter G (monoHoles G a ∪ S.biUnion G)
    (nf (locIdeal G S) (monomial a 1))
  have heq : nf (locIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
          (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
          monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (locIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (locIdeal G S) (monomial a 1) b (Finset.mem_filter.mp (hsub hb)).1
    · have h := localNF_zeroOut_mem G (S := S) (K := monoHoles G a ∪ S.biUnion G)
        Finset.subset_union_right (nf_sub_mem (locIdeal G S) (monomial a 1))
      rw [map_sub, localNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        localNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
      (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
      monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2
noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e
noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)
theorem localNF_override_monomial_of_notMem (p : Fin m) {j : Fin N} {b : GEdge G →₀ ℕ}
    (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (localNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, localNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [localNF_override, ite_eq_right hne]
  rw [hprod, monomial_eq]
  rfl
theorem localNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hj : j ∈ G p)
    (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ locIdeal G (insert p S)) :
    bind₁ (localNF_override G p j) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_override G p j e) * eval α (localNF_override G p j e') = 0
    by_cases h : e.1.2 = j
    · have h' : e'.1.2 = j := h1 ▸ h
      by_cases hp : e.1.1 = p
      · have hp' : ¬ e'.1.1 = p := fun h3 => h2 (hp.trans h3.symm)
        rw [localNF_override, localNF_override, ite_eq_left h', ite_eq_right hp', map_zero,
          mul_zero]
      · rw [localNF_override, ite_eq_left h, ite_eq_right hp, map_zero, zero_mul]
    · have h' : ¬ e'.1.2 = j := fun h3 => h (h1.trans h3)
      rw [localNF_override, localNF_override, ite_eq_right h, ite_eq_right h', eval_X, eval_X]
      exact hα.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (localNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [localNF_override, ite_eq_left rfl, ite_eq_left rfl, map_one]
    · obtain ⟨e, he, h1⟩ := hα.2 i h
      have hne : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (localNF_override G p j e) = 1
      rw [localNF_override, ite_eq_right hne, eval_X, h1]
theorem localNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (localNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (localNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, e.1.2 = j ∧ ¬ e.1.1 = p
  · obtain ⟨e, he, h1, h2⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rw [localNF_override, ite_eq_left h1, ite_eq_right h2, zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz' : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, h, h2⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), localNF_override, ite_eq_left h,
        ite_eq_left (hz' e he h), one_pow]
    · rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        localNF_override, ite_eq_right h]
theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega
theorem localNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (localNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases localNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))
theorem nf_locIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoHoles G a) :
    nf (locIdeal G (insert p S)) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have _ := hp
  refine nf_unique (locIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (locIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hbj : j ∉ monoHoles G b := by
      intro h
      rcases Finset.mem_union.mp (nf_locIdeal_holes G S a b hb h) with h' | h'
      · exact ha h'
      · exact hjS h'
    have himg := congrArg (bind₁ (localNF_override G p j)) huw
    rw [map_add, localNF_override_monomial_of_notMem G p hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (localNF_override_mem G hj hjS hu)
      (localNF_override_mem_restrictSupport G p j hw)
  · exact locIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (locIdeal G S) (monomial a 1))
theorem nf_locIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoHoles G a ⊆ K) :
    nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_locIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0
noncomputable def funLocIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : funLocalSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap
theorem mem_funLocIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ funLocIdeal G S ↔ ∀ α, funLocalSat G S α → eval α f = 0 := by
  simp only [funLocIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl
theorem locIdeal_le_funLocIdeal (S : Finset (Fin m)) : locIdeal G S ≤ funLocIdeal G S := by
  intro f hf
  rw [mem_locIdeal] at hf
  rw [mem_funLocIdeal]
  exact fun α hα => hf α hα.1
theorem funLocIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') :
    funLocIdeal G S ≤ funLocIdeal G S' := by
  intro f hf
  rw [mem_funLocIdeal] at hf ⊢
  exact fun α hα => hf α ⟨⟨hα.1.1, fun i hi => hα.1.2 i (h hi)⟩, hα.2⟩
theorem X_mul_mem_funLocIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    X v * f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]
theorem fun_mem_funLocIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.1 = e'.1.1) (h2 : e.1.2 ≠ e'.1.2) : X e * X e' ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal]
  intro α hα
  simpa using hα.2 e e' h1 h2
theorem one_not_mem_funLocIdeal_empty :
    (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ funLocIdeal G ∅ := by
  rw [mem_funLocIdeal]
  intro h
  have h0 := h (fun _ => 0)
    ⟨⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩, fun _ _ _ _ => mul_zero _⟩
  rw [map_one] at h0
  exact one_ne_zero h0
def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)
def monoNbrs (a : GEdge G →₀ ℕ) : Finset (Fin N) := (monoPigeons G a).biUnion G
theorem card_monoNbrs_le {d : ℕ} (hd : LeftDegLe G d) (a : GEdge G →₀ ℕ) :
    (monoNbrs G a).card ≤ d * a.degree := by
  have h1 : (monoNbrs G a).card ≤ (monoPigeons G a).card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hd i
  have h2 : (monoPigeons G a).card ≤ a.degree := by
    refine Finset.card_image_le.trans ?_
    rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  calc (monoNbrs G a).card ≤ (monoPigeons G a).card * d := h1
    _ ≤ a.degree * d := Nat.mul_le_mul_right d h2
    _ = d * a.degree := Nat.mul_comm _ _
theorem monoNbrs_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoNbrs G (a + Finsupp.single v 1) = monoNbrs G a ∪ G v.1.1 := by
  ext j
  simp only [monoNbrs, monoPigeons, Finset.mem_biUnion, Finset.mem_image, Finset.mem_union,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hj⟩
    by_cases hev : e = v
    · exact Or.inr (hev ▸ hj)
    · refine Or.inl ⟨e.1.1, ⟨e, ?_, rfl⟩, hj⟩
      rwa [Finsupp.single_apply, ite_eq_right (Ne.symm hev), add_zero] at he
  · rintro (⟨i, ⟨e, he, rfl⟩, hj⟩ | hj)
    · exact ⟨e.1.1, ⟨e, fun h0 => he (Nat.eq_zero_of_add_eq_zero_right h0), rfl⟩, hj⟩
    · exact ⟨v.1.1, ⟨v, by rw [Finsupp.single_eq_same]; omega, rfl⟩, hj⟩
theorem monoNbrs_subset_of_monoPigeons {a b : GEdge G →₀ ℕ} {S : Finset (Fin m)}
    (h : monoPigeons G b ⊆ monoPigeons G a ∪ S) :
    monoNbrs G b ⊆ monoNbrs G a ∪ S.biUnion G := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  rcases Finset.mem_union.mp (h hi) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
theorem monoNbrs_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoNbrs G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨i', hi', hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  rwa [h] at hji
theorem cnfSystem_funGraphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    (∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e') ∨
    ∃ e e' : GEdge G, e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with hC | ⟨e, e', h1, h2, rfl⟩
    · rcases cnfSystem_graphPHP_cases G (Or.inr ⟨C, hC, rfl⟩) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩))
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
noncomputable def funNF_zeroOut (Q : Finset (Fin m)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 ∈ Q then X e else 0
theorem funNF_zeroOut_monomial (Q : Finset (Fin m)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (funNF_zeroOut G Q) (monomial b c)
      = if monoPigeons G b ⊆ Q then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, funNF_zeroOut G Q e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [funNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxQ⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [funNF_zeroOut, ite_eq_right hxQ, zero_pow (Finsupp.mem_support_iff.mp he)]
theorem funNF_zeroOut_mem {S Q : Finset (Fin m)} (hQ : S ⊆ Q)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    bind₁ (funNF_zeroOut G Q) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have key : ∀ e e' : GEdge G, α e * α e' = 0 →
      eval α (funNF_zeroOut G Q e) * eval α (funNF_zeroOut G Q e') = 0 := by
    intro e e' h0
    by_cases h : e.1.1 ∈ Q
    · by_cases h' : e'.1.1 ∈ Q
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact h0
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [funNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    exact key e e' (hα.1.1 e e' h1 h2)
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.1.2 i hi
    have hmem : e.1.1 ∈ Q := by
      rw [he]
      exact hQ hi
    refine ⟨e, he, ?_⟩
    show eval α (funNF_zeroOut G Q e) = 1
    rw [funNF_zeroOut, ite_eq_left hmem, eval_X, h1]
  · intro e e' h1 h2
    exact key e e' (hα.2 e e' h1 h2)
theorem funNF_zeroOut_eq (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (funNF_zeroOut G Q) r
      = ∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => funNF_zeroOut_monomial G Q b _
theorem funNF_support_sum_filter (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoPigeons G b ⊆ Q) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc
theorem nf_funLocIdeal_pigeons (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support,
      monoPigeons G b ⊆ monoPigeons G a ∪ S := by
  have hsub := funNF_support_sum_filter G (monoPigeons G a ∪ S)
    (nf (funLocIdeal G S) (monomial a 1))
  have heq : nf (funLocIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
          (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
          monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (funLocIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (funLocIdeal G S) (monomial a 1) b
        (Finset.mem_filter.mp (hsub hb)).1
    · have h := funNF_zeroOut_mem G (S := S) (Q := monoPigeons G a ∪ S)
        Finset.subset_union_right (nf_sub_mem (funLocIdeal G S) (monomial a 1))
      rw [map_sub, funNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        funNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
      (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
      monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2
noncomputable def funNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else X e)
theorem funNF_override_monomial_of_notMem {p : Fin m} {j : Fin N} {b : GEdge G →₀ ℕ}
    (hp : p ∉ monoPigeons G b) (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (funNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, funNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne1 : e.1.1 ≠ p := fun h => hp (h ▸ Finset.mem_image_of_mem _ he)
    have hne2 : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [funNF_override, ite_eq_right hne1, ite_eq_right hne2]
  rw [hprod, monomial_eq]
  rfl
theorem funNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hp : p ∉ S)
    (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ funLocIdeal G (insert p S)) :
    bind₁ (funNF_override G p j) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have hval : ∀ e : GEdge G, eval α (funNF_override G p j e)
      = if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else α e) := by
    intro e
    rw [funNF_override]
    split_ifs <;> simp
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hj1 : e.1.2 = j
    · have hj2 : e'.1.2 = j := h1.symm.trans hj1
      by_cases hp1 : e.1.1 = p
      · have hp2 : ¬ e'.1.1 = p := fun h3 => h2 (hp1.trans h3.symm)
        rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
    · have hj2 : ¬ e'.1.2 = j := fun h3 => hj1 (h1.trans h3)
      by_cases hp1 : e.1.1 = p
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
      · by_cases hp2 : e'.1.1 = p
        · rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.1.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (funNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [hval, ite_eq_left rfl, ite_eq_left rfl]
    · obtain ⟨e, he, h1⟩ := hα.1.2 i h
      have hne1 : ¬ e.1.1 = p := by
        intro h3
        rw [he] at h3
        exact hp (h3 ▸ h)
      have hne2 : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (funNF_override G p j e) = 1
      rw [hval, ite_eq_right hne1, ite_eq_right hne2, h1]
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hp1 : e.1.1 = p
    · have hp2 : e'.1.1 = p := h1.symm.trans hp1
      by_cases hj1 : e.1.2 = j
      · have hj2 : ¬ e'.1.2 = j := fun h3 => h2 (hj1.trans h3.symm)
        rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
    · have hp2 : ¬ e'.1.1 = p := fun h3 => hp1 (h1.trans h3)
      by_cases hj1 : e.1.2 = j
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
      · by_cases hj2 : e'.1.2 = j
        · rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.2 e e' h1 h2
theorem funNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (funNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (funNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, (e.1.1 = p ∧ ¬ e.1.2 = j) ∨ (¬ e.1.1 = p ∧ e.1.2 = j)
  · obtain ⟨e, he, h⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [funNF_override, ite_eq_left h1, ite_eq_right h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
    · rw [funNF_override, ite_eq_right h1, ite_eq_left h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz1 : ∀ e ∈ c.support, e.1.1 = p → e.1.2 = j := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inl ⟨h, h2⟩⟩
    have hz2 : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inr ⟨h2, h⟩⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), funNF_override, ite_eq_left (hz2 e he h),
        ite_eq_left h, one_pow]
    · have hne : ¬ e.1.1 = p := fun h3 => h (hz1 e he h3)
      rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        funNF_override, ite_eq_right hne, ite_eq_right h]
theorem funNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (funNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases funNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))
theorem nf_funLocIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoNbrs G a) :
    nf (funLocIdeal G (insert p S)) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  refine nf_unique (funLocIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (funLocIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hloc := nf_funLocIdeal_pigeons G S a b hb
    have hbp : p ∉ monoPigeons G b := by
      intro h
      rcases Finset.mem_union.mp (hloc h) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨p, h', hj⟩)
      · exact hp h'
    have hbj : j ∉ monoHoles G b := by
      intro h
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp h
      have hje : j ∈ G e.1.1 := by
        rw [← hej]
        exact e.2
      rcases Finset.mem_union.mp (hloc (Finset.mem_image_of_mem _ he)) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
      · exact hjS (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
    have himg := congrArg (bind₁ (funNF_override G p j)) huw
    rw [map_add, funNF_override_monomial_of_notMem G hbp hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (funNF_override_mem G hp hj hjS hu)
      (funNF_override_mem_restrictSupport G p j hw)
  · exact funLocIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (funLocIdeal G S) (monomial a 1))
theorem nf_funLocIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoNbrs G a ⊆ K) :
    nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_funLocIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by
  have hsum : ∀ (v : σ) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ a ∈ s, a.degree + 1 ≤ D) →
      R (X v * ∑ a ∈ s, c a • monomial a 1) =
        R (X v * R (∑ a ∈ s, c a • monomial a 1)) := by
    intro v s c hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
    exact Finset.sum_congr rfl fun a ha => by rw [hmul v a (hs a ha)]
  have key : ∀ {p : MvPolynomial σ (ZMod 2)}, PCDerivable F D p → R p = 0 := by
    intro p h
    induction h with
    | ax hp hdeg => exact hax _ hp hdeg
    | zero => exact map_zero R
    | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
    | @mulX j p _ hdeg ih =>
      by_cases hp0 : p = 0
      · rw [hp0, mul_zero, map_zero]
      · have hdeg' : p.totalDegree + 1 ≤ D := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X] at hdeg
          omega
        have hp : p = ∑ a ∈ p.support, p.coeff a • monomial a (1 : ZMod 2) := by
          conv_lhs => rw [p.as_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
        have hs : ∀ a ∈ p.support, a.degree + 1 ≤ D := by
          intro a ha
          have h1 : a.degree ≤ p.totalDegree := le_totalDegree ha
          omega
        have h2 := hsum j p.support (fun a => p.coeff a) hs
        rw [← hp, ih, mul_zero, map_zero] at h2
        exact h2
  intro href
  exact hone (key href)
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
section Static
variable {σ : Type}
noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}
theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]
theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl
theorem X_mul_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} (j : σ)
    {g : MvPolynomial σ (ZMod 2)} (hg : g ∈ staticSpan F k) :
    X j * g ∈ staticSpan F (k + 1) := by
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    have heq : X j * (monomial a 1 * f) =
        monomial (a + Finsupp.single j 1) (1 : ZMod 2) * f := by
      rw [← monomial_one_mul_X]
      ring
    refine Submodule.subset_span ⟨a + Finsupp.single j 1, f, hf, ?_, heq⟩
    rw [← heq]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx
theorem pcDerivable_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p ∈ staticSpan F B := by
  induction h with
  | @ax p hp hdeg =>
    exact Submodule.subset_span ⟨0, p, hp, by simpa using hdeg, by simp⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    exact X_mul_mem_staticSpan j (hint k (Nat.lt_succ_self k) p ih (by omega))
theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))
theorem dual_eq_of_monomial_eq {k : ℕ}
    (f g : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : ∀ a : σ →₀ ℕ, a.degree ≤ k → f (monomial a 1) = g (monomial a 1))
    (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ k) : f p = g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm : monomial a (p.coeff a) = p.coeff a • monomial a (1 : ZMod 2) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, h a ((le_totalDegree ha).trans hp)]
theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]
theorem card_support_le_degree (a : σ →₀ ℕ) : a.support.card ≤ a.degree := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
end Static
section Matching
variable {m N : ℕ}
def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b
def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)
def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T
theorem isPartialMatching_empty : IsPartialMatching (∅ : Finset (Fin m × Fin N)) := by
  intro a ha
  simp at ha
theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h
theorem isPartialMatching_insert_iff {S : Finset (Fin m × Fin N)} (hS : IsPartialMatching S)
    {i : Fin m} (hrow : ∀ a ∈ S, a.1 ≠ i) (j : Fin N) :
    IsPartialMatching (insert (i, j) S) ↔ ∀ a ∈ S, a.2 ≠ j := by
  constructor
  · intro h a ha haj
    have := h a (Finset.mem_insert_of_mem ha) (i, j) (Finset.mem_insert_self _ _) (Or.inr haj)
    exact hrow a ha (by rw [this])
  · intro hcol a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · rfl
    · rcases hab with h | h
      · exact absurd h.symm (hrow b hb')
      · exact absurd h.symm (hcol b hb')
    · rcases hab with h | h
      · exact absurd h (hrow a ha')
      · exact absurd h (hcol a ha')
    · exact hS a ha' b hb' hab
theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)
open Classical in
noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0
theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h
theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h
theorem momentWeight_row_sum {z : Finset (Fin m × Fin N) → ZMod 2} {k : ℕ}
    (hz : MomentConsistent m N k z) (S : Finset (Fin m × Fin N))
    (hS : IsPartialMatching S → S.card < k) (i : Fin m) :
    ∑ j : Fin N, momentWeight z (insert (i, j) S) = momentWeight z S := by
  by_cases hM : IsPartialMatching S
  · by_cases hrow : ∀ a ∈ S, a.1 ≠ i
    · rw [momentWeight_of_matching hM, hz S hM (hS hM) i hrow, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : ∀ a ∈ S, a.2 ≠ j
      · rw [ite_eq_left hc,
          momentWeight_of_matching ((isPartialMatching_insert_iff hM hrow j).mpr hc)]
      · rw [ite_eq_right hc, momentWeight_of_not
          (fun h => hc ((isPartialMatching_insert_iff hM hrow j).mp h))]
    · push Not at hrow
      obtain ⟨⟨i', j0⟩, ha, hi⟩ := hrow
      simp only at hi
      subst hi
      rw [Finset.sum_eq_single j0]
      · rw [Finset.insert_eq_of_mem ha]
      · intro j _ hj
        exact momentWeight_of_not (not_isPartialMatching_insert ha hj)
      · intro h
        exact absurd (Finset.mem_univ _) h
  · rw [momentWeight_of_not hM]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact momentWeight_of_not fun h => hM (h.mono (Finset.subset_insert _ _))
noncomputable def momentFunctional (z : Finset (Fin m × Fin N) → ZMod 2) :
    MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (basisMonomials (Fin m × Fin N) (ZMod 2)).constr (ZMod 2)
    fun a => momentWeight z a.support
theorem momentFunctional_monomial (z : Finset (Fin m × Fin N) → ZMod 2)
    (a : Fin m × Fin N →₀ ℕ) :
    momentFunctional z (monomial a 1) = momentWeight z a.support := by
  have h := (basisMonomials (Fin m × Fin N) (ZMod 2)).constr_basis (ZMod 2)
    (fun a => momentWeight z a.support) a
  rw [coe_basisMonomials] at h
  exact h
theorem rowAxiom_totalDegree_le (i : Fin m) :
    ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [totalDegree_X]
theorem one_le_rowAxiom_totalDegree (hN : 1 ≤ N) (i : Fin m) :
    1 ≤ ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree := by
  by_contra hlt
  have h0 : ((∑ j : Fin N, X (i, j)) + 1 :
      MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have e0 := congrArg (eval (fun _ : Fin m × Fin N => (0 : ZMod 2))) h0
  have e1 := congrArg
    (eval (fun v : Fin m × Fin N => if v = (i, (⟨0, hN⟩ : Fin N)) then (1 : ZMod 2) else 0)) h0
  simp only [map_add, map_sum, eval_X, map_one, eval_C, Finset.sum_const_zero, zero_add] at e0 e1
  rw [← e0] at e1
  simp [Prod.mk.injEq] at e1
theorem monomial_one_mul_rowAxiom (a : Fin m × Fin N →₀ ℕ) (i : Fin m) :
    monomial a (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) =
      (∑ j : Fin N, monomial (a + Finsupp.single (i, j) 1) 1) + monomial a 1 := by
  rw [mul_add, mul_one, Finset.mul_sum]
  simp only [monomial_one_mul_X]
theorem momentFunctional_staticSpan (hN : 1 ≤ N) {z : Finset (Fin m × Fin N) → ZMod 2}
    {k : ℕ} (hz : MomentConsistent m N k z) {p : MvPolynomial (Fin m × Fin N) (ZMod 2)}
    (hp : p ∈ staticSpan (funPHPSystem m N) k) : momentFunctional z p = 0 := by
  induction hp using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    rcases hf with ⟨v, rfl⟩ | ⟨i, j, j', hne, rfl⟩ | ⟨i, i', j, hne, rfl⟩ | ⟨i, rfl⟩
    · rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, map_add,
        momentFunctional_monomial, momentFunctional_monomial, support_add_single_one,
        support_add_single_one, Finset.insert_idem v a.support]
      exact CharTwo.add_self_eq_zero _
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i, j')
        (Finset.mem_insert_self _ _) (Or.inl rfl)
      exact congrArg Prod.snd this
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i', j)
        (Finset.mem_insert_self _ _) (Or.inr rfl)
      exact congrArg Prod.fst this
    · have hrow := one_le_rowAxiom_totalDegree (m := m) hN i
      have hne0 :
          ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) ≠ 0 := by
        intro h0
        rw [h0, totalDegree_zero] at hrow
        omega
      have hmon : monomial a (1 : ZMod 2) ≠ 0 := by
        rw [Ne, monomial_eq_zero]
        exact one_ne_zero
      rw [totalDegree_mul_of_isDomain hmon hne0, totalDegree_monomial_one] at hdeg
      have hcard := card_support_le_degree a
      rw [monomial_one_mul_rowAxiom, map_add, map_sum, momentFunctional_monomial]
      simp only [momentFunctional_monomial, support_add_single_one]
      rw [momentWeight_row_sum hz a.support (fun _ => by omega) i]
      exact CharTwo.add_self_eq_zero _
noncomputable def indMon (T : Finset (Fin m × Fin N)) : Fin m × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v ∈ T then 1 else 0
theorem indMon_apply (T : Finset (Fin m × Fin N)) (v : Fin m × Fin N) :
    indMon T v = if v ∈ T then 1 else 0 := rfl
theorem indMon_support (T : Finset (Fin m × Fin N)) : (indMon T).support = T := by
  ext v
  simp [indMon_apply]
theorem indMon_degree (T : Finset (Fin m × Fin N)) : (indMon T).degree = T.card := by
  rw [Finsupp.degree_eq_sum]
  simp [indMon_apply]
theorem indMon_insert {T : Finset (Fin m × Fin N)} {v : Fin m × Fin N} (hv : v ∉ T) :
    indMon (insert v T) = indMon T + Finsupp.single v 1 := by
  ext u
  by_cases h : u = v
  · subst h
    simp [indMon_apply, hv]
  · simp [indMon_apply, h]
theorem eq_indMon_support {a : Fin m × Fin N →₀ ℕ} (h : ∀ v, a v ≤ 1) :
    a = indMon a.support := by
  ext v
  have := h v
  by_cases h0 : a v = 0
  · simp [indMon_apply, h0]
  · simp [indMon_apply, h0]
    omega
theorem dual_monomial_eq_indMon {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    ∀ (n : ℕ) (a : Fin m × Fin N →₀ ℕ), a.degree = n → a.degree ≤ k →
      φ (monomial a 1) = φ (monomial (indMon a.support) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a han hak
    by_cases h : ∀ v, a v ≤ 1
    · rw [← eq_indMon_support h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    have hle : Finsupp.single v 2 ≤ a := by
      intro u
      by_cases huv : v = u
      · subst huv
        rw [Finsupp.single_eq_same]
        omega
      · simp [huv]
    obtain ⟨b, hb⟩ : ∃ b, a = b + Finsupp.single v 2 :=
      ⟨a - Finsupp.single v 2, (tsub_add_cancel_of_le hle).symm⟩
    set c := b + Finsupp.single v 1 with hc
    have hac : a = c + Finsupp.single v 1 := by
      rw [hb, hc, add_assoc, ← Finsupp.single_add]
    have hdeg : a.degree = c.degree + 1 := by
      rw [hac, map_add, Finsupp.degree_single]
    have hq : monomial b (1 : ZMod 2) * (X v * X v + X v) = monomial a 1 + monomial c 1 := by
      rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, ← hc, ← hac]
    have hmem : monomial a (1 : ZMod 2) + monomial c 1 ∈ staticSpan (funPHPSystem m N) k := by
      refine Submodule.subset_span ⟨b, _, Or.inl ⟨v, rfl⟩, ?_, hq.symm⟩
      rw [hq]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_monomial_one]
        exact hak
      · rw [totalDegree_monomial_one]
        omega
    have h0 := hφ _ hmem
    rw [map_add, CharTwo.add_eq_zero] at h0
    have hsupp : a.support = c.support := by
      rw [hac, support_add_single_one, Finset.insert_eq_of_mem]
      rw [Finsupp.mem_support_iff, hc]
      simp
    rw [h0, hsupp]
    exact ih c.degree (by omega) c rfl (by omega)
theorem dual_monomial_eq_zero {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (a : Fin m × Fin N →₀ ℕ) (hak : a.degree ≤ k) (hM : ¬ IsPartialMatching a.support) :
    φ (monomial a 1) = 0 := by
  unfold IsPartialMatching at hM
  push Not at hM
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hM
  have hle : Finsupp.single u 1 + Finsupp.single v 1 ≤ a := by
    intro w
    have h1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
    have h2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    by_cases hwu : u = w
    · subst hwu
      simpa [Finsupp.single_apply, Ne.symm hne] using h1
    · by_cases hwv : v = w
      · subst hwv
        simpa [Finsupp.single_apply, hne] using h2
      · simp [hwu, hwv]
  obtain ⟨b, hb⟩ : ∃ b, a = b + (Finsupp.single u 1 + Finsupp.single v 1) :=
    ⟨a - (Finsupp.single u 1 + Finsupp.single v 1), (tsub_add_cancel_of_le hle).symm⟩
  have hq : monomial b (1 : ZMod 2) * (X u * X v) = monomial a 1 := by
    rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, hb, add_assoc]
  have hF : (X u * X v : MvPolynomial (Fin m × Fin N) (ZMod 2)) ∈ funPHPSystem m N := by
    obtain ⟨i, j⟩ := u
    obtain ⟨i', j'⟩ := v
    rcases huv with h | h
    · simp only at h
      subst h
      exact Or.inr (Or.inl ⟨i, j, j', fun h => hne (by rw [h]), rfl⟩)
    · simp only at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨i, i', j, fun h => hne (by rw [h]), rfl⟩))
  refine hφ _ (Submodule.subset_span ⟨b, _, hF, ?_, hq.symm⟩)
  rw [hq, totalDegree_monomial_one]
  exact hak
theorem momentConsistent_of_dual {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    MomentConsistent m N k fun T => φ (monomial (indMon T) 1) := by
  intro T hT hcard i hrow
  have hnot : ∀ j : Fin N, (i, j) ∉ T := fun j hj => hrow _ hj rfl
  have hmem : monomial (indMon T) (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) ∈
      staticSpan (funPHPSystem m N) k := by
    refine Submodule.subset_span ⟨indMon T, _, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)), ?_, rfl⟩
    refine (totalDegree_mul _ _).trans ?_
    have h1 := rowAxiom_totalDegree_le (N := N) i
    rw [totalDegree_monomial_one, indMon_degree]
    omega
  have h0 := hφ _ hmem
  rw [monomial_one_mul_rowAxiom, map_add, CharTwo.add_eq_zero, map_sum] at h0
  show φ (monomial (indMon T) 1) = _
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← indMon_insert (hnot j)]
  by_cases hc : ∀ a ∈ T, a.2 ≠ j
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    refine dual_monomial_eq_zero hφ _ ?_ ?_
    · rw [indMon_degree, Finset.card_insert_of_notMem (hnot j)]
      omega
    · rw [indMon_support]
      exact fun h => hc ((isPartialMatching_insert_iff hT hrow j).mp h)
theorem dual_eq_momentFunctional {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2)) (hp : p.totalDegree ≤ k) :
    φ p = momentFunctional (fun T => φ (monomial (indMon T) 1)) p := by
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hp
  rw [momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM]
    exact dual_monomial_eq_indMon hφ _ a rfl ha
  · rw [momentWeight_of_not hM]
    exact dual_monomial_eq_zero hφ a ha hM
theorem staticSpan_funPHP_inter (hN : 1 ≤ N) {k : ℕ} (hext : MomentExt m N k)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2))
    (hp : p ∈ staticSpan (funPHPSystem m N) (k + 1)) (hdeg : p.totalDegree ≤ k) :
    p ∈ staticSpan (funPHPSystem m N) k := by
  by_contra hnot
  obtain ⟨φ, hφp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0 := by
    intro q hq
    have : φ q ∈ (staticSpan (funPHPSystem m N) k).map φ := Submodule.mem_map_of_mem hq
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨z', hz', hagree⟩ := hext _ (momentConsistent_of_dual hφ)
  apply hφp
  rw [dual_eq_momentFunctional hφ p hdeg, ← momentFunctional_staticSpan hN hz' hp]
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hdeg
  rw [momentFunctional_monomial, momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM, momentWeight_of_matching hM]
    exact (hagree _ hM ((card_support_le_degree a).trans ha)).symm
  · rw [momentWeight_of_not hM, momentWeight_of_not hM]
theorem no_pc_refutation_of_momentExt :
    ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, MomentExt m N k) →
      ¬ PCRefutable (funPHPSystem m N) B := by
  intro m N B hN hext href
  have hint : ∀ k < B, ∀ p, p ∈ staticSpan (funPHPSystem m N) (k + 1) → p.totalDegree ≤ k →
      p ∈ staticSpan (funPHPSystem m N) k :=
    fun k hk p => staticSpan_funPHP_inter hN (hext k hk) p
  have h0 := one_mem_staticSpan_zero hint (pcDerivable_mem_staticSpan hint href)
  have hz : MomentConsistent m N 0 fun _ => 1 := by
    intro T _ hcard
    omega
  have hval := momentFunctional_staticSpan hN hz h0
  have h1 : (1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, momentFunctional_monomial, Finsupp.support_zero,
    momentWeight_of_matching isPartialMatching_empty] at hval
  exact one_ne_zero hval
theorem momentExt_zero (m N : ℕ) (hN : 1 ≤ N) : MomentExt m N 0 := by
  intro z _
  refine ⟨fun T => if T = ∅ then z ∅ else
    if ∃ i : Fin m, T = {(i, (⟨0, hN⟩ : Fin N))} then z ∅ else 0, ?_, ?_⟩
  · intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      ite_true, insert_empty_eq, Finset.singleton_ne_empty, ite_false]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [ite_eq_left ⟨i, rfl⟩]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨i', h⟩
      rw [Finset.singleton_inj] at h
      exact hj (congrArg Prod.snd h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro T _ hcard
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1
theorem not_momentExt_two_one_one : ¬ MomentExt 2 1 1 := by
  intro h
  have hz : MomentConsistent 2 1 1 fun _ => 1 := by
    intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
  obtain ⟨z', hz', hagree⟩ := h _ hz
  have hM : IsPartialMatching ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)) := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  have h1 := hz' {((0 : Fin 2), (0 : Fin 1))} hM (by simp) 1 (by simp)
  rw [hagree _ hM (by simp)] at h1
  have hempty : (Finset.univ.filter fun j : Fin 1 =>
      ∀ a ∈ ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)), a.2 ≠ j) = ∅ := by
    decide
  rw [hempty, Finset.sum_empty] at h1
  exact one_ne_zero h1
end Matching
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
noncomputable def pseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1))
theorem pseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1)) a
  simpa only [pseudoR, coe_basisMonomials] using h
theorem monoHoles_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoHoles G (a + Finsupp.single v 1) = insert v.1.2 (monoHoles G a) := by
  unfold monoHoles
  rw [support_add_single_one, Finset.image_insert]
theorem monoHoles_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, e.1.2 ∈ K) : ∀ a ∈ f.support, monoHoles G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩)
theorem pseudoR_monomial_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {a : GEdge G →₀ ℕ} (ha : a.degree ≤ D)
    (haK : monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s K)) (monomial a 1) := by
  rw [pseudoR_monomial]
  have h3 := card_monoHoles_le G a
  have hH : (monoHoles G a).card ≤ s := h3.trans (ha.trans hD)
  have hKs : K.card ≤ s := hK.trans hD
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoHoles G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoHoles G a)) (supp G s K)
    omega
  have e1 := nf_locIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoHoles G a))
  have e2 := nf_locIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoHoles G a))
  exact e1.symm.trans e2
theorem pseudoR_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s f = nf (locIdeal G (supp G s K)) f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (pseudoR G s), e (nf (locIdeal G (supp G s K)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [pseudoR_monomial_eq_nf G hG hD hK ((le_totalDegree ha).trans hf) (hfK a ha)]
theorem pseudoR_mul {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    pseudoR G s (X v * monomial a 1) = pseudoR G s (X v * pseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoHoles G (a + Finsupp.single v 1)).card ≤ D :=
    (card_monoHoles_le G _).trans (by omega)
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoHoles G a ⊆ monoHoles G (a + Finsupp.single v 1) := by
    rw [monoHoles_add_single]
    exact Finset.subset_insert _ _
  have e1 : pseudoR G s (monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1) :=
    pseudoR_monomial_eq_nf G hG hD hK0 (by omega) (haK0.trans Finset.subset_union_left)
  have e2 : pseudoR G s (X v * monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact pseudoR_monomial_eq_nf G hG hD hK0 (by omega) Finset.subset_union_left
  have hq : (nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : pseudoR G s (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
        (monomial a 1))
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine pseudoR_eq_nf G hG hD hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := nf_locIdeal_holes G _ a c hc
      rw [addRightEmbedding_apply, monoHoles_add_single]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine Finset.mem_union_left _ ?_
        rw [monoHoles_add_single]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1)
      ∈ locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_locIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0
theorem pseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ s) (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K)
    (hmem : f ∈ locIdeal G (supp G s K)) : pseudoR G s f = 0 := by
  rw [pseudoR_eq_nf G hG le_rfl hK hf (fun a ha => (hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem
theorem pseudoR_axiom {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s) (hD : D ≤ s)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ cnfSystem (graphPHP G))
    (hdeg : f.totalDegree ≤ D) : pseudoR G s f = 0 := by
  rcases cnfSystem_graphPHP_cases G hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · refine pseudoR_eq_zero_of_mem G hG (K := {v.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (bool_mem_locIdeal G _ v)
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
  · refine pseudoR_eq_zero_of_mem G hG (K := G i) ?_ (hdeg.trans hD)
      (monoHoles_pigeonClause G i)
      (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _)))
    rw [← totalDegree_pigeonClause G i]
    exact hdeg.trans hD
  · refine pseudoR_eq_zero_of_mem G hG (K := {e.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (hole_mem_locIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
      exact Finset.mem_singleton_self _
theorem pseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : pseudoR G s 1 ≠ 0 := by
  have hm : monoHoles G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoHoles
    rw [Finsupp.support_zero, Finset.image_empty]
  have h0 : supp G s (monoHoles G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : pseudoR G s 1 = nf (locIdeal G ∅) 1 := by
    have h := pseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_locIdeal_empty G ((nf_eq_zero_iff _ _).mp h)
theorem graphPHP_no_pc_refutation {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s)
    (hD : D ≤ s) : ¬ PCRefutable (cnfSystem (graphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (pseudoR G s)
    (fun _ hf hdeg => pseudoR_axiom G hG hs hD hf hdeg)
    (fun v a ha => pseudoR_mul G hG hD v a ha)
    (pseudoR_one G hG)
end PCXLib.Helpers
end
section
namespace PCXLib.Helpers
open PEqualNP.ProofComplexity
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
noncomputable def funPseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1))
theorem funPseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1)) a
  simpa only [funPseudoR, coe_basisMonomials] using h
theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji
theorem funPseudoR_monomial_eq_nf {s B : ℕ} (hG : IsBdryExpander G s 2) (hB : B ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ B) {a : GEdge G →₀ ℕ}
    (ha : (monoNbrs G a).card ≤ B)
    (haK : monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s (monomial a 1) = nf (funLocIdeal G (supp G s K)) (monomial a 1) := by
  rw [funPseudoR_monomial]
  have hH : (monoNbrs G a).card ≤ s := ha.trans hB
  have hKs : K.card ≤ s := hK.trans hB
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoNbrs G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoNbrs G a)) (supp G s K)
    omega
  have e1 := nf_funLocIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoNbrs G a))
  have e2 := nf_funLocIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoNbrs G a))
  exact e1.symm.trans e2
theorem funPseudoR_eq_nf_of_monomials {s : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)))
    {f : MvPolynomial (GEdge G) (ZMod 2)}
    (h : ∀ a ∈ f.support, funPseudoR G s (monomial a 1) = nf U (monomial a 1)) :
    funPseudoR G s f = nf U f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (funPseudoR G s), e (nf U)]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]
theorem funPseudoR_eq_nf {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) {K : Finset (Fin N)} (hK : K.card ≤ d * D)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s f = nf (funLocIdeal G (supp G s K)) f :=
  funPseudoR_eq_nf_of_monomials G _ fun a ha =>
    funPseudoR_monomial_eq_nf G hG hB hK
      ((card_monoNbrs_le G hd a).trans
        (Nat.mul_le_mul_left d ((le_totalDegree ha).trans hf))) (hfK a ha)
theorem funPseudoR_mul {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    funPseudoR G s (X v * monomial a 1)
      = funPseudoR G s (X v * funPseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoNbrs G (a + Finsupp.single v 1)).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hKa : (monoNbrs G a).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoNbrs G a ⊆ monoNbrs G (a + Finsupp.single v 1) := by
    rw [monoNbrs_add_single]
    exact Finset.subset_union_left
  have e1 : funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1)))) (monomial a 1) :=
    funPseudoR_monomial_eq_nf G hG hB hK0 hKa (haK0.trans Finset.subset_union_left)
  have e2 : funPseudoR G s (X v * monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact funPseudoR_monomial_eq_nf G hG hB hK0 hK0 Finset.subset_union_left
  have hq : (nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : funPseudoR G s
        (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1))
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine funPseudoR_eq_nf G hG hd hB hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := monoNbrs_subset_of_monoPigeons G (nf_funLocIdeal_pigeons G _ a c hc)
      rw [addRightEmbedding_apply, monoNbrs_add_single]
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
      · refine Finset.mem_union_left _ ?_
        rw [monoNbrs_add_single]
        exact Finset.mem_union_right _ hj
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1)
      ∈ funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_funLocIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0
theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem
theorem totalDegree_X_mul_X (e e' : GEdge G) :
    (X e * X e' : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
  have h : (X e * X e' : MvPolynomial (GEdge G) (ZMod 2))
      = monomial (Finsupp.single e 1 + Finsupp.single e' 1) 1 := by
    have hX : (X e : MvPolynomial (GEdge G) (ZMod 2)) = monomial (Finsupp.single e 1) 1 := rfl
    rw [hX, monomial_one_mul_X]
  rw [h, totalDegree_monomial_one, map_add, Finsupp.degree_single, Finsupp.degree_single]
theorem funPseudoR_axiom {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hs : 1 ≤ s) (hB : d * D ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) (hdeg : f.totalDegree ≤ D) : funPseudoR G s f = 0 := by
  have hcard : ∀ i, 1 ≤ D → (G i).card ≤ d * D := fun i hD =>
    (hd i).trans (Nat.le_mul_of_pos_right d hD)
  rcases cnfSystem_funGraphPHP_cases G hf with
    ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
      rw [totalDegree_add_eq_left_of_totalDegree_lt, totalDegree_X_mul_X]
      rw [totalDegree_X_mul_X, totalDegree_X]
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G v.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (bool_mem_locIdeal G _ v))
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
  · have hi : (G i).card ≤ D := by
      rw [← totalDegree_pigeonClause G i]
      exact hdeg
    have hi' : (G i).card ≤ s := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · omega
      · exact (hcard i h0).trans hB
    exact funPseudoR_eq_zero_of_mem G hG (K := G i) hi' (monoNbrs_pigeonClause G i)
      (locIdeal_le_funLocIdeal G _
        (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _))))
  · rw [totalDegree_X_mul_X] at hdeg
    have hK : (G e.1.1 ∪ G e'.1.1).card ≤ s := by
      have h3 := Finset.card_union_le (G e.1.1) (G e'.1.1)
      have h4 := hd e.1.1
      have h5 := hd e'.1.1
      have h6 : d * 2 ≤ d * D := Nat.mul_le_mul_left d hdeg
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1 ∪ G e'.1.1) hK
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (hole_mem_locIdeal G _ h1 h2))
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_left
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_right
  · rw [totalDegree_X_mul_X] at hdeg
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_) (fun_mem_funLocIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
theorem funPseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : funPseudoR G s 1 ≠ 0 := by
  have hm : monoNbrs G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoNbrs monoPigeons
    rw [Finsupp.support_zero, Finset.image_empty, Finset.biUnion_empty]
  have h0 : supp G s (monoNbrs G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : funPseudoR G s 1 = nf (funLocIdeal G ∅) 1 := by
    have h := funPseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_funLocIdeal_empty G ((nf_eq_zero_iff _ _).mp h)
theorem funGraphPHP_no_pc_refutation {s d D : ℕ} (hG : IsBdryExpander G s 2)
    (hd : LeftDegLe G d) (hs : 1 ≤ s) (hB : d * D ≤ s) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (funPseudoR G s)
    (fun _ hf hdeg => funPseudoR_axiom G hG hd hs hB hf hdeg)
    (fun v a ha => funPseudoR_mul G hG hd hB v a ha)
    (funPseudoR_one G hG)
end PCXLib.Helpers
end
section
namespace PCXLib
open PEqualNP.ProofComplexity
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB
end PCXLib
end
section ProofBody
open MvPolynomial PEqualNP.Expanders PEqualNP.ProofComplexity PCXLib.Helpers
private lemma zmod2_add_self {V : Type} (p : MvPolynomial V (ZMod 2)) : p + p = 0 := by
  rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]
private lemma zmod2_add_cancel_right {V : Type} (p q : MvPolynomial V (ZMod 2)) :
    (p + q) + q = p := by
  rw [add_assoc, zmod2_add_self, add_zero]
private lemma zmod2_add_cancel_left {V : Type} (p q : MvPolynomial V (ZMod 2)) :
    p + (p + q) = q := by
  rw [← add_assoc, zmod2_add_self, zero_add]
private lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide
private lemma zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert h; revert c; decide
private lemma zmod2_add_one_eq_zero_iff (c : ZMod 2) : c + 1 = 0 ↔ c ≠ 0 := by
  revert c; decide
private lemma natCast_zmod2_eq_zero_iff (m : ℕ) : (m : ZMod 2) = 0 ↔ ¬ Odd m := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨k, rfl⟩ ⟨r, hr⟩; omega
  · intro h
    have hmod : m % 2 = 0 := by
      by_contra hne
      exact h ⟨m / 2, by omega⟩
    exact Nat.dvd_of_mod_eq_zero hmod
private def b2f {V : Type} (x : V → Bool) : V → ZMod 2 :=
  fun v => if x v = true then 1 else 0
private def f2b {V : Type} (a : V → ZMod 2) : V → Bool :=
  fun v => decide (a v = 1)
private lemma b2f_f2b {V : Type} (a : V → ZMod 2) : b2f (f2b a) = a := by
  funext v
  rcases zmod2_eq_zero_or_one (a v) with h | h <;> simp [b2f, f2b, h]
private lemma f2b_b2f {V : Type} (x : V → Bool) : f2b (b2f x) = x := by
  funext v
  cases h : x v <;> simp [b2f, f2b, h]
private noncomputable def linEqPoly {V : Type} (e : LinEq V) : MvPolynomial V (ZMod 2) :=
  (∑ v ∈ e.1, X v) + if e.2 = true then 1 else 0
private lemma linEqPoly_deg {V : Type} (e : LinEq V) : (linEqPoly e).totalDegree ≤ 1 := by
  unfold linEqPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le fun v _ => ?_
    rw [totalDegree_X]
  · split_ifs <;> simp
private lemma eval_linEqPoly {V : Type} (x : V → Bool) (e : LinEq V) :
    eval (b2f x) (linEqPoly e) = 0 ↔ LinEqSat x e := by
  classical
  unfold linEqPoly LinEqSat
  have hsum : eval (b2f x) (∑ v ∈ e.1, X v) =
      ((e.1.filter (fun v => x v = true)).card : ZMod 2) := by
    rw [map_sum]
    simp only [eval_X, b2f]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  rw [map_add, hsum]
  cases hb : e.2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, map_zero, add_zero, iff_false]
    exact natCast_zmod2_eq_zero_iff _
  | true =>
    simp only [↓reduceIte, map_one, iff_true]
    rw [zmod2_add_one_eq_zero_iff, ne_eq, natCast_zmod2_eq_zero_iff, not_not]
private lemma pc_deg1_idem {V : Type} (F : Set (MvPolynomial V (ZMod 2)))
    (hBool : ∀ v : V, X v * X v + X v ∈ F)
    (ℓ : MvPolynomial V (ZMod 2)) (hℓ : ℓ.totalDegree ≤ 1) :
    PCDerivable F 2 (ℓ * (ℓ + 1)) := by
  have hdeg : (ℓ * (ℓ + 1)).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (ℓ + 1).totalDegree ≤ 1 := by
      refine (totalDegree_add _ _).trans (max_le hℓ ?_)
      simp
    omega
  refine PCXLib.Helpers.BoolVanish.vanish_derivable V F 2 (ℓ * (ℓ + 1)) hBool hdeg fun a => ?_
  simp only [map_mul, map_add, map_one]
  generalize eval a ℓ = c
  revert c; decide
private lemma clausePoly_deg {V : Type} (C : Clause V) : (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ l ∈ C, (if l.2 = true then 1 + X l.1 else X l.1 : MvPolynomial V (ZMod 2)).totalDegree
      ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum fun l _ => by
        split_ifs
        · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
          · simp
          · rw [totalDegree_X]
        · rw [totalDegree_X]
    _ = C.card := by simp
private lemma incPig_card_le {m N : ℕ} (G : BipGraph m N) (i : Fin m) :
    (Finset.univ.filter (fun e : GEdge G => e.1.1 = i)).card ≤ (G i).card := by
  refine Finset.card_le_card_of_injOn (fun e => e.1.2) ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he
    have hmem := e.2
    rw [he] at hmem
    exact hmem
  · intro e₁ he₁ e₂ he₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    apply Subtype.ext
    exact Prod.ext (he₁.trans he₂.symm) heq
private lemma incHole_card_le {m N : ℕ} (G : BipGraph m N) (j : Fin N) :
    (Finset.univ.filter (fun e : GEdge G => e.1.2 = j)).card ≤ (rightNbrs G j).card := by
  refine Finset.card_le_card_of_injOn (fun e => e.1.1) ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_coe, rightNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
    have hmem := e.2
    rw [he] at hmem
    exact hmem
  · intro e₁ he₁ e₂ he₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    apply Subtype.ext
    exact Prod.ext heq (he₁.trans he₂.symm)
private lemma clausePoly_deg_of_funGraphPHP {m N : ℕ} (G : BipGraph m N) (b' : ℕ)
    (hb' : 2 ≤ b') (hLeft : LeftDegLe G b') (C : Clause (GEdge G)) (hC : C ∈ funGraphPHP G) :
    (clausePoly C).totalDegree ≤ b' := by
  refine (clausePoly_deg C).trans ?_
  rcases hC with (⟨i, rfl⟩ | ⟨e, e', _, _, rfl⟩) | ⟨e, e', _, _, rfl⟩
  · have hle : (Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)).card ≤
        (G i).card := by
      refine Finset.card_le_card_of_injOn (fun l => l.1.1.2) ?_ ?_
      · intro l hl
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        have hmem := l.1.2
        rw [hl.1] at hmem
        exact hmem
      · intro l₁ hl₁ l₂ hl₂ heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl₁ hl₂
        exact Prod.ext (Subtype.ext (Prod.ext (hl₁.1.trans hl₂.1.symm) heq))
          (hl₁.2.trans hl₂.2.symm)
    exact hle.trans (hLeft i)
  · exact (Finset.card_le_two).trans hb'
  · exact (Finset.card_le_two).trans hb'
private lemma cnfSystem_deg_le {m N : ℕ} (G : BipGraph m N) (b' : ℕ)
    (hb' : 2 ≤ b') (hLeft : LeftDegLe G b') (p : MvPolynomial (GEdge G) (ZMod 2))
    (hp : p ∈ cnfSystem (funGraphPHP G)) : p.totalDegree ≤ b' := by
  rcases hp with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  · exact clausePoly_deg_of_funGraphPHP G b' hb' hLeft C hC
private lemma eval_clausePoly {V : Type} (x : V → Bool) (C : Clause V) :
    eval (b2f x) (clausePoly C) = 0 ↔ ClauseSat x C := by
  unfold clausePoly ClauseSat
  rw [map_prod, Finset.prod_eq_zero_iff]
  refine exists_congr fun l => and_congr_right fun _ => ?_
  cases h2 : l.2 with
  | true =>
    simp only [↓reduceIte, map_add, map_one, eval_X, b2f]
    cases hx : x l.1 <;> decide
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, eval_X, b2f]
    cases hx : x l.1 <;> decide
private noncomputable def satProd {V : Type} (S : Finset (Clause V)) : MvPolynomial V (ZMod 2) :=
  ∏ cl ∈ S, (1 + clausePoly cl)
private lemma satProd_deg {V : Type} (b' : ℕ) (S : Finset (Clause V))
    (hS : ∀ cl ∈ S, (clausePoly cl).totalDegree ≤ b') :
    (satProd S).totalDegree ≤ b' * S.card := by
  unfold satProd
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ cl ∈ S, (1 + clausePoly cl).totalDegree
      ≤ ∑ _cl ∈ S, b' := Finset.sum_le_sum fun cl hcl => by
        refine (totalDegree_add _ _).trans (max_le ?_ (hS cl hcl))
        simp
    _ = S.card * b' := by simp
    _ = b' * S.card := mul_comm _ _
private lemma eval_satProd {V : Type} (x : V → Bool) (S : Finset (Clause V)) :
    eval (b2f x) (satProd S) = 0 ↔ ∃ cl ∈ S, ¬ ClauseSat x cl := by
  unfold satProd
  rw [map_prod, Finset.prod_eq_zero_iff]
  refine exists_congr fun cl => and_congr_right fun _ => ?_
  rw [map_add, map_one, add_comm, zmod2_add_one_eq_zero_iff, ne_eq, eval_clausePoly]
private lemma pc_one_add_satProd {V : Type} (F : Set (Clause V)) (b' : ℕ)
    (S : Finset (Clause V)) (hSF : ∀ cl ∈ S, cl ∈ F)
    (hSdeg : ∀ cl ∈ S, (clausePoly cl).totalDegree ≤ b') :
    PCDerivable (cnfSystem F) (b' * S.card) (1 + satProd S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (1 + satProd (∅ : Finset (Clause V)) : MvPolynomial V (ZMod 2)) = 0 := by
      simp [satProd, zmod2_add_self]
    rw [h0]
    exact .zero
  | @insert cl S hcl ih =>
    have hSF' : ∀ c ∈ S, c ∈ F := fun c hc => hSF c (Finset.mem_insert_of_mem hc)
    have hSdeg' : ∀ c ∈ S, (clausePoly c).totalDegree ≤ b' :=
      fun c hc => hSdeg c (Finset.mem_insert_of_mem hc)
    have hcard : (insert cl S).card = S.card + 1 := Finset.card_insert_of_notMem hcl
    rw [hcard]
    have hsplit : (1 + satProd (insert cl S) : MvPolynomial V (ZMod 2)) =
        (1 + satProd S) + satProd S * clausePoly cl := by
      simp only [satProd, Finset.prod_insert hcl]
      ring
    rw [hsplit]
    have h1 : PCDerivable (cnfSystem F) (b' * (S.card + 1)) (1 + satProd S) :=
      pcDerivable_mono (ih hSF' hSdeg') (Nat.mul_le_mul_left b' (Nat.le_succ _)) subset_rfl
    have hcl_deg : (clausePoly cl).totalDegree ≤ b' := hSdeg cl (Finset.mem_insert_self cl S)
    have hax : PCDerivable (cnfSystem F) (b' * (S.card + 1)) (clausePoly cl) :=
      .ax (Or.inr ⟨cl, hSF cl (Finset.mem_insert_self cl S), rfl⟩)
        (hcl_deg.trans (by nlinarith))
    have h2 : PCDerivable (cnfSystem F) (b' * (S.card + 1)) (satProd S * clausePoly cl) := by
      have hm := pcDerivable_mul_left hax (satProd S)
      have hbd : (satProd S).totalDegree + (clausePoly cl).totalDegree ≤ b' * (S.card + 1) := by
        have hsd := satProd_deg b' S hSdeg'
        linarith
      rwa [max_eq_left hbd] at hm
    exact .add h1 h2
private lemma pcDerivable_subst_ax {V : Type} {A B : Set (MvPolynomial V (ZMod 2))} {D : ℕ}
    {p : MvPolynomial V (ZMod 2)} (h : PCDerivable A D p)
    (hax : ∀ a ∈ A, a.totalDegree ≤ D → PCDerivable B D a) :
    PCDerivable B D p := by
  induction h with
  | ax ha hd => exact hax _ ha hd
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hd ih => exact .mulX j ih hd
private lemma finsupp_sum_le_one {V : Type} {a : V →₀ ℕ} (ha : (a.sum fun _ e => e) ≤ 1) :
    a = 0 ∨ ∃ v : V, a = Finsupp.single v 1 := by
  classical
  by_cases hs : a.support = ∅
  · left; exact Finsupp.support_eq_empty.mp hs
  · right
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    refine ⟨v, ?_⟩
    have hav_pos : 1 ≤ a v := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv))
    have hsum_eq : a.sum (fun _ e => e) = ∑ w ∈ a.support, a w := rfl
    have hav_le : a v ≤ a.sum (fun _ e => e) := by
      rw [hsum_eq]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    have hav : a v = 1 := by omega
    ext w
    by_cases hw : w = v
    · subst hw; simp [hav]
    · simp only [Finsupp.single_apply, Ne.symm hw, ↓reduceIte]
      by_contra hne
      have hw_mem : w ∈ a.support := Finsupp.mem_support_iff.mpr hne
      have haw_pos : 1 ≤ a w := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      have hpair : a v + a w ≤ ∑ u ∈ a.support, a u := by
        have hsub : ({v, w} : Finset V) ⊆ a.support := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
        calc a v + a w = ∑ u ∈ ({v, w} : Finset V), a u := by
              rw [Finset.sum_pair (Ne.symm hw)]
          _ ≤ ∑ u ∈ a.support, a u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      omega
private lemma deg1_cases {V : Type} (ℓ : MvPolynomial V (ZMod 2)) (hℓ : ℓ.totalDegree ≤ 1) :
    ℓ = 0 ∨ ℓ = 1 ∨ ∃ (v₀ : V) (g : MvPolynomial V (ZMod 2)),
      g.totalDegree ≤ 1 ∧ (∀ a ∈ g.support, a v₀ = 0) ∧ ℓ = X v₀ + g := by
  classical
  by_cases hex : ∃ v₀ : V, Finsupp.single v₀ 1 ∈ ℓ.support
  · right; right
    obtain ⟨v₀, hv₀⟩ := hex
    refine ⟨v₀, ℓ + X v₀, ?_, ?_, ?_⟩
    · refine (totalDegree_add _ _).trans (max_le hℓ ?_)
      rw [totalDegree_X]
    · intro a ha
      have hdeg_g : (ℓ + X v₀).totalDegree ≤ 1 := by
        refine (totalDegree_add _ _).trans (max_le hℓ ?_)
        rw [totalDegree_X]
      have hsum : (a.sum fun _ e => e) ≤ 1 := (le_totalDegree ha).trans hdeg_g
      rcases finsupp_sum_le_one hsum with rfl | ⟨v, rfl⟩
      · simp
      · by_cases hvv : v = v₀
        · subst hvv
          exfalso
          have hnz : (ℓ + X v).coeff (Finsupp.single v 1) ≠ 0 := mem_support_iff.mp ha
          have hℓ1 : ℓ.coeff (Finsupp.single v 1) = 1 :=
            zmod2_eq_one_of_ne_zero (mem_support_iff.mp hv₀)
          have hX1 : (X v : MvPolynomial V (ZMod 2)).coeff (Finsupp.single v 1) = 1 := by
            simp [coeff_X]
          have hadd : (ℓ + X v).coeff (Finsupp.single v 1) =
              ℓ.coeff (Finsupp.single v 1) + (X v : MvPolynomial V (ZMod 2)).coeff (Finsupp.single v 1) := rfl
          rw [hadd, hℓ1, hX1] at hnz
          exact hnz rfl
        · simp [Ne.symm hvv]
    · rw [add_comm (X v₀), zmod2_add_cancel_right]
  · push Not at hex
    have hconst : ℓ = C (ℓ.coeff 0) := by
      ext a
      by_cases ha0 : a = 0
      · subst ha0; simp
      · simp only [coeff_C, Ne.symm ha0, ↓reduceIte]
        by_contra hne
        have hmem : a ∈ ℓ.support := mem_support_iff.mpr hne
        have hsum : (a.sum fun _ e => e) ≤ 1 := (le_totalDegree hmem).trans hℓ
        rcases finsupp_sum_le_one hsum with rfl | ⟨v, rfl⟩
        · exact ha0 rfl
        · exact hex v hmem
    rcases zmod2_eq_zero_or_one (ℓ.coeff 0) with h0 | h1
    · left; rw [hconst, h0, map_zero]
    · right; left; rw [hconst, h1, map_one]
private lemma eval_bind₁_eq {V : Type} (a : V → ZMod 2) (φ : V → MvPolynomial V (ZMod 2))
    (p : MvPolynomial V (ZMod 2)) :
    eval a (bind₁ φ p) = eval (fun v => eval a (φ v)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q ihp ihq => simp [ihp, ihq]
  | mul_X p v ih => simp [ih]
private lemma bind₁_update_eq_self {V : Type} [DecidableEq V] (v₀ : V)
    (g p : MvPolynomial V (ZMod 2)) (hno : ∀ a ∈ p.support, a v₀ = 0) :
    bind₁ (Function.update X v₀ g) p = p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [bind₁_monomial]
  have hprod : ∏ i ∈ a.support, (Function.update (X : V → MvPolynomial V (ZMod 2)) v₀ g i) ^ a i =
      ∏ i ∈ a.support, (X i : MvPolynomial V (ZMod 2)) ^ a i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ v₀ := fun h => by
      subst h; exact (Finsupp.mem_support_iff.mp hi) (hno a ha)
    rw [Function.update_of_ne hne]
  rw [hprod]
  have hX := bind₁_monomial (R := ZMod 2) (f := (X : V → MvPolynomial V (ZMod 2))) a (p.coeff a)
  rw [bind₁_X_left] at hX
  exact hX.symm
private lemma bind₁_update_deg1 {V : Type} [DecidableEq V] (v₀ : V)
    (g : MvPolynomial V (ZMod 2)) (hno_g : ∀ a ∈ g.support, a v₀ = 0)
    (ℓ' : MvPolynomial V (ZMod 2)) (hℓ' : ℓ'.totalDegree ≤ 1) :
    bind₁ (Function.update X v₀ g) ℓ' = ℓ' ∨
      bind₁ (Function.update X v₀ g) ℓ' = ℓ' + (X v₀ + g) := by
  classical
  by_cases hv : Finsupp.single v₀ 1 ∈ ℓ'.support
  · right
    set g' := ℓ' + X v₀ with hg'
    have hno_g' : ∀ a ∈ g'.support, a v₀ = 0 := by
      intro a ha
      have hdeg_g' : g'.totalDegree ≤ 1 := by
        refine (totalDegree_add _ _).trans (max_le hℓ' ?_)
        rw [totalDegree_X]
      rcases finsupp_sum_le_one ((le_totalDegree ha).trans hdeg_g') with rfl | ⟨v, rfl⟩
      · simp
      · by_cases hvv : v = v₀
        · subst hvv
          exfalso
          have hnz : (ℓ' + X v).coeff (Finsupp.single v 1) ≠ 0 := mem_support_iff.mp ha
          have h1 : ℓ'.coeff (Finsupp.single v 1) = 1 :=
            zmod2_eq_one_of_ne_zero (mem_support_iff.mp hv)
          have h2 : (X v : MvPolynomial V (ZMod 2)).coeff (Finsupp.single v 1) = 1 := by
            simp [coeff_X]
          have hadd : (ℓ' + X v).coeff (Finsupp.single v 1) =
              ℓ'.coeff (Finsupp.single v 1) + (X v : MvPolynomial V (ZMod 2)).coeff (Finsupp.single v 1) := rfl
          rw [hadd, h1, h2] at hnz
          exact hnz rfl
        · simp [Ne.symm hvv]
    have hℓ'_eq : ℓ' = X v₀ + g' := by rw [hg', add_comm (X v₀), zmod2_add_cancel_right]
    have hfix : bind₁ (Function.update X v₀ g) g' = g' := bind₁_update_eq_self v₀ g g' hno_g'
    have h_calc : bind₁ (Function.update X v₀ g) ℓ' = g + g' := by
      conv_lhs => rw [hℓ'_eq]
      rw [map_add, bind₁_X_right, Function.update_self, hfix]
    rw [h_calc, hg']
    have hcomm : g + (ℓ' + X v₀) = ℓ' + (X v₀ + g) := by ring
    exact hcomm
  · left
    refine bind₁_update_eq_self v₀ g ℓ' fun a ha => ?_
    rcases finsupp_sum_le_one ((le_totalDegree ha).trans hℓ') with rfl | ⟨v, rfl⟩
    · simp
    · have hne : v ≠ v₀ := fun h => by subst h; exact hv ha
      exact Finsupp.single_eq_of_ne (Ne.symm hne)
private lemma pow_add_pow_factor {V : Type} (v₀ : V) (g : MvPolynomial V (ZMod 2))
    (hg : g.totalDegree ≤ 1) :
    ∀ e : ℕ, ∃ R : MvPolynomial V (ZMod 2),
      R.totalDegree ≤ e ∧ X v₀ ^ (e + 1) + g ^ (e + 1) = R * (X v₀ + g) := by
  intro e
  induction e with
  | zero =>
    refine ⟨1, by simp, ?_⟩
    simp
  | succ e ih =>
    obtain ⟨R, hRdeg, hReq⟩ := ih
    refine ⟨X v₀ * R + g ^ (e + 1), ?_, ?_⟩
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · refine (totalDegree_pow _ _).trans ?_
        nlinarith
    · calc X v₀ ^ (e + 2) + g ^ (e + 2)
          = (X v₀ ^ (e + 2) + g ^ (e + 2)) + (X v₀ * g ^ (e + 1) + X v₀ * g ^ (e + 1)) := by
            rw [zmod2_add_self, add_zero]
        _ = X v₀ * (X v₀ ^ (e + 1) + g ^ (e + 1)) + g ^ (e + 1) * (X v₀ + g) := by ring
        _ = X v₀ * (R * (X v₀ + g)) + g ^ (e + 1) * (X v₀ + g) := by rw [hReq]
        _ = (X v₀ * R + g ^ (e + 1)) * (X v₀ + g) := by ring
private lemma monomial_add_bind₁_factor {V : Type} [DecidableEq V] (v₀ : V)
    (g : MvPolynomial V (ZMod 2)) (hg : g.totalDegree ≤ 1) (d : ℕ)
    (a : V →₀ ℕ) (ha : (a.sum fun _ e => e) ≤ d) :
    ∃ Q : MvPolynomial V (ZMod 2),
      Q.totalDegree ≤ d - 1 ∧
        monomial a 1 + bind₁ (Function.update X v₀ g) (monomial a 1) = Q * (X v₀ + g) := by
  cases he : a v₀ with
  | zero =>
    have hfix : bind₁ (Function.update X v₀ g) (monomial a 1) = monomial a 1 := by
      refine bind₁_update_eq_self v₀ g (monomial a 1) fun c hc => ?_
      rw [support_monomial] at hc
      simp only [show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, Finset.mem_singleton] at hc
      rw [hc, he]
    refine ⟨0, by simp, ?_⟩
    rw [hfix, zmod2_add_self, zero_mul]
  | succ e =>
    set a' := a - Finsupp.single v₀ (e + 1) with ha'
    have ha'_v0 : a' v₀ = 0 := by simp [ha', he]
    have ha_eq : a = a' + Finsupp.single v₀ (e + 1) := by
      ext w
      simp only [ha', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hw
      · subst hw; omega
      · omega
    have hsum_split : (a.sum fun _ k => k) = (a'.sum fun _ k => k) + (e + 1) := by
      conv_lhs => rw [ha_eq]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have hmon_split : monomial a (1 : ZMod 2) = monomial a' 1 * X v₀ ^ (e + 1) := by
      rw [ha_eq, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    have hfix_a' : bind₁ (Function.update X v₀ g) (monomial a' 1) = monomial a' 1 := by
      refine bind₁_update_eq_self v₀ g (monomial a' 1) fun c hc => ?_
      rw [support_monomial] at hc
      simp only [show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, Finset.mem_singleton] at hc
      rw [hc, ha'_v0]
    obtain ⟨R, hRdeg, hReq⟩ := pow_add_pow_factor v₀ g hg e
    refine ⟨monomial a' 1 * R, ?_, ?_⟩
    · refine (totalDegree_mul _ _).trans ?_
      have h1 : (monomial a' (1 : ZMod 2)).totalDegree ≤ a'.sum fun _ k => k :=
        totalDegree_monomial_le a' 1
      omega
    · rw [hmon_split, map_mul, hfix_a', map_pow, bind₁_X_right, Function.update_self,
        ← mul_add, hReq, mul_assoc]
private lemma subVar_diff_factor {V : Type} [DecidableEq V] (v₀ : V)
    (g : MvPolynomial V (ZMod 2)) (hg : g.totalDegree ≤ 1) (d : ℕ)
    (p : MvPolynomial V (ZMod 2)) (hp : p.totalDegree ≤ d) :
    ∃ Q : MvPolynomial V (ZMod 2),
      Q.totalDegree ≤ d - 1 ∧
        p + bind₁ (Function.update X v₀ g) p = Q * (X v₀ + g) := by
  classical
  have hterm : ∀ a ∈ p.support, ∃ Q : MvPolynomial V (ZMod 2),
      Q.totalDegree ≤ d - 1 ∧
        monomial a 1 + bind₁ (Function.update X v₀ g) (monomial a 1) = Q * (X v₀ + g) :=
    fun a ha => monomial_add_bind₁_factor v₀ g hg d a ((le_totalDegree ha).trans hp)
  choose Q hQdeg hQeq using hterm
  refine ⟨∑ a ∈ p.support.attach, Q a.1 a.2, ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun a _ => hQdeg a.1 a.2
  · rw [Finset.sum_mul]
    have hpas : p = ∑ a ∈ p.support.attach, monomial a.1 (1 : ZMod 2) := by
      conv_lhs => rw [p.as_sum]
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [zmod2_eq_one_of_ne_zero (mem_support_iff.mp a.2)]
    conv_lhs => rw [hpas]
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => hQeq a.1 a.2
private lemma affine_nullstellensatz {V : Type} [DecidableEq V]
    (F : Set (MvPolynomial V (ZMod 2)))
    (hBool : ∀ v : V, X v * X v + X v ∈ F)
    (d : ℕ) (hd : 1 ≤ d) :
    ∀ (m : ℕ) (L : Finset (MvPolynomial V (ZMod 2))),
      L.card ≤ m →
      (∀ ℓ ∈ L, ℓ.totalDegree ≤ 1) →
      ∀ (p : MvPolynomial V (ZMod 2)), p.totalDegree ≤ d →
        (∀ a : V → ZMod 2, (∀ ℓ ∈ L, eval a ℓ = 0) → eval a p = 0) →
        PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d p := by
  classical
  intro m
  induction m with
  | zero =>
    intro L hcard _ p hp hvan
    have hLempty : L = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    have hvan' : ∀ a : V → ZMod 2, eval a p = 0 := fun a =>
      hvan a (by rw [hLempty]; intro ℓ hℓ; exact absurd hℓ (Finset.notMem_empty ℓ))
    exact pcDerivable_mono
      (PCXLib.Helpers.BoolVanish.vanish_derivable V F d p hBool hp hvan')
      le_rfl Set.subset_union_left
  | succ m ih =>
    intro L hcard hL p hp hvan
    by_cases hLempty : L = ∅
    · have hvan' : ∀ a : V → ZMod 2, eval a p = 0 := fun a =>
        hvan a (by rw [hLempty]; intro ℓ hℓ; exact absurd hℓ (Finset.notMem_empty ℓ))
      exact pcDerivable_mono
        (PCXLib.Helpers.BoolVanish.vanish_derivable V F d p hBool hp hvan')
        le_rfl Set.subset_union_left
    · obtain ⟨ℓ, hℓmem⟩ := Finset.nonempty_iff_ne_empty.mpr hLempty
      set L' := L.erase ℓ with hL'def
      have hL'card : L'.card ≤ m := by
        have hce : L'.card = L.card - 1 := Finset.card_erase_of_mem hℓmem
        omega
      have hL'sub : L' ⊆ L := Finset.erase_subset ℓ L
      have hL'deg : ∀ q ∈ L', q.totalDegree ≤ 1 := fun q hq => hL q (hL'sub hq)
      rcases deg1_cases ℓ (hL ℓ hℓmem) with rfl | rfl | ⟨v₀, g, hgdeg, hgno, hℓeq⟩
      · have hvan' : ∀ a : V → ZMod 2, (∀ q ∈ L', eval a q = 0) → eval a p = 0 := by
          intro a ha
          refine hvan a fun q hq => ?_
          by_cases hq0 : q = 0
          · subst hq0; simp
          · exact ha q (Finset.mem_erase.mpr ⟨hq0, hq⟩)
        exact pcDerivable_mono (ih L' hL'card hL'deg p hp hvan') le_rfl
          (Set.union_subset_union_right F (Finset.coe_subset.mpr hL'sub))
      · have h1ax : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d 1 :=
          .ax (Or.inr hℓmem) (by simp)
        have hm := pcDerivable_mul_left h1ax p
        rw [mul_one, totalDegree_one, add_zero, max_eq_left hp] at hm
        exact hm
      · set φ : V → MvPolynomial V (ZMod 2) := Function.update X v₀ g with hφdef
        have hφdeg : ∀ j : V, (φ j).totalDegree ≤ 1 := by
          intro j
          by_cases hj : j = v₀
          · subst hj; simpa [hφdef] using hgdeg
          · rw [hφdef, Function.update_of_ne hj, totalDegree_X]
        set L'' := L'.image (bind₁ φ) with hL''def
        have hL''card : L''.card ≤ m := (Finset.card_image_le).trans hL'card
        have hL''deg : ∀ q ∈ L'', q.totalDegree ≤ 1 := by
          intro q hq
          obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
          have := totalDegree_bind₁_le φ hφdeg q'
          have hq'd := hL'deg q' hq'
          omega
        have hσp_deg : (bind₁ φ p).totalDegree ≤ d := by
          have := totalDegree_bind₁_le φ hφdeg p
          omega
        have hσg : bind₁ φ g = g := bind₁_update_eq_self v₀ g g hgno
        have hσℓ : bind₁ φ ℓ = 0 := by
          rw [hℓeq, map_add, bind₁_X_right, hφdef, Function.update_self, hσg, zmod2_add_self]
        have hvan'' : ∀ a : V → ZMod 2, (∀ q ∈ L'', eval a q = 0) → eval a (bind₁ φ p) = 0 := by
          intro a ha
          set a' : V → ZMod 2 := fun v => eval a (φ v)
          have hev : ∀ r : MvPolynomial V (ZMod 2), eval a (bind₁ φ r) = eval a' r :=
            fun r => eval_bind₁_eq a φ r
          rw [hev p]
          refine hvan a' fun q hq => ?_
          by_cases hqℓ : q = ℓ
          · rw [hqℓ, ← hev ℓ, hσℓ, map_zero]
          · rw [← hev q]
            exact ha (bind₁ φ q) (Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqℓ, hq⟩, rfl⟩)
        have hder_σp' : PCDerivable (F ∪ (L'' : Set (MvPolynomial V (ZMod 2)))) d (bind₁ φ p) :=
          ih L'' hL''card hL''deg (bind₁ φ p) hσp_deg hvan''
        have hder_σp : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d (bind₁ φ p) := by
          refine pcDerivable_subst_ax hder_σp' fun q hq hqdeg => ?_
          rcases hq with hqF | hqL''
          · exact .ax (Or.inl hqF) hqdeg
          · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hqL''
            have hq'mem : q' ∈ L := hL'sub hq'
            have hq'ax : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d q' :=
              .ax (Or.inr hq'mem) ((hL'deg q' hq').trans hd)
            have hℓax : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d ℓ :=
              .ax (Or.inr hℓmem) ((hL ℓ hℓmem).trans hd)
            rcases bind₁_update_deg1 v₀ g hgno q' (hL'deg q' hq') with heq | heq
            · rw [hφdef, heq]; exact hq'ax
            · rw [hφdef, heq, ← hℓeq]; exact .add hq'ax hℓax
        obtain ⟨Q, hQdeg, hQeq⟩ := subVar_diff_factor v₀ g hgdeg d p hp
        have hℓax : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d ℓ :=
          .ax (Or.inr hℓmem) ((hL ℓ hℓmem).trans hd)
        have hder_diff : PCDerivable (F ∪ (L : Set (MvPolynomial V (ZMod 2)))) d (p + bind₁ φ p) := by
          rw [hφdef, hQeq, ← hℓeq]
          have hm := pcDerivable_mul_left hℓax Q
          have hℓd := hL ℓ hℓmem
          have hbd : Q.totalDegree + ℓ.totalDegree ≤ d := by omega
          rwa [max_eq_left hbd] at hm
        have hsum := PCDerivable.add hder_diff hder_σp
        rwa [zmod2_add_cancel_right] at hsum
private lemma pc_mul_affine {V : Type}
    (F₀ : Set (MvPolynomial V (ZMod 2)))
    (hBool : ∀ v : V, X v * X v + X v ∈ F₀)
    (ℓ : MvPolynomial V (ZMod 2)) (hℓ : ℓ.totalDegree ≤ 1)
    (D : ℕ) (hD : 1 ≤ D)
    (h : PCDerivable (F₀ ∪ {ℓ}) D 1) :
    PCDerivable F₀ (D + 1) (ℓ + 1) := by
  have h1deg : (ℓ + 1).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le hℓ ?_)
    simp
  have hrep := pcDerivable_replay (F := F₀ ∪ {ℓ}) (G := F₀) (T := 1) (D := D) (s := 1)
    (X : V → MvPolynomial V (ZMod 2)) (fun j => by rw [totalDegree_X]) (ℓ + 1) h1deg ?_ h
  · simpa using hrep
  · intro a ha hadeg
    simp only [bind₁_X_left, AlgHom.id_apply]
    rcases ha with haF | haℓ
    · have hax : PCDerivable F₀ (1 * D + 1) a := .ax haF (by omega)
      have hm := pcDerivable_mul_left hax (ℓ + 1)
      have hbd : (ℓ + 1).totalDegree + a.totalDegree ≤ 1 * D + 1 := by omega
      rwa [max_eq_left hbd] at hm
    · rw [Set.mem_singleton_iff] at haℓ
      rw [haℓ, mul_comm (ℓ + 1) ℓ]
      refine pcDerivable_mono (pc_deg1_idem F₀ hBool ℓ hℓ) ?_ subset_rfl
      omega
private lemma pc_subst_replay {V : Type} [DecidableEq V]
    (F₀ : Set (MvPolynomial V (ZMod 2))) (b' : ℕ) (hb' : 1 ≤ b')
    (hF₀ : ∀ p ∈ F₀, p.totalDegree ≤ b')
    (ℓ : MvPolynomial V (ZMod 2)) (hℓ : ℓ.totalDegree ≤ 1)
    (D₁ D₂ : ℕ)
    (h1 : PCDerivable F₀ D₁ ℓ)
    (h2 : PCDerivable (F₀ ∪ {ℓ}) D₂ 1) :
    PCDerivable F₀ (max D₂ (max D₁ b')) 1 := by
  set B := max D₂ (max D₁ b') with hBdef
  have h2B : PCDerivable (F₀ ∪ {ℓ}) B 1 :=
    pcDerivable_mono h2 (le_max_left _ _) subset_rfl
  rcases deg1_cases ℓ hℓ with rfl | rfl | ⟨v₀, g, hgdeg, hgno, hℓeq⟩
  · refine pcDerivable_subst_ax h2B fun a ha hadeg => ?_
    rcases ha with haF | ha0
    · exact .ax haF hadeg
    · rw [Set.mem_singleton_iff] at ha0; subst ha0; exact .zero
  · exact pcDerivable_mono h1 ((le_max_left _ _).trans (le_max_right _ _)) subset_rfl
  · set φ : V → MvPolynomial V (ZMod 2) := Function.update X v₀ g with hφdef
    have hφdeg : ∀ j : V, (φ j).totalDegree ≤ 1 := by
      intro j
      by_cases hj : j = v₀
      · subst hj; simpa [hφdef] using hgdeg
      · rw [hφdef, Function.update_of_ne hj, totalDegree_X]
    have hσg : bind₁ φ g = g := bind₁_update_eq_self v₀ g g hgno
    have hσℓ : bind₁ φ ℓ = 0 := by
      rw [hℓeq, map_add, bind₁_X_right, hφdef, Function.update_self, hσg, zmod2_add_self]
    have hrep := pcDerivable_replay (F := F₀ ∪ {ℓ}) (G := F₀) (T := 1) (D := B) (s := 0)
      φ hφdeg 1 (by simp) ?_ h2B
    · simpa using hrep
    · intro a ha _
      simp only [one_mul, add_zero]
      rcases ha with haF | haℓ
      · have had : a.totalDegree ≤ b' := hF₀ a haF
        obtain ⟨Q, hQdeg, hQeq⟩ := subVar_diff_factor v₀ g hgdeg b' a had
        have hσa : bind₁ φ a = a + Q * ℓ := by
          rw [hφdef, hℓeq, ← hQeq, zmod2_add_cancel_left]
        rw [hσa]
        have hax : PCDerivable F₀ B a :=
          .ax haF (had.trans (by omega))
        have h1B : PCDerivable F₀ B ℓ :=
          pcDerivable_mono h1 (by omega) subset_rfl
        have hQℓ : PCDerivable F₀ B (Q * ℓ) := by
          have hm := pcDerivable_mul_left h1B Q
          have hbd : Q.totalDegree + ℓ.totalDegree ≤ B := by omega
          rwa [max_eq_left hbd] at hm
        exact .add hax hQℓ
      · rw [Set.mem_singleton_iff] at haℓ
        rw [haℓ, hσℓ]
        exact .zero
private lemma nat_log2_succ_le {W₁ W : ℕ} (h1 : 1 ≤ W₁) (h2 : 2 * W₁ ≤ W) :
    Nat.log 2 W₁ + 1 ≤ Nat.log 2 W := by
  refine Nat.le_log_of_pow_le (by omega) ?_
  have hp : 2 ^ Nat.log 2 W₁ ≤ W₁ := Nat.pow_log_le_self 2 (by omega)
  rw [pow_succ, mul_comm]
  omega
private lemma combine_linear {V : Type} [DecidableEq V]
    (F_PC : Set (MvPolynomial V (ZMod 2))) (b' k : ℕ) (hb' : 2 ≤ b')
    (hBool : ∀ v : V, X v * X v + X v ∈ F_PC)
    (hF_deg : ∀ p ∈ F_PC, p.totalDegree ≤ b')
    (L : Finset (MvPolynomial V (ZMod 2))) (hL : ∀ q ∈ L, q.totalDegree ≤ 1)
    (ℓ : MvPolynomial V (ZMod 2)) (hℓ : ℓ.totalDegree ≤ 1)
    (W₁ W₂ W : ℕ) (hsum : W₁ + W₂ ≤ W)
    (hside1 : (W₁ = 0 → ∀ a : V → ZMod 2, (∀ q ∈ insert ℓ L, eval a q = 0) → False) ∧
      (1 ≤ W₁ → PCDerivable (F_PC ∪ ((insert ℓ L : Finset (MvPolynomial V (ZMod 2))) : Set (MvPolynomial V (ZMod 2))))
        (b' * k + b' + Nat.log 2 W₁) 1))
    (hside2 : (W₂ = 0 → ∀ a : V → ZMod 2, (∀ q ∈ insert (ℓ + 1) L, eval a q = 0) → False) ∧
      (1 ≤ W₂ → PCDerivable (F_PC ∪ ((insert (ℓ + 1) L : Finset (MvPolynomial V (ZMod 2))) : Set (MvPolynomial V (ZMod 2))))
        (b' * k + b' + Nat.log 2 W₂) 1)) :
    (W = 0 → ∀ a : V → ZMod 2, (∀ q ∈ L, eval a q = 0) → False) ∧
    (1 ≤ W → PCDerivable (F_PC ∪ (L : Set (MvPolynomial V (ZMod 2))))
      (b' * k + b' + Nat.log 2 W) 1) := by
  set F₀ : Set (MvPolynomial V (ZMod 2)) := F_PC ∪ (L : Set (MvPolynomial V (ZMod 2)))
  have hBool₀ : ∀ v : V, X v * X v + X v ∈ F₀ := fun v => Or.inl (hBool v)
  have hF₀_deg : ∀ p ∈ F₀, p.totalDegree ≤ b' := by
    intro p hp
    rcases hp with hpF | hpL
    · exact hF_deg p hpF
    · exact (hL p hpL).trans (by omega)
  have hℓ1_deg : (ℓ + 1).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le hℓ ?_)
    simp
  have hins_eq : ∀ r : MvPolynomial V (ZMod 2),
      F_PC ∪ ((insert r L : Finset (MvPolynomial V (ZMod 2))) : Set (MvPolynomial V (ZMod 2))) =
        F₀ ∪ {r} := by
    intro r
    ext p
    simp only [F₀, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hbot : ∀ a : V → ZMod 2, (∀ q ∈ L, eval a q = 0) →
      (∀ q ∈ insert ℓ L, eval a q = 0) ∨ (∀ q ∈ insert (ℓ + 1) L, eval a q = 0) := by
    intro a ha
    rcases zmod2_eq_zero_or_one (eval a ℓ) with h0 | h1
    · left
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqL
      · exact h0
      · exact ha q hqL
    · right
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqL
      · simp only [map_add, map_one, h1]; decide
      · exact ha q hqL
  constructor
  · intro hW0 a ha
    have hW1 : W₁ = 0 := by omega
    have hW2 : W₂ = 0 := by omega
    rcases hbot a ha with h1 | h2
    · exact hside1.1 hW1 a h1
    · exact hside2.1 hW2 a h2
  · intro _
    by_cases h10 : W₁ = 0
    · by_cases h20 : W₂ = 0
      · have hvan : ∀ a : V → ZMod 2, (∀ q ∈ L, eval a q = 0) → eval a 1 = 0 := by
          intro a ha
          rcases hbot a ha with h1 | h2
          · exact False.elim (hside1.1 h10 a h1)
          · exact False.elim (hside2.1 h20 a h2)
        exact affine_nullstellensatz F_PC hBool (b' * k + b' + Nat.log 2 W) (by omega)
          L.card L le_rfl hL 1 (by simp) hvan
      · have hW2pos : 1 ≤ W₂ := by omega
        have hvan : ∀ a : V → ZMod 2, (∀ q ∈ L, eval a q = 0) → eval a (ℓ + 1) = 0 := by
          intro a ha
          rcases hbot a ha with h1 | h2
          · exact False.elim (hside1.1 h10 a h1)
          · exact h2 (ℓ + 1) (Finset.mem_insert_self _ _)
        have hder_ℓ1 : PCDerivable F₀ 1 (ℓ + 1) :=
          affine_nullstellensatz F_PC hBool 1 le_rfl L.card L le_rfl hL (ℓ + 1) hℓ1_deg hvan
        have h2 := hside2.2 hW2pos
        rw [hins_eq] at h2
        have h2' : PCDerivable (F₀ ∪ {ℓ + 1}) (b' * k + b' + Nat.log 2 W) 1 :=
          pcDerivable_mono h2 (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) subset_rfl
        refine pcDerivable_subst_ax h2' fun a ha hadeg => ?_
        rcases ha with haF₀ | haℓ1
        · exact .ax haF₀ hadeg
        · rw [Set.mem_singleton_iff] at haℓ1; subst haℓ1
          exact pcDerivable_mono hder_ℓ1 (by omega) subset_rfl
    · have hW1pos : 1 ≤ W₁ := by omega
      by_cases h20 : W₂ = 0
      · have hvan : ∀ a : V → ZMod 2, (∀ q ∈ L, eval a q = 0) → eval a ℓ = 0 := by
          intro a ha
          rcases hbot a ha with h1 | h2
          · exact h1 ℓ (Finset.mem_insert_self _ _)
          · exact False.elim (hside2.1 h20 a h2)
        have hder_ℓ : PCDerivable F₀ 1 ℓ :=
          affine_nullstellensatz F_PC hBool 1 le_rfl L.card L le_rfl hL ℓ hℓ hvan
        have h1 := hside1.2 hW1pos
        rw [hins_eq] at h1
        have h1' : PCDerivable (F₀ ∪ {ℓ}) (b' * k + b' + Nat.log 2 W) 1 :=
          pcDerivable_mono h1 (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) subset_rfl
        refine pcDerivable_subst_ax h1' fun a ha hadeg => ?_
        rcases ha with haF₀ | haℓ
        · exact .ax haF₀ hadeg
        · rw [Set.mem_singleton_iff] at haℓ; subst haℓ
          exact pcDerivable_mono hder_ℓ (by omega) subset_rfl
      · have hW2pos : 1 ≤ W₂ := by omega
        have h1 := hside1.2 hW1pos
        have h2 := hside2.2 hW2pos
        rw [hins_eq] at h1 h2
        by_cases hle : W₁ ≤ W₂
        · have hlog1 : Nat.log 2 W₁ + 1 ≤ Nat.log 2 W := nat_log2_succ_le hW1pos (by omega)
          have hlog2 : Nat.log 2 W₂ ≤ Nat.log 2 W := Nat.log_mono_right (by omega)
          have hmul := pc_mul_affine F₀ hBool₀ ℓ hℓ (b' * k + b' + Nat.log 2 W₁) (by omega) h1
          have hrep := pc_subst_replay F₀ b' (by omega) hF₀_deg (ℓ + 1) hℓ1_deg
            (b' * k + b' + Nat.log 2 W₁ + 1) (b' * k + b' + Nat.log 2 W₂) hmul h2
          exact pcDerivable_mono hrep (by omega) subset_rfl
        · have hlog2 : Nat.log 2 W₂ + 1 ≤ Nat.log 2 W := nat_log2_succ_le hW2pos (by omega)
          have hlog1 : Nat.log 2 W₁ ≤ Nat.log 2 W := Nat.log_mono_right (by omega)
          have hmul := pc_mul_affine F₀ hBool₀ (ℓ + 1) hℓ1_deg (b' * k + b' + Nat.log 2 W₂) (by omega) h2
          rw [zmod2_add_cancel_right] at hmul
          have hrep := pc_subst_replay F₀ b' (by omega) hF₀_deg ℓ hℓ
            (b' * k + b' + Nat.log 2 W₂ + 1) (b' * k + b' + Nat.log 2 W₁) hmul h1
          exact pcDerivable_mono hrep (by omega) subset_rfl
private def Lset (leaves : Finset (List Bool)) (u : List Bool) : Finset (List Bool) :=
  leaves.filter (List.IsPrefix u)
private def rwgt {V : Type} (ask : List Bool → LinTerm V) (u p : List Bool) : ℕ :=
  2 ^ (Finset.univ.filter fun i : Fin p.length =>
    u.length ≤ i.val ∧ p.get i = false ∧ (ask (p.take i.val)).card = 2).card
private def subW {V : Type} (leaves : Finset (List Bool)) (ask : List Bool → LinTerm V)
    (u : List Bool) : ℕ :=
  ∑ p ∈ Lset leaves u, rwgt ask u p
private lemma rwgt_pos {V : Type} (ask : List Bool → LinTerm V) (u p : List Bool) :
    1 ≤ rwgt ask u p := Nat.one_le_two_pow
private lemma subW_eq_zero_iff {V : Type} (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V) (u : List Bool) :
    subW leaves ask u = 0 ↔ Lset leaves u = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpos : 1 ≤ rwgt ask u p := rwgt_pos ask u p
    have hle : rwgt ask u p ≤ subW leaves ask u :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
    omega
  · intro h; simp [subW, h]
private lemma prefix_append_singleton_iff (u p : List Bool) (b : Bool) :
    List.IsPrefix (u ++ [b]) p ↔
      ∃ h : u.length < p.length, List.IsPrefix u p ∧ p.get ⟨u.length, h⟩ = b := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨by simp, ⟨b :: t, by simp⟩, ?_⟩
    simp
  · rintro ⟨hlt, ⟨t, rfl⟩, hget⟩
    cases t with
    | nil => simp at hlt
    | cons c t' =>
      have hc : c = b := by simpa using hget
      subst hc
      exact ⟨t', by simp⟩
private lemma follows_append_singleton {V : Type} (ask : List Bool → LinTerm V)
    (u : List Bool) (b : Bool) (x : V → Bool) :
    (∀ i : Fin (u ++ [b]).length, (u ++ [b]).get i = true ↔
        LinTermSat x (ask ((u ++ [b]).take i.val))) ↔
      (∀ i : Fin u.length, u.get i = true ↔ LinTermSat x (ask (u.take i.val))) ∧
      (b = true ↔ LinTermSat x (ask u)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h ⟨i.val, by simp⟩
      have hget : (u ++ [b]).get ⟨i.val, by simp⟩ = u.get i := by
        simp [List.getElem_append_left i.isLt]
      have htake : (u ++ [b]).take i.val = u.take i.val := by
        rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
      rwa [hget, htake] at hi
    · have hi := h ⟨u.length, by simp⟩
      have hget : (u ++ [b]).get ⟨u.length, by simp⟩ = b := by simp
      have htake : (u ++ [b]).take u.length = u := by simp
      rwa [hget, htake] at hi
  · rintro ⟨hu, hb⟩ i
    have hlen : (u ++ [b]).length = u.length + 1 := by simp
    by_cases hlt : i.val < u.length
    · have hget : (u ++ [b]).get i = u.get ⟨i.val, hlt⟩ := by
        simp [List.getElem_append_left hlt]
      have htake : (u ++ [b]).take i.val = u.take i.val := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      rw [hget, htake]
      exact hu ⟨i.val, hlt⟩
    · have heq : i.val = u.length := by omega
      have hget : (u ++ [b]).get i = b := by
        simp [List.get_eq_getElem, heq]
      have htake : (u ++ [b]).take i.val = u := by rw [heq]; simp
      rw [hget, htake]
      exact hb
private lemma follows_comparable {V : Type} (ask : List Bool → LinTerm V)
    (u p : List Bool) (x : V → Bool)
    (hu : ∀ i : Fin u.length, u.get i = true ↔ LinTermSat x (ask (u.take i.val)))
    (hp : ∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val))) :
    List.IsPrefix u p ∨ List.IsPrefix p u := by
  have htake : ∀ k ≤ min u.length p.length, u.take k = p.take k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hku : k < u.length := by omega
      have hkp : k < p.length := by omega
      have hprev : u.take k = p.take k := ih (by omega)
      have hbit : u[k] = p[k] := by
        rw [Bool.eq_iff_iff]
        have h1 : u.get ⟨k, hku⟩ = true ↔ LinTermSat x (ask (u.take k)) := hu ⟨k, hku⟩
        have h2 : p.get ⟨k, hkp⟩ = true ↔ LinTermSat x (ask (p.take k)) := hp ⟨k, hkp⟩
        rw [hprev] at h1
        exact h1.trans h2.symm
      rw [List.take_succ_eq_append_getElem hku, List.take_succ_eq_append_getElem hkp, hprev, hbit]
  by_cases hle : u.length ≤ p.length
  · left
    have h1 := htake u.length (by omega)
    rw [List.take_length] at h1
    rw [h1]
    exact List.take_prefix u.length p
  · right
    have h1 := htake p.length (by omega)
    rw [List.take_length] at h1
    rw [← h1]
    exact List.take_prefix p.length u
private lemma rwgt_child_true {V : Type} (ask : List Bool → LinTerm V)
    (u p : List Bool) (hp : List.IsPrefix (u ++ [true]) p) :
    rwgt ask u p = rwgt ask (u ++ [true]) p := by
  obtain ⟨hlt, _, hget⟩ := (prefix_append_singleton_iff u p true).mp hp
  unfold rwgt
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hge, hpf, hcard⟩
    refine ⟨?_, hpf, hcard⟩
    by_contra hlt'
    have heq : i = ⟨u.length, hlt⟩ := Fin.ext (by dsimp; omega)
    rw [heq, hget] at hpf
    exact Bool.noConfusion hpf
  · rintro ⟨hge, hpf, hcard⟩
    exact ⟨by omega, hpf, hcard⟩
private lemma rwgt_child_false_lt2 {V : Type} (ask : List Bool → LinTerm V)
    (u p : List Bool) (hp : List.IsPrefix (u ++ [false]) p) (hcard : (ask u).card ≠ 2) :
    rwgt ask u p = rwgt ask (u ++ [false]) p := by
  obtain ⟨hlt, hpref, _⟩ := (prefix_append_singleton_iff u p false).mp hp
  have htake : p.take u.length = u := by
    obtain ⟨t, rfl⟩ := hpref
    simp
  unfold rwgt
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hge, hpf, hc⟩
    refine ⟨?_, hpf, hc⟩
    by_contra hlt'
    have heq : i.val = u.length := by omega
    rw [heq, htake] at hc
    exact hcard hc
  · rintro ⟨hge, hpf, hc⟩
    exact ⟨by omega, hpf, hc⟩
private lemma rwgt_child_false_eq2 {V : Type} (ask : List Bool → LinTerm V)
    (u p : List Bool) (hp : List.IsPrefix (u ++ [false]) p) (hcard : (ask u).card = 2) :
    rwgt ask u p = 2 * rwgt ask (u ++ [false]) p := by
  obtain ⟨hlt, hpref, hget⟩ := (prefix_append_singleton_iff u p false).mp hp
  have htake : p.take u.length = u := by
    obtain ⟨t, rfl⟩ := hpref
    simp
  set S1 := Finset.univ.filter fun i : Fin p.length =>
    u.length ≤ i.val ∧ p.get i = false ∧ (ask (p.take i.val)).card = 2
  set S2 := Finset.univ.filter fun i : Fin p.length =>
    (u ++ [false]).length ≤ i.val ∧ p.get i = false ∧ (ask (p.take i.val)).card = 2
  set i0 : Fin p.length := ⟨u.length, hlt⟩
  have hi0_not : i0 ∉ S2 := by
    simp [S2, i0]
  have hS1_eq : S1 = insert i0 S2 := by
    ext i
    simp only [S1, S2, i0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      List.length_append, List.length_singleton, Fin.ext_iff]
    constructor
    · rintro ⟨hge, hpf, hc⟩
      by_cases heq : i.val = u.length
      · left; exact heq
      · right; exact ⟨by omega, hpf, hc⟩
    · rintro (heq | ⟨hge, hpf, hc⟩)
      · refine ⟨by omega, ?_, ?_⟩
        · have hi : i = ⟨u.length, hlt⟩ := Fin.ext heq
          rw [hi]; exact hget
        · rw [heq, htake]; exact hcard
      · exact ⟨by omega, hpf, hc⟩
  change 2 ^ S1.card = 2 * 2 ^ S2.card
  rw [hS1_eq, Finset.card_insert_of_notMem hi0_not, pow_succ, mul_comm]
private lemma Lset_split {leaves : Finset (List Bool)} {u : List Bool} (hu : u ∉ leaves) :
    Lset leaves u = Lset leaves (u ++ [true]) ∪ Lset leaves (u ++ [false]) ∧
      Disjoint (Lset leaves (u ++ [true])) (Lset leaves (u ++ [false])) := by
  constructor
  · ext p
    simp only [Lset, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpref⟩
      have hne : u ≠ p := fun h => hu (h ▸ hp)
      have hlt : u.length < p.length := by
        obtain ⟨t, rfl⟩ := hpref
        cases t with
        | nil => exfalso; exact hne (by simp)
        | cons _ _ => simp
      cases hb : p.get ⟨u.length, hlt⟩ with
      | true =>
        left; exact ⟨hp, (prefix_append_singleton_iff u p true).mpr ⟨hlt, hpref, hb⟩⟩
      | false =>
        right; exact ⟨hp, (prefix_append_singleton_iff u p false).mpr ⟨hlt, hpref, hb⟩⟩
    · rintro (⟨hp, hpref⟩ | ⟨hp, hpref⟩)
      · exact ⟨hp, ((prefix_append_singleton_iff u p true).mp hpref).2.1⟩
      · exact ⟨hp, ((prefix_append_singleton_iff u p false).mp hpref).2.1⟩
  · rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Lset, Finset.mem_filter] at h1 h2
    obtain ⟨hlt, _, ht⟩ := (prefix_append_singleton_iff u p true).mp h1.2
    obtain ⟨_, _, hf⟩ := (prefix_append_singleton_iff u p false).mp h2.2
    rw [ht] at hf
    exact Bool.noConfusion hf
private lemma subW_split_lt2 {V : Type} (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V) (u : List Bool) (hu : u ∉ leaves) (hcard : (ask u).card ≠ 2) :
    subW leaves ask u = subW leaves ask (u ++ [true]) + subW leaves ask (u ++ [false]) := by
  obtain ⟨hun, hdisj⟩ := Lset_split hu
  unfold subW
  rw [hun, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact rwgt_child_true ask u p (Finset.mem_filter.mp hp).2
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact rwgt_child_false_lt2 ask u p (Finset.mem_filter.mp hp).2 hcard
private lemma subW_split_eq2 {V : Type} (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V) (u : List Bool) (hu : u ∉ leaves) (hcard : (ask u).card = 2) :
    subW leaves ask u = subW leaves ask (u ++ [true]) + 2 * subW leaves ask (u ++ [false]) := by
  obtain ⟨hun, hdisj⟩ := Lset_split hu
  unfold subW
  rw [hun, Finset.sum_union hdisj, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact rwgt_child_true ask u p (Finset.mem_filter.mp hp).2
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact rwgt_child_false_eq2 ask u p (Finset.mem_filter.mp hp).2 hcard
private lemma tree_pc_derivable {V : Type} [DecidableEq V]
    (F : Set (Clause V)) (b' k : ℕ) (hb' : 2 ≤ b')
    (hF_deg : ∀ cl ∈ F, (clausePoly cl).totalDegree ≤ b')
    (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V)
    (out : List Bool → Finset (Clause V))
    (hpref_free : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    (hcomp : ∀ x : V → Bool, ∃ p ∈ leaves,
      ∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val)))
    (hask2 : ∀ p ∈ leaves, ∀ i : Fin p.length, (ask (p.take i.val)).card ≤ 2)
    (hout_card : ∀ p ∈ leaves, (out p).card ≤ k ∧ ∀ cl ∈ out p, cl ∈ F)
    (hout_unsat : ∀ p ∈ leaves, ∀ x : V → Bool,
      (∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val))) →
      ∃ cl ∈ out p, ¬ ClauseSat x cl) :
    ∀ (m : ℕ) (u : List Bool) (L : Finset (MvPolynomial V (ZMod 2))),
      leaves.sup List.length - u.length ≤ m →
      (∀ p ∈ leaves, List.IsPrefix p u → p = u) →
      (∀ ℓ ∈ L, ℓ.totalDegree ≤ 1) →
      (∀ x : V → Bool, (∀ ℓ ∈ L, eval (b2f x) ℓ = 0) →
        ∀ i : Fin u.length, u.get i = true ↔ LinTermSat x (ask (u.take i.val))) →
      (subW leaves ask u = 0 → ∀ a : V → ZMod 2, (∀ ℓ ∈ L, eval a ℓ = 0) → False) ∧
      (1 ≤ subW leaves ask u →
        PCDerivable (cnfSystem F ∪ (L : Set (MvPolynomial V (ZMod 2))))
          (b' * k + b' + Nat.log 2 (subW leaves ask u)) 1) := by
  classical
  have hBool : ∀ v : V, X v * X v + X v ∈ cnfSystem F := fun v => Or.inl ⟨v, rfl⟩
  have hFPC_deg : ∀ p ∈ cnfSystem F, p.totalDegree ≤ b' := by
    intro p hp
    rcases hp with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
    · have h2 : (X v * X v + X v : MvPolynomial V (ZMod 2)).totalDegree ≤ 2 := by
        refine (totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X]
        · rw [totalDegree_X]; omega
      omega
    · exact hF_deg C hC
  intro m
  induction m with
  | zero =>
    intro u L hm hnostrict hL hfol
    by_cases hW0 : subW leaves ask u = 0
    · refine ⟨fun _ a ha => ?_, fun h1 => by omega⟩
      have hLempty : Lset leaves u = ∅ := (subW_eq_zero_iff leaves ask u).mp hW0
      set x := f2b a
      have hx_fol := hfol x (fun ℓ hℓ => by rw [b2f_f2b]; exact ha ℓ hℓ)
      obtain ⟨p, hp, hp_fol⟩ := hcomp x
      rcases follows_comparable ask u p x hx_fol hp_fol with hup | hpu
      · have : p ∈ Lset leaves u := Finset.mem_filter.mpr ⟨hp, hup⟩
        rw [hLempty] at this
        exact Finset.notMem_empty p this
      · have hpeq : p = u := hnostrict p hp hpu
        have : p ∈ Lset leaves u := Finset.mem_filter.mpr ⟨hp, by rw [hpeq]⟩
        rw [hLempty] at this
        exact Finset.notMem_empty p this
    · refine ⟨fun h => absurd h hW0, fun _ => ?_⟩
      have hne : (Lset leaves u).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (mt (subW_eq_zero_iff leaves ask u).mpr hW0)
      obtain ⟨p₀, hp₀⟩ := hne
      obtain ⟨hp₀_mem, hp₀_pref⟩ := Finset.mem_filter.mp hp₀
      have hp₀_len : p₀.length ≤ leaves.sup List.length := Finset.le_sup hp₀_mem
      have hu_eq : u = p₀ := by
        obtain ⟨t, ht⟩ := hp₀_pref
        have htlen : t.length = 0 := by
          have : p₀.length = u.length + t.length := by rw [← ht, List.length_append]
          omega
        have ht0 : t = [] := List.eq_nil_of_length_eq_zero htlen
        rw [← ht, ht0, List.append_nil]
      subst hu_eq
      have hLset_eq : Lset leaves u = {u} := by
        ext q
        simp only [Lset, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun ⟨hq, hqp⟩ => (hpref_free u hp₀_mem q hq hqp).symm,
          fun hq => by subst hq; exact ⟨hp₀_mem, List.prefix_rfl⟩⟩
      have hW1 : subW leaves ask u = 1 := by
        unfold subW
        rw [hLset_eq, Finset.sum_singleton, rwgt]
        have hf0 : (Finset.univ.filter fun i : Fin u.length =>
            u.length ≤ i.val ∧ u.get i = false ∧ (ask (u.take i.val)).card = 2) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h; exact Nat.not_le.mpr i.isLt h.1
        rw [hf0, Finset.card_empty, pow_zero]
      have hout := hout_card u hp₀_mem
      have hder1 : PCDerivable (cnfSystem F ∪ (L : Set (MvPolynomial V (ZMod 2))))
          (b' * k + b' + Nat.log 2 (subW leaves ask u)) (1 + satProd (out u)) := by
        have h1 := pc_one_add_satProd F b' (out u) hout.2 (fun cl hcl => hF_deg cl (hout.2 cl hcl))
        refine pcDerivable_mono h1 ?_ Set.subset_union_left
        have hmk : b' * (out u).card ≤ b' * k := Nat.mul_le_mul_left b' hout.1
        omega
      have hder2 : PCDerivable (cnfSystem F ∪ (L : Set (MvPolynomial V (ZMod 2))))
          (b' * k + b' + Nat.log 2 (subW leaves ask u)) (satProd (out u)) := by
        refine affine_nullstellensatz (cnfSystem F) hBool
          (b' * k + b' + Nat.log 2 (subW leaves ask u)) (by omega)
          L.card L le_rfl hL (satProd (out u)) ?_ ?_
        · have hsd := satProd_deg b' (out u) (fun cl hcl => hF_deg cl (hout.2 cl hcl))
          have hmk : b' * (out u).card ≤ b' * k := Nat.mul_le_mul_left b' hout.1
          omega
        · intro a ha
          set x := f2b a
          have hx_fol := hfol x (fun ℓ hℓ => by rw [b2f_f2b]; exact ha ℓ hℓ)
          rw [← b2f_f2b a, eval_satProd]
          exact hout_unsat u hp₀_mem x hx_fol
      have hsum := PCDerivable.add hder1 hder2
      rwa [zmod2_add_cancel_right] at hsum
  | succ m ih =>
    intro u L hm hnostrict hL hfol
    by_cases hW0 : subW leaves ask u = 0
    · refine ⟨fun _ a ha => ?_, fun h1 => by omega⟩
      have hLempty : Lset leaves u = ∅ := (subW_eq_zero_iff leaves ask u).mp hW0
      set x := f2b a
      have hx_fol := hfol x (fun ℓ hℓ => by rw [b2f_f2b]; exact ha ℓ hℓ)
      obtain ⟨p, hp, hp_fol⟩ := hcomp x
      rcases follows_comparable ask u p x hx_fol hp_fol with hup | hpu
      · have : p ∈ Lset leaves u := Finset.mem_filter.mpr ⟨hp, hup⟩
        rw [hLempty] at this
        exact Finset.notMem_empty p this
      · have hpeq : p = u := hnostrict p hp hpu
        have : p ∈ Lset leaves u := Finset.mem_filter.mpr ⟨hp, by rw [hpeq]⟩
        rw [hLempty] at this
        exact Finset.notMem_empty p this
    · refine ⟨fun h => absurd h hW0, fun hWpos => ?_⟩
      by_cases huleaf : u ∈ leaves
      · have hout := hout_card u huleaf
        have hder1 : PCDerivable (cnfSystem F ∪ (L : Set (MvPolynomial V (ZMod 2))))
            (b' * k + b' + Nat.log 2 (subW leaves ask u)) (1 + satProd (out u)) := by
          have h1 := pc_one_add_satProd F b' (out u) hout.2 (fun cl hcl => hF_deg cl (hout.2 cl hcl))
          refine pcDerivable_mono h1 ?_ Set.subset_union_left
          have hmk : b' * (out u).card ≤ b' * k := Nat.mul_le_mul_left b' hout.1
          omega
        have hder2 : PCDerivable (cnfSystem F ∪ (L : Set (MvPolynomial V (ZMod 2))))
            (b' * k + b' + Nat.log 2 (subW leaves ask u)) (satProd (out u)) := by
          refine affine_nullstellensatz (cnfSystem F) hBool
            (b' * k + b' + Nat.log 2 (subW leaves ask u)) (by omega)
            L.card L le_rfl hL (satProd (out u)) ?_ ?_
          · have hsd := satProd_deg b' (out u) (fun cl hcl => hF_deg cl (hout.2 cl hcl))
            have hmk : b' * (out u).card ≤ b' * k := Nat.mul_le_mul_left b' hout.1
            omega
          · intro a ha
            set x := f2b a
            have hx_fol := hfol x (fun ℓ hℓ => by rw [b2f_f2b]; exact ha ℓ hℓ)
            rw [← b2f_f2b a, eval_satProd]
            exact hout_unsat u huleaf x hx_fol
        have hsum := PCDerivable.add hder1 hder2
        rwa [zmod2_add_cancel_right] at hsum
      · have hne : (Lset leaves u).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr (mt (subW_eq_zero_iff leaves ask u).mpr hW0)
        obtain ⟨p₀, hp₀⟩ := hne
        obtain ⟨hp₀_mem, hp₀_pref⟩ := Finset.mem_filter.mp hp₀
        have hu_lt_p0 : u.length < p₀.length := by
          obtain ⟨t, ht⟩ := hp₀_pref
          cases t with
          | nil =>
            exfalso
            have : u = p₀ := by simpa using ht
            exact huleaf (this ▸ hp₀_mem)
          | cons _ _ =>
            rw [← ht]; simp
        have hp₀_len : p₀.length ≤ leaves.sup List.length := Finset.le_sup hp₀_mem
        have hm_child : ∀ b : Bool, leaves.sup List.length - (u ++ [b]).length ≤ m := by
          intro b; simp only [List.length_append, List.length_singleton]; omega
        have hns_child : ∀ b : Bool, ∀ p ∈ leaves, List.IsPrefix p (u ++ [b]) → p = u ++ [b] := by
          intro b p hp hpu
          by_cases hlen : p.length ≤ u.length
          · obtain ⟨t, ht⟩ := hpu
            have hpu' : List.IsPrefix p u := by
              have htake := congrArg (List.take p.length) ht
              rw [List.take_left, List.take_append_of_le_length hlen] at htake
              rw [htake]
              exact List.take_prefix p.length u
            have hpeq := hnostrict p hp hpu'
            exact absurd (hpeq ▸ hp) huleaf
          · obtain ⟨t, ht⟩ := hpu
            have htlen : t.length = 0 := by
              have : (u ++ [b]).length = p.length + t.length := by rw [← ht, List.length_append]
              simp only [List.length_append, List.length_singleton] at this
              omega
            have ht0 : t = [] := List.eq_nil_of_length_eq_zero htlen
            rw [← ht, ht0, List.append_nil]
        have hask_le2 : (ask u).card ≤ 2 := by
          have htake : p₀.take u.length = u := by
            obtain ⟨t, rfl⟩ := hp₀_pref; simp
          have := hask2 p₀ hp₀_mem ⟨u.length, hu_lt_p0⟩
          rwa [htake] at this
        have hcase : (ask u).card = 0 ∨ (ask u).card = 1 ∨ (ask u).card = 2 := by omega
        rcases hcase with hcard0 | hcard1 | hcard2
        · have hempty : ask u = ∅ := Finset.card_eq_zero.mp hcard0
          have hfol_T : ∀ x : V → Bool, (∀ ℓ ∈ L, eval (b2f x) ℓ = 0) →
              ∀ i : Fin (u ++ [true]).length,
                (u ++ [true]).get i = true ↔ LinTermSat x (ask ((u ++ [true]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x hx, ?_⟩
            simp [LinTermSat, hempty]
          have hT := ih (u ++ [true]) L (hm_child true) (hns_child true) hL hfol_T
          have hWsplit := subW_split_lt2 leaves ask u huleaf (by omega)
          by_cases hWT0 : subW leaves ask (u ++ [true]) = 0
          · have hvan : ∀ a : V → ZMod 2, (∀ ℓ ∈ L, eval a ℓ = 0) → eval a 1 = 0 :=
              fun a ha => False.elim (hT.1 hWT0 a ha)
            exact affine_nullstellensatz (cnfSystem F) hBool
              (b' * k + b' + Nat.log 2 (subW leaves ask u)) (by omega)
              L.card L le_rfl hL 1 (by simp) hvan
          · exact pcDerivable_mono (hT.2 (by omega))
              (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) subset_rfl
        · obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hcard1
          set ℓ := linEqPoly e with hℓdef
          have hℓdeg : ℓ.totalDegree ≤ 1 := linEqPoly_deg e
          have hℓ1deg : (ℓ + 1).totalDegree ≤ 1 := by
            refine (totalDegree_add _ _).trans (max_le hℓdeg ?_)
            simp
          have hL_T : ∀ q ∈ insert ℓ L, q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓdeg
            · exact hL q hqL
          have hL_F : ∀ q ∈ insert (ℓ + 1) L, q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓ1deg
            · exact hL q hqL
          have hfol_T : ∀ x : V → Bool, (∀ q ∈ insert ℓ L, eval (b2f x) q = 0) →
              ∀ i : Fin (u ++ [true]).length,
                (u ++ [true]).get i = true ↔ LinTermSat x (ask ((u ++ [true]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x (fun q hq => hx q (Finset.mem_insert_of_mem hq)), ?_⟩
            simp only [true_iff, LinTermSat, heq, Finset.mem_singleton, forall_eq]
            exact (eval_linEqPoly x e).mp (hx ℓ (Finset.mem_insert_self ℓ L))
          have hfol_F : ∀ x : V → Bool, (∀ q ∈ insert (ℓ + 1) L, eval (b2f x) q = 0) →
              ∀ i : Fin (u ++ [false]).length,
                (u ++ [false]).get i = true ↔ LinTermSat x (ask ((u ++ [false]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x (fun q hq => hx q (Finset.mem_insert_of_mem hq)), ?_⟩
            simp only [Bool.false_eq_true, false_iff, LinTermSat, heq, Finset.mem_singleton, forall_eq]
            have h1 : eval (b2f x) (ℓ + 1) = 0 := hx (ℓ + 1) (Finset.mem_insert_self _ _)
            rw [map_add, map_one, zmod2_add_one_eq_zero_iff] at h1
            exact mt (eval_linEqPoly x e).mpr h1
          have hT := ih (u ++ [true]) (insert ℓ L) (hm_child true) (hns_child true) hL_T hfol_T
          have hF := ih (u ++ [false]) (insert (ℓ + 1) L) (hm_child false) (hns_child false) hL_F hfol_F
          have hWsplit := subW_split_lt2 leaves ask u huleaf (by omega)
          exact (combine_linear (cnfSystem F) b' k hb' hBool hFPC_deg L hL ℓ hℓdeg
            (subW leaves ask (u ++ [true])) (subW leaves ask (u ++ [false])) (subW leaves ask u)
            (by omega) hT hF).2 hWpos
        · obtain ⟨e₁, e₂, _, heq⟩ := Finset.card_eq_two.mp hcard2
          set ℓ₁ := linEqPoly e₁
          set ℓ₂ := linEqPoly e₂
          have hℓ₁deg : ℓ₁.totalDegree ≤ 1 := linEqPoly_deg e₁
          have hℓ₂deg : ℓ₂.totalDegree ≤ 1 := linEqPoly_deg e₂
          have hℓ₁1deg : (ℓ₁ + 1).totalDegree ≤ 1 :=
            (totalDegree_add _ _).trans (max_le hℓ₁deg (by simp))
          have hℓ₂1deg : (ℓ₂ + 1).totalDegree ≤ 1 :=
            (totalDegree_add _ _).trans (max_le hℓ₂deg (by simp))
          have hL1 : ∀ q ∈ insert ℓ₁ L, q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓ₁deg
            · exact hL q hqL
          have hL12 : ∀ q ∈ insert ℓ₂ (insert ℓ₁ L), q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓ₂deg
            · exact hL1 q hqL
          have hL12' : ∀ q ∈ insert (ℓ₂ + 1) (insert ℓ₁ L), q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓ₂1deg
            · exact hL1 q hqL
          have hL1' : ∀ q ∈ insert (ℓ₁ + 1) L, q.totalDegree ≤ 1 := fun q hq => by
            rcases Finset.mem_insert.mp hq with rfl | hqL
            · exact hℓ₁1deg
            · exact hL q hqL
          have hfol_TT : ∀ x : V → Bool, (∀ q ∈ insert ℓ₂ (insert ℓ₁ L), eval (b2f x) q = 0) →
              ∀ i : Fin (u ++ [true]).length,
                (u ++ [true]).get i = true ↔ LinTermSat x (ask ((u ++ [true]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x (fun q hq => hx q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq))), ?_⟩
            simp only [true_iff, LinTermSat, heq, Finset.mem_insert, Finset.mem_singleton]
            rintro e (he | he)
            · rw [he]
              exact (eval_linEqPoly x e₁).mp (hx ℓ₁ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
            · rw [he]
              exact (eval_linEqPoly x e₂).mp (hx ℓ₂ (Finset.mem_insert_self _ _))
          have hfol_TF : ∀ x : V → Bool, (∀ q ∈ insert (ℓ₂ + 1) (insert ℓ₁ L), eval (b2f x) q = 0) →
              ∀ i : Fin (u ++ [false]).length,
                (u ++ [false]).get i = true ↔ LinTermSat x (ask ((u ++ [false]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x (fun q hq => hx q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq))), ?_⟩
            simp only [Bool.false_eq_true, false_iff, LinTermSat, heq]
            intro hsat
            have h2 := hsat e₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂))
            have h20 : eval (b2f x) ℓ₂ = 0 := (eval_linEqPoly x e₂).mpr h2
            have h21 : eval (b2f x) (ℓ₂ + 1) = 0 := hx (ℓ₂ + 1) (Finset.mem_insert_self _ _)
            rw [map_add, map_one, h20, zero_add] at h21
            exact absurd h21 (by decide)
          have hfol_F : ∀ x : V → Bool, (∀ q ∈ insert (ℓ₁ + 1) L, eval (b2f x) q = 0) →
              ∀ i : Fin (u ++ [false]).length,
                (u ++ [false]).get i = true ↔ LinTermSat x (ask ((u ++ [false]).take i.val)) := by
            intro x hx
            rw [follows_append_singleton]
            refine ⟨hfol x (fun q hq => hx q (Finset.mem_insert_of_mem hq)), ?_⟩
            simp only [Bool.false_eq_true, false_iff, LinTermSat, heq]
            intro hsat
            have h1 := hsat e₁ (Finset.mem_insert_self e₁ _)
            have h10 : eval (b2f x) ℓ₁ = 0 := (eval_linEqPoly x e₁).mpr h1
            have h11 : eval (b2f x) (ℓ₁ + 1) = 0 := hx (ℓ₁ + 1) (Finset.mem_insert_self _ _)
            rw [map_add, map_one, h10, zero_add] at h11
            exact absurd h11 (by decide)
          have hTT := ih (u ++ [true]) (insert ℓ₂ (insert ℓ₁ L)) (hm_child true) (hns_child true) hL12 hfol_TT
          have hTF := ih (u ++ [false]) (insert (ℓ₂ + 1) (insert ℓ₁ L)) (hm_child false) (hns_child false) hL12' hfol_TF
          have hF := ih (u ++ [false]) (insert (ℓ₁ + 1) L) (hm_child false) (hns_child false) hL1' hfol_F
          have hmid := combine_linear (cnfSystem F) b' k hb' hBool hFPC_deg
            (insert ℓ₁ L) hL1 ℓ₂ hℓ₂deg
            (subW leaves ask (u ++ [true])) (subW leaves ask (u ++ [false]))
            (subW leaves ask (u ++ [true]) + subW leaves ask (u ++ [false]))
            le_rfl hTT hTF
          have hWsplit := subW_split_eq2 leaves ask u huleaf hcard2
          exact (combine_linear (cnfSystem F) b' k hb' hBool hFPC_deg
            L hL ℓ₁ hℓ₁deg
            (subW leaves ask (u ++ [true]) + subW leaves ask (u ++ [false]))
            (subW leaves ask (u ++ [false]))
            (subW leaves ask u)
            (by omega) hmid hF).2 hWpos
private lemma nat_log2_mul_pow2 {a : ℕ} (ha : 1 ≤ a) :
    ∀ q : ℕ, Nat.log 2 (a * 2 ^ q) = Nat.log 2 a + q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hmul : a * 2 ^ (q + 1) = (a * 2 ^ q) * 2 := by rw [pow_succ, mul_assoc]
    rw [hmul, Nat.log_mul_base (by omega) (by positivity), ih]
    omega
private lemma lower_bound_of_expander {n b' s₀ C : ℕ}
    (hb' : 2 ≤ b') (hs₀ : 0 < s₀) (hn_s₀ : s₀ ≤ n)
    (hC : s₀ * b' * b' ≤ C)
    (G : BipGraph (n + 1) n)
    (hLeft : LeftDegLe G b')
    (hExp : IsBdryExpander G (n / s₀) 2) :
    let V := GEdge G
    let F := funGraphPHP G
    ∀ (leaves : Finset (List Bool)) (ask : List Bool → LinTerm V)
        (out : List Bool → Finset (Clause V)) (k q : ℕ),
      let follows := fun (p : List Bool) (x : V → Bool) =>
        ∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val))
      (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
      (∀ x : V → Bool, ∃ p ∈ leaves, follows p x) →
      (∀ p ∈ leaves, ∃ x : V → Bool, follows p x) →
      (∀ p ∈ leaves, ∀ i : Fin p.length, (ask (p.take i.val)).card ≤ 2) →
      (∀ p ∈ leaves, (Finset.univ.filter (fun i : Fin p.length =>
        p.get i = false ∧ (ask (p.take i.val)).card = 2)).card ≤ q) →
      (∀ p ∈ leaves, (out p).card ≤ k ∧ ∀ cl ∈ out p, cl ∈ F) →
      (∀ p ∈ leaves, ∀ x : V → Bool, follows p x → ∃ cl ∈ out p, ¬ ClauseSat x cl) →
      n ≤ C * (1 + k + q + Nat.log 2 leaves.card) := by
  intro V F leaves ask out k q follows hpref hcomp _ hask2 hrej hout_c hout_u
  have hF_deg : ∀ cl ∈ F, (clausePoly cl).totalDegree ≤ b' :=
    fun cl hcl => clausePoly_deg_of_funGraphPHP G b' hb' hLeft cl hcl
  have hroot := tree_pc_derivable F b' k hb' hF_deg leaves ask out hpref hcomp hask2 hout_c hout_u
    (leaves.sup List.length) [] ∅ (by simp) (fun p _ hp => List.prefix_nil.mp hp)
    (fun _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ i => Fin.elim0 i)
  obtain ⟨p₀, hp₀, _⟩ := hcomp (fun _ => false)
  have hLroot : Lset leaves [] = leaves := by
    ext p; simp [Lset]
  have hleaves_pos : 1 ≤ leaves.card := Finset.one_le_card.mpr ⟨p₀, hp₀⟩
  have hWpos : 1 ≤ subW leaves ask [] := by
    have hne : Lset leaves [] ≠ ∅ := by rw [hLroot]; exact Finset.ne_empty_of_mem hp₀
    have hnz : subW leaves ask [] ≠ 0 := mt (subW_eq_zero_iff leaves ask []).mp hne
    omega
  have hWle : subW leaves ask [] ≤ leaves.card * 2 ^ q := by
    unfold subW
    rw [hLroot]
    calc ∑ p ∈ leaves, rwgt ask [] p
        ≤ ∑ _p ∈ leaves, 2 ^ q := Finset.sum_le_sum fun p hp => by
          unfold rwgt
          refine Nat.pow_le_pow_right (by omega) ?_
          have hfeq : (Finset.univ.filter fun i : Fin p.length =>
              ([] : List Bool).length ≤ i.val ∧ p.get i = false ∧ (ask (p.take i.val)).card = 2) =
            Finset.univ.filter fun i : Fin p.length =>
              p.get i = false ∧ (ask (p.take i.val)).card = 2 := by
            ext i; simp
          rw [hfeq]
          exact hrej p hp
      _ = leaves.card * 2 ^ q := by simp
  have hlog_le : Nat.log 2 (subW leaves ask []) ≤ Nat.log 2 leaves.card + q := by
    calc Nat.log 2 (subW leaves ask [])
        ≤ Nat.log 2 (leaves.card * 2 ^ q) := Nat.log_mono_right hWle
      _ = Nat.log 2 leaves.card + q := nat_log2_mul_pow2 hleaves_pos q
  set D := b' * k + b' + q + Nat.log 2 leaves.card
  have href : PCRefutable (cnfSystem F) D := by
    have h1 := hroot.2 hWpos
    refine pcDerivable_mono h1 (by omega) ?_
    simp
  have hno := PCXLib.L049 (n + 1) n G (n / s₀) b' D hExp hLeft
    (Nat.div_pos hn_s₀ hs₀)
  have hgt : n / s₀ < b' * D := by
    by_contra hle
    exact hno (not_lt.mp hle) href
  have hD_le : D ≤ b' * (1 + k + q + Nat.log 2 leaves.card) := by
    have : 1 * (q + Nat.log 2 leaves.card) ≤ b' * (q + Nat.log 2 leaves.card) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp only [D]
    nlinarith
  have hn_lt : n < s₀ * (n / s₀ + 1) := by
    have hdm := Nat.div_add_mod n s₀
    have hmod := Nat.mod_lt n hs₀
    nlinarith
  have hn_le1 : n ≤ s₀ * (b' * D) := by
    have hstep : n / s₀ + 1 ≤ b' * D := hgt
    have hmul := Nat.mul_le_mul_left s₀ hstep
    omega
  calc n ≤ s₀ * (b' * D) := hn_le1
    _ ≤ s₀ * (b' * (b' * (1 + k + q + Nat.log 2 leaves.card))) :=
      Nat.mul_le_mul_left s₀ (Nat.mul_le_mul_left b' hD_le)
    _ = (s₀ * b' * b') * (1 + k + q + Nat.log 2 leaves.card) := by ring
    _ ≤ C * (1 + k + q + Nat.log 2 leaves.card) := Nat.mul_le_mul_right _ hC
private def collPairs {n : ℕ} (G : BipGraph (n + 1) n) : Finset (GEdge G × GEdge G) :=
  Finset.univ.filter fun uv : GEdge G × GEdge G =>
    (uv.1.1.1 = uv.2.1.1 ∧ uv.1.1.2 ≠ uv.2.1.2) ∨
    (uv.1.1.2 = uv.2.1.2 ∧ uv.1.1.1 ≠ uv.2.1.1)
private lemma collPairs_card_le {n b' : ℕ} (hn : 1 ≤ n)
    (G : BipGraph (n + 1) n) (hLeft : LeftDegLe G b') (hRight : RightDegLe G b') :
    (collPairs G).card ≤ 3 * b' * b' * n := by
  let incP : Fin (n + 1) → Finset (GEdge G) := fun p => Finset.univ.filter (fun e => e.1.1 = p)
  let incH : Fin n → Finset (GEdge G) := fun j => Finset.univ.filter (fun e => e.1.2 = j)
  let SP : Finset (GEdge G × GEdge G) := Finset.univ.biUnion fun p => incP p ×ˢ incP p
  let SH : Finset (GEdge G × GEdge G) := Finset.univ.biUnion fun j => incH j ×ˢ incH j
  have hsub : collPairs G ⊆ SP ∪ SH := by
    intro uv huv
    simp only [collPairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    rw [Finset.mem_union]
    rcases huv with ⟨hp, _⟩ | ⟨hh, _⟩
    · left
      rw [Finset.mem_biUnion]
      refine ⟨uv.1.1.1, Finset.mem_univ _, ?_⟩
      simp [incP, hp]
    · right
      rw [Finset.mem_biUnion]
      refine ⟨uv.1.1.2, Finset.mem_univ _, ?_⟩
      simp [incH, hh]
  have hSP : SP.card ≤ (n + 1) * (b' * b') := by
    calc SP.card ≤ ∑ p : Fin (n + 1), (incP p ×ˢ incP p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : Fin (n + 1), b' * b' := Finset.sum_le_sum fun p _ => by
        rw [Finset.card_product]
        have hp : (incP p).card ≤ b' := (incPig_card_le G p).trans (hLeft p)
        exact Nat.mul_le_mul hp hp
      _ = (n + 1) * (b' * b') := by simp
  have hSH : SH.card ≤ n * (b' * b') := by
    calc SH.card ≤ ∑ j : Fin n, (incH j ×ˢ incH j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin n, b' * b' := Finset.sum_le_sum fun j _ => by
        rw [Finset.card_product]
        have hj : (incH j).card ≤ b' := (incHole_card_le G j).trans (hRight j)
        exact Nat.mul_le_mul hj hj
      _ = n * (b' * b') := by simp
  have hun := (Finset.card_le_card hsub).trans (Finset.card_union_le SP SH)
  nlinarith
private lemma linEqSat_singleton_true {V : Type} (x : V → Bool) (v : V) :
    LinEqSat x (({v} : Finset V), true) ↔ x v = true := by
  unfold LinEqSat
  simp only [iff_true]
  cases hx : x v with
  | true =>
    have hf : (({v} : Finset V).filter (fun w => x w = true)) = {v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl; exact hx
    simp [hf]
  | false =>
    have hf : (({v} : Finset V).filter (fun w => x w = true)) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl; simp [hx]
    simp [hf]
private lemma upper_bound_of_deg {n b' C : ℕ} (hn : 1 ≤ n)
    (hC1 : b' ≤ C) (hC2 : 3 * b' * b' + 2 ≤ C)
    (G : BipGraph (n + 1) n) (hLeft : LeftDegLe G b') (hRight : RightDegLe G b') :
    let V := GEdge G
    let F := funGraphPHP G
    ∃ (m h : ℕ) (test : Fin m → LinTerm V) (name : Fin m → Clause V),
      h ≤ m ∧ m ≤ C * n ∧ (∀ i, name i ∈ F) ∧
      (∀ i : Fin m, i.val < h →
        ∃ u v : V, u ≠ v ∧ test i = {(({u} : Finset V), true), (({v} : Finset V), true)}) ∧
      (∀ i : Fin m, h ≤ i.val → ∃ S : Finset V, S.card ≤ C ∧ test i = {(S, false)}) ∧
      ∀ x : V → Bool, ∃ i : Fin m, LinTermSat x (test i) ∧
        (∀ j : Fin m, j < i → ¬ LinTermSat x (test j)) ∧
        ¬ ClauseSat x (name i) := by
  classical
  intro V F
  set h := (collPairs G).card with hhdef
  set m := h + (n + 1) with hmdef
  let eColl : Fin h ≃ collPairs G := (collPairs G).equivFin.symm
  let incP : Fin (n + 1) → Finset V := fun p => Finset.univ.filter (fun e => e.1.1 = p)
  let test : Fin m → LinTerm V := fun i =>
    if hi : i.val < h then
      let uv := (eColl ⟨i.val, hi⟩).1
      {(({uv.1} : Finset V), true), (({uv.2} : Finset V), true)}
    else
      {(incP ⟨i.val - h, by omega⟩, false)}
  let name : Fin m → Clause V := fun i =>
    if hi : i.val < h then
      let uv := (eColl ⟨i.val, hi⟩).1
      {(uv.1, false), (uv.2, false)}
    else
      Finset.univ.filter (fun l : Literal V => l.1.1.1 = ⟨i.val - h, by omega⟩ ∧ l.2 = true)
  refine ⟨m, h, test, name, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · have hh_le : h ≤ 3 * b' * b' * n := collPairs_card_le hn G hLeft hRight
    nlinarith
  · intro i
    dsimp only [name]
    split_ifs with hi
    · have huv := (eColl ⟨i.val, hi⟩).2
      simp only [collPairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      rcases huv with ⟨hp, hne⟩ | ⟨hh, hne⟩
      · exact Or.inr ⟨_, _, hp, hne, rfl⟩
      · exact Or.inl (Or.inr ⟨_, _, hh, hne, rfl⟩)
    · exact Or.inl (Or.inl ⟨⟨i.val - h, by omega⟩, rfl⟩)
  · intro i hi
    dsimp only [test]
    simp only [hi, ↓reduceDIte]
    set uv := (eColl ⟨i.val, hi⟩).1
    have huv := (eColl ⟨i.val, hi⟩).2
    simp only [collPairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    refine ⟨uv.1, uv.2, ?_, rfl⟩
    intro heq
    have heq' : (eColl ⟨i.val, hi⟩).1.1 = (eColl ⟨i.val, hi⟩).1.2 := heq
    rcases huv with ⟨_, hne⟩ | ⟨_, hne⟩
    · exact hne (congrArg (fun e => e.1.2) heq')
    · exact hne (congrArg (fun e => e.1.1) heq')
  · intro i hi
    dsimp only [test]
    simp only [not_lt.mpr hi, ↓reduceDIte]
    refine ⟨incP ⟨i.val - h, by omega⟩, ?_, rfl⟩
    exact ((incPig_card_le G _).trans (hLeft _)).trans hC1
  · intro x
    have htest_lt : ∀ (i : Fin m) (hi : i.val < h),
        LinTermSat x (test i) ↔ x (eColl ⟨i.val, hi⟩).1.1 = true ∧ x (eColl ⟨i.val, hi⟩).1.2 = true := by
      intro i hi
      dsimp only [test]
      simp only [hi, ↓reduceDIte]
      unfold LinTermSat
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
        linEqSat_singleton_true]
    have htest_ge : ∀ (i : Fin m) (hi : ¬ i.val < h),
        LinTermSat x (test i) ↔
          ¬ Odd ((incP ⟨i.val - h, by omega⟩).filter (fun e => x e = true)).card := by
      intro i hi
      dsimp only [test]
      simp only [hi, ↓reduceDIte]
      unfold LinTermSat LinEqSat
      simp
    have hex_sat : ∃ i : Fin m, LinTermSat x (test i) := by
      by_cases hcoll : ∃ uv : collPairs G, x uv.1.1 = true ∧ x uv.1.2 = true
      · obtain ⟨uv, h1, h2⟩ := hcoll
        set k := eColl.symm uv
        refine ⟨⟨k.val, by omega⟩, ?_⟩
        rw [htest_lt _ k.isLt]
        have heq : eColl ⟨k.val, k.isLt⟩ = uv := by
          change eColl (eColl.symm uv) = uv
          exact eColl.apply_symm_apply uv
        rw [heq]
        exact ⟨h1, h2⟩
      · push Not at hcoll
        have hex_empty : ∃ p : Fin (n + 1), ∀ e ∈ incP p, x e ≠ true := by
          by_contra hall
          push Not at hall
          choose f hf_mem hf_true using hall
          have hfp : ∀ p : Fin (n + 1), (f p).1.1 = p := fun p =>
            (Finset.mem_filter.mp (hf_mem p)).2
          have hinj : Function.Injective (fun p : Fin (n + 1) => (f p).1.2) := by
            intro p₁ p₂ heq
            by_contra hne
            have hmem : (f p₁, f p₂) ∈ collPairs G := by
              simp only [collPairs, Finset.mem_filter, Finset.mem_univ, true_and]
              right; exact ⟨heq, by rw [hfp p₁, hfp p₂]; exact hne⟩
            exact hcoll ⟨(f p₁, f p₂), hmem⟩ (hf_true p₁) (hf_true p₂)
          have hcard := Fintype.card_le_of_injective _ hinj
          simp at hcard
        obtain ⟨p, hp⟩ := hex_empty
        refine ⟨⟨h + p.val, by omega⟩, ?_⟩
        rw [htest_ge ⟨h + p.val, by omega⟩ (by dsimp; omega)]
        have hidx : (⟨(⟨h + p.val, by omega⟩ : Fin m).val - h, by dsimp; omega⟩ : Fin (n + 1)) = p :=
          Fin.ext (by dsimp; omega)
        rw [hidx]
        have hf0 : (incP p).filter (fun e => x e = true) = ∅ := by
          ext e
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          exact hp e
        rw [hf0, Finset.card_empty]
        rintro ⟨k, hk⟩; omega
    set S := Finset.univ.filter (fun i : Fin m => LinTermSat x (test i))
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hex_sat
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    set i := S.min' hSne
    have hi_mem : i ∈ S := Finset.min'_mem S hSne
    have hi_sat : LinTermSat x (test i) := (Finset.mem_filter.mp hi_mem).2
    have hi_min : ∀ j : Fin m, j < i → ¬ LinTermSat x (test j) := by
      intro j hj hjsat
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjsat⟩
      exact not_lt.mpr (Finset.min'_le S j hjS) hj
    refine ⟨i, hi_sat, hi_min, ?_⟩
    dsimp only [name]
    split_ifs with hi
    · rw [htest_lt i hi] at hi_sat
      rintro ⟨l, hl, hxl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · rw [hi_sat.1] at hxl; exact Bool.noConfusion hxl
      · rw [hi_sat.2] at hxl; exact Bool.noConfusion hxl
    · rw [htest_ge i hi] at hi_sat
      set p : Fin (n + 1) := ⟨i.val - h, by omega⟩
      rintro ⟨l, hl, hxl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      have he1_mem : l.1 ∈ incP p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl.1⟩
      have he1_true : x l.1 = true := hxl.trans hl.2
      have hf_eq : (incP p).filter (fun e => x e = true) = {l.1} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨he_inc, he_true⟩
          by_contra hne
          have he_p : e.1.1 = p := (Finset.mem_filter.mp he_inc).2
          have hne_hole : e.1.2 ≠ l.1.1.2 := by
            intro hhole
            apply hne
            apply Subtype.ext
            exact Prod.ext (he_p.trans hl.1.symm) hhole
          have hcmem : (e, l.1) ∈ collPairs G := by
            simp only [collPairs, Finset.mem_filter, Finset.mem_univ, true_and]
            left; exact ⟨he_p.trans hl.1.symm, hne_hole⟩
          set k := eColl.symm ⟨(e, l.1), hcmem⟩
          set j : Fin m := ⟨k.val, by omega⟩
          have hjlt : j < i := by
            change k.val < i.val
            omega
          have hjsat : LinTermSat x (test j) := by
            rw [htest_lt j k.isLt]
            have heq : eColl ⟨k.val, k.isLt⟩ = ⟨(e, l.1), hcmem⟩ := by
              change eColl (eColl.symm _) = _
              exact eColl.apply_symm_apply _
            rw [heq]
            exact ⟨he_true, he1_true⟩
          exact hi_min j hjlt hjsat
        · rintro rfl
          exact ⟨he1_mem, he1_true⟩
      rw [hf_eq, Finset.card_singleton] at hi_sat
      exact hi_sat ⟨0, rfl⟩
private lemma main_proof : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.Expanders.funGraphPHP G
    (∀ (leaves : Finset (List Bool)) (ask : List Bool → PEqualNP.ProofComplexity.LinTerm V)
        (out : List Bool → Finset (PEqualNP.ProofComplexity.Clause V)) (k q : ℕ),
      let follows := fun (p : List Bool) (x : V → Bool) =>
        ∀ i : Fin p.length, p.get i = true ↔
          PEqualNP.ProofComplexity.LinTermSat x (ask (p.take i.val))
      (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
      (∀ x : V → Bool, ∃ p ∈ leaves, follows p x) →
      (∀ p ∈ leaves, ∃ x : V → Bool, follows p x) →
      (∀ p ∈ leaves, ∀ i : Fin p.length, (ask (p.take i.val)).card ≤ 2) →
      (∀ p ∈ leaves, (Finset.univ.filter (fun i : Fin p.length =>
        p.get i = false ∧ (ask (p.take i.val)).card = 2)).card ≤ q) →
      (∀ p ∈ leaves, (out p).card ≤ k ∧ ∀ cl ∈ out p, cl ∈ F) →
      (∀ p ∈ leaves, ∀ x : V → Bool, follows p x →
        ∃ cl ∈ out p, ¬ PEqualNP.ProofComplexity.ClauseSat x cl) →
      n ≤ C * (1 + k + q + Nat.log 2 leaves.card)) ∧
    ∃ (m h : ℕ) (test : Fin m → PEqualNP.ProofComplexity.LinTerm V)
        (name : Fin m → PEqualNP.ProofComplexity.Clause V),
      h ≤ m ∧ m ≤ C*n ∧ (∀ i, name i ∈ F) ∧
      (∀ i : Fin m, i.val < h →
        ∃ u v : V, u ≠ v ∧ test i = {(({u} : Finset V),true), (({v} : Finset V),true)}) ∧
      (∀ i : Fin m, h ≤ i.val → ∃ S : Finset V, S.card ≤ C ∧ test i = {(S,false)}) ∧
      ∀ x : V → Bool, ∃ i : Fin m, PEqualNP.ProofComplexity.LinTermSat x (test i) ∧
        (∀ j : Fin m, j < i → ¬ PEqualNP.ProofComplexity.LinTermSat x (test j)) ∧
        ¬ PEqualNP.ProofComplexity.ClauseSat x (name i)) := by
  obtain ⟨b, s₀, n₀, hs₀, hL043⟩ := PCXLib.L043
  set b' := max b 2
  set C := max (3 * b' * b' + 2) (s₀ * b' * b')
  set n₀' := max n₀ (max s₀ 1)
  have hb'2 : 2 ≤ b' := le_max_right b 2
  have hb_le : b ≤ b' := le_max_left b 2
  have hC_ge2 : 2 ≤ C := by
    have : 2 ≤ 3 * b' * b' + 2 := by omega
    exact this.trans (le_max_left _ _)
  have hC_b' : b' ≤ C := by
    have : b' ≤ 3 * b' * b' + 2 := by nlinarith
    exact this.trans (le_max_left _ _)
  refine ⟨C, n₀', hC_ge2, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hs0n : s₀ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn1 : 1 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨G, hLeft, hRight, hExp⟩ := hL043 n hn0
  have hLeft' : LeftDegLe G b' := fun i => (hLeft i).trans hb_le
  have hRight' : RightDegLe G b' := fun j => (hRight j).trans hb_le
  refine ⟨G, fun i => (hLeft' i).trans hC_b', fun j => (hRight' j).trans hC_b', ?_, ?_⟩
  · exact lower_bound_of_expander hb'2 hs₀ hs0n (le_max_right _ _) G hLeft' hExp
  · exact upper_bound_of_deg hn1 hC_b' (le_max_left _ _) G hLeft' hRight'
end ProofBody
end PEqualNP.Outside.L_pcx_395
theorem PEqualNP.Outside.L_pcx_395 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.Expanders.funGraphPHP G
    (∀ (leaves : Finset (List Bool)) (ask : List Bool → PEqualNP.ProofComplexity.LinTerm V)
        (out : List Bool → Finset (PEqualNP.ProofComplexity.Clause V)) (k q : ℕ),
      let follows := fun (p : List Bool) (x : V → Bool) =>
        ∀ i : Fin p.length, p.get i = true ↔
          PEqualNP.ProofComplexity.LinTermSat x (ask (p.take i.val))
      (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
      (∀ x : V → Bool, ∃ p ∈ leaves, follows p x) →
      (∀ p ∈ leaves, ∃ x : V → Bool, follows p x) →
      (∀ p ∈ leaves, ∀ i : Fin p.length, (ask (p.take i.val)).card ≤ 2) →
      (∀ p ∈ leaves, (Finset.univ.filter (fun i : Fin p.length =>
        p.get i = false ∧ (ask (p.take i.val)).card = 2)).card ≤ q) →
      (∀ p ∈ leaves, (out p).card ≤ k ∧ ∀ cl ∈ out p, cl ∈ F) →
      (∀ p ∈ leaves, ∀ x : V → Bool, follows p x →
        ∃ cl ∈ out p, ¬ PEqualNP.ProofComplexity.ClauseSat x cl) →
      n ≤ C * (1 + k + q + Nat.log 2 leaves.card)) ∧
    ∃ (m h : ℕ) (test : Fin m → PEqualNP.ProofComplexity.LinTerm V)
        (name : Fin m → PEqualNP.ProofComplexity.Clause V),
      h ≤ m ∧ m ≤ C*n ∧ (∀ i, name i ∈ F) ∧
      (∀ i : Fin m, i.val < h →
        ∃ u v : V, u ≠ v ∧ test i = {(({u} : Finset V),true), (({v} : Finset V),true)}) ∧
      (∀ i : Fin m, h ≤ i.val → ∃ S : Finset V, S.card ≤ C ∧ test i = {(S,false)}) ∧
      ∀ x : V → Bool, ∃ i : Fin m, PEqualNP.ProofComplexity.LinTermSat x (test i) ∧
        (∀ j : Fin m, j < i → ¬ PEqualNP.ProofComplexity.LinTermSat x (test j)) ∧
        ¬ PEqualNP.ProofComplexity.ClauseSat x (name i)) :=
  PEqualNP.Outside.L_pcx_395.main_proof

