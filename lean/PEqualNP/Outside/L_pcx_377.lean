import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_pcx_377.H.Helpers
open PEqualNP.ProofComplexity
section Sec_ExpanderGraph
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
end Sec_ExpanderGraph

section Sec_ExpanderDet
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
end Sec_ExpanderDet

section Sec_ExpanderPerm
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
end Sec_ExpanderPerm

section Sec_ExpanderArith
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
end Sec_ExpanderArith

section Sec_ExpanderAssembly
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
end Sec_ExpanderAssembly

section Sec_PCToolkit
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
end Sec_PCToolkit

section Sec_BoolVanish
namespace BoolVanish

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H

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

end BoolVanish
end Sec_BoolVanish

section Sec_PseudoReduction
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
end Sec_PseudoReduction

section Sec_EchelonNF
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
end Sec_EchelonNF

section Sec_ExpanderSupp
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
end Sec_ExpanderSupp

section Sec_LocalSat
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
end Sec_LocalSat

section Sec_LocalNF
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
end Sec_LocalNF

section Sec_MomentReduction
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
end Sec_MomentReduction

section Sec_GraphPHPReduction
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
end Sec_GraphPHPReduction

section Sec_FunLocalSat
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
end Sec_FunLocalSat

section Sec_FunLocalNF
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
end Sec_FunLocalNF

section Sec_FunGraphPHPReduction
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
end Sec_FunGraphPHPReduction
end PEqualNP.Outside.L_pcx_377.H.Helpers

namespace PEqualNP.Outside.L_pcx_377.H
theorem L043 : ∃ b s₀ n₀ : ℕ, 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
      PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
      PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ),
    PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s →
    ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB
end PEqualNP.Outside.L_pcx_377.H

namespace PEqualNP.Outside.L_pcx_377.H.Helpers
open MvPolynomial PEqualNP.ProofComplexity
theorem two_eq_zero_mvPolynomial {σ : Type} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  have h1 : (1 : MvPolynomial σ (ZMod 2)) + 1 = 0 := by
    rw [← map_one C, ← map_add, show (1 : ZMod 2) + 1 = 0 from rfl, map_zero]
  exact (one_add_one_eq_two (R := MvPolynomial σ (ZMod 2))).symm.trans h1
theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide
theorem char2_add_self {σ : Type} (x : MvPolynomial σ (ZMod 2)) : x + x = 0 := by
  rw [← two_mul, two_eq_zero_mvPolynomial, zero_mul]
noncomputable def eqPoly {V : Type} (q : LinEq V) : MvPolynomial V (ZMod 2) :=
  ∑ v ∈ q.1, X v + C (if q.2 = true then 0 else 1)
theorem totalDegree_eqPoly_le {V : Type} (q : LinEq V) : (eqPoly q).totalDegree ≤ 1 := by
  unfold eqPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_finsetSum_le fun v _ => (totalDegree_X v).le
  · rw [totalDegree_C]; exact Nat.zero_le _
theorem clausePoly_eq_prod {V : Type} (A : Clause V) :
    clausePoly A = ∏ l ∈ A, (1 + eqPoly ((({l.1} : Finset V), l.2) : LinEq V)) := by
  unfold clausePoly
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases l with ⟨v, b⟩
  cases b
  · simp only [eqPoly, Finset.sum_singleton, Bool.false_eq_true, ite_false, C_1]
    linear_combination (-(1 : MvPolynomial V (ZMod 2))) * two_eq_zero_mvPolynomial (σ := V)
  · simp [eqPoly]
theorem totalDegree_mul_le' {σ : Type} {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
theorem totalDegree_prod_one_add_le {σ ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) {e : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ e) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ e * s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ u ∈ s, (1 + a u).totalDegree ≤ ∑ _u ∈ s, e := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine (totalDegree_add _ _).trans ?_
        rw [totalDegree_one]
        exact max_le (Nat.zero_le _) (ha u hu)
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem linEqSat_singleton {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  unfold LinEqSat
  rw [Finset.filter_singleton]
  cases h : a v <;> cases s <;> simp
end PEqualNP.Outside.L_pcx_377.H.Helpers

namespace PEqualNP.Outside.L_pcx_377.H.Helpers
open MvPolynomial PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]
def eqVec (q : LinEq V) : (V → ZMod 2) × ZMod 2 :=
  (fun v => if v ∈ q.1 then 1 else 0, if q.2 = true then 0 else 1)
noncomputable def affPoly : ((V → ZMod 2) × ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) :=
  (Fintype.linearCombination (ZMod 2) (fun v : V => (X v : MvPolynomial V (ZMod 2)))).coprod
    (Algebra.linearMap (ZMod 2) (MvPolynomial V (ZMod 2)))
theorem affPoly_eqVec (q : LinEq V) : affPoly (eqVec q) = eqPoly q := by
  simp [affPoly, eqVec, eqPoly, Fintype.linearCombination_apply, MvPolynomial.algebraMap_eq,
    Finset.sum_ite_mem]
omit [DecidableEq V] in
theorem affPoly_one : affPoly ((0, 1) : (V → ZMod 2) × ZMod 2) = 1 := by
  simp [affPoly, Fintype.linearCombination_apply]
omit [Fintype V] [DecidableEq V] in
theorem linEqSat_iff_sum (a : V → ZMod 2) (q : LinEq V) :
    LinEqSat (fun v => decide (a v = 1)) q ↔
      ∑ v ∈ q.1, a v + (if q.2 = true then 0 else 1) = 1 := by
  unfold LinEqSat
  have hs : ∑ v ∈ q.1, a v
      = ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    generalize a v = x
    revert x
    decide
  rw [hs, ← ZMod.natCast_eq_one_iff_odd]
  generalize ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) = x
  rcases q with ⟨f, b⟩
  cases b
  · simp only [Bool.false_eq_true, iff_false, ite_false]
    revert x
    decide
  · simp
theorem dual_apply (φ : Module.Dual (ZMod 2) ((V → ZMod 2) × ZMod 2))
    (h1 : φ (0, 1) = 1) (q : LinEq V) :
    φ (eqVec q) = ∑ v ∈ q.1, φ (fun j => if v = j then 1 else 0, 0) + (if q.2 = true then 0 else 1) := by
  have hsplit : eqVec q = LinearMap.inl (ZMod 2) (V → ZMod 2) (ZMod 2)
      (fun v => if v ∈ q.1 then 1 else 0)
      + (if q.2 = true then (0 : ZMod 2) else 1) • ((0, 1) : (V → ZMod 2) × ZMod 2) := by
    rcases q with ⟨f, b⟩
    cases b <;> simp [eqVec]
  rw [hsplit, map_add, map_smul, h1, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [Finset.sum_ite_mem]
theorem lin_alt (q : LinEq V) (D : LinClause V)
    (himp : ∀ a : V → Bool, LinEqSat a q → LinClauseSat a D) :
    ∃ J : Finset (LinEq V), J ⊆ D ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q) := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hq : LinEqSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) q := by
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Set.mem_insert _ _))
      rw [map_add, h1] at this
      generalize φ (eqVec q) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hq
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨d, hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨c, z, hz, hEq⟩ := hmem
  rw [Finsupp.mem_span_image_iff_linearCombination] at hz
  obtain ⟨lc, hlc, rfl⟩ := hz
  have hJ : lc.support ⊆ D := by
    intro d hd
    exact Finsupp.mem_supported _ _ |>.mp hlc hd
  have hsum : affPoly (Finsupp.linearCombination (ZMod 2) eqVec lc)
      = ∑ d ∈ lc.support, eqPoly d := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
    have h1 : lc d = 1 := by
      generalize lc d = x at h0
      revert x
      decide
    rw [h1, one_smul, affPoly_eqVec]
  have hP := congrArg affPoly hEq
  rw [map_add, map_smul, map_add, affPoly_one, affPoly_eqVec, hsum] at hP
  refine ⟨lc.support, hJ, ?_⟩
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc c with rfl | rfl
  · left
    rw [zero_smul, zero_add] at hP
    exact hP.symm
  · right
    rw [one_smul] at hP
    linear_combination hP + char2_add_self (∑ d ∈ lc.support, eqPoly d)
end PEqualNP.Outside.L_pcx_377.H.Helpers

namespace PEqualNP.Outside.L_pcx_377.H.PhpFinal
open PEqualNP.ProofComplexity PEqualNP.Expanders
def Stmt046 : Prop := ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → 2 * (D + 1) ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.graphPHP G)) D
def Stmt047 : Prop := ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin N))), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP m N) π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.Expanders.graphPHP G) π' ∧ π'.length ≤ 2 * π.length
theorem card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ m * b := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter (fun e : Fin m × Fin N => e.2 ∈ G e.1)).filter
        (fun e => e.1 = i)).card ≤ b := by
    intro i _
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hb i)
    · intro e he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have h1 := (Finset.mem_filter.mp he'.1).2
      rw [he'.2] at h1
      exact Finset.mem_coe.mpr h1
    · intro e he e' he' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
      exact Prod.ext (h1.trans h2.symm) h
  calc _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum hfib
    _ = m * b := by simp
theorem graphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ graphPHP G, C.card ≤ max b 2 := by
  classical
  intro C hC
  rcases hC with ⟨i, rfl⟩ | ⟨e, e', -, -, rfl⟩
  · refine le_trans (le_trans
      (Finset.card_le_card_of_injOn (fun l : Literal (GEdge G) => l.1.1.2) ?_ ?_) (hb i))
      (le_max_left _ _)
    · intro l hl
      have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h1 : l.1.1.2 ∈ G l.1.1.1 := l.1.2
      rw [hl'.1] at h1
      exact Finset.mem_coe.mpr h1
    · intro l hl l' hl' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
      exact Prod.ext (Subtype.ext (Prod.ext (h1.1.trans h2.1.symm) h)) (h1.2.trans h2.2.symm)
  · exact le_trans Finset.card_le_two (le_max_right _ _)
end PEqualNP.Outside.L_pcx_377.H.PhpFinal

namespace PEqualNP.Outside.L_pcx_377.H.DegSizePlan
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
section Abstract
variable {σ : Type}
def pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) where
  carrier := {p | PCDerivable A D p}; add_mem' := fun hp hq => PCDerivable.add hp hq
  zero_mem' := PCDerivable.zero
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa using (PCDerivable.zero : PCDerivable A D 0)
    · simpa using hp
theorem mem_pcClosure {A : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    {p : MvPolynomial σ (ZMod 2)} : p ∈ pcClosure A D ↔ PCDerivable A D p := Iff.rfl
structure DegClosed (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ) : Prop where
  two_le : 2 ≤ D
  mulX : ∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ C → f.totalDegree + 1 ≤ D → X v * f ∈ C
  bool : ∀ v : σ, X v * X v + X v ∈ C
theorem degClosed_pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) (hD : 2 ≤ D)
    (hA : ∀ v : σ, X v * X v + X v ∈ A) : DegClosed (pcClosure A D) D where
  two_le := hD
  mulX := fun v f hf hdeg => PCDerivable.mulX v hf
    ((totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega))
  bool := fun v => PCDerivable.ax (hA v) (by
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · rw [totalDegree_X]; omega
    · rw [totalDegree_X]; omega)
noncomputable abbrev polyLE (σ : Type) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictTotalDegree σ (ZMod 2) k
noncomputable def errKer (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  polyLE σ k ⊓ ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_errKer {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C M k ↔ f.totalDegree ≤ k ∧ ∀ m ∈ M, m * f ∈ C := by
  simp [errKer, polyLE, mem_restrictTotalDegree]
noncomputable def errRank (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) (errKer C M k)
noncomputable def zMul (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))) :
    Set (MvPolynomial σ (ZMod 2)) := (fun g => P * g) '' G
def numMono (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j
noncomputable def hCodim (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ K) - finrank (ZMod 2) ↥(C ⊓ polyLE σ K)
noncomputable def eta (n K : ℕ) : ℝ := (numMono n (K - 1) : ℝ) / (2 * numMono n K)
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ), DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ), DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (Z : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ),
    (∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ Z → f.totalDegree + 1 ≤ K → X v * f ∈ Z) →
    (∀ (v : σ) (u : σ →₀ ℕ), (u.sum fun _ e => e) + 2 ≤ K →
      (X v * X v + X v) * monomial u (1 : ZMod 2) ∈ Z) →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      (finrank (ZMod 2) (polyLE σ k') - finrank (ZMod 2) ↥(Z ⊓ polyLE σ k')) *
          numMono (Fintype.card σ) k
        ≤ (finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) ↥(Z ⊓ polyLE σ k)) *
          numMono (Fintype.card σ) k'
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'
example : Prop :=
  ∀ (ι r n : Type) [Fintype ι] [Fintype r] [Fintype n] [DecidableEq n]
    (E : Type) [Field E] [Algebra (ZMod 2) E] (lam : ι → E)
    (M : ι → Matrix r n (ZMod 2)),
    LinearIndependent (ZMod 2) lam →
    (∀ u : n → E, (∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)).mulVec u = 0 →
      (∑ i, lam i ^ 2 • (M i).map (algebraMap (ZMod 2) E)).mulVec u = 0) →
    ∃ c : ι → ZMod 2,
      (Matrix.of fun (p : ι × r) (j : n) => M p.1 p.2 j).rank ≤ 2 * (∑ i, c i • M i).rank
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
    a + K + 2 ≤ D →
    ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
      2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
        ≤ 2 * errRank C (zMul P ↑G) K
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
    (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
    ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
      (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
      (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
        ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
    (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
    (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
    (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
    ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
      f.totalDegree ≤ K ∧ f ∉ C ∧
      (∀ ν ∈ S, ∀ j, qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
      ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C
end Abstract
end PEqualNP.Outside.L_pcx_377.H.DegSizePlan

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem monomial_mul_mem (hC : DegClosed C D) (a : σ →₀ ℕ) :
    ∀ {g : MvPolynomial σ (ZMod 2)}, g ∈ C → (a.sum fun _ e => e) + g.totalDegree ≤ D →
      monomial a 1 * g ∈ C := by
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
      exact hC.mulX j _ (ih hg (by omega)) (by omega)
theorem absorb_le (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ C) {a b : ℕ} (hg : g.totalDegree ≤ a)
    (hfd : f.totalDegree ≤ b) (hB : a + b ≤ D) : g * f ∈ C := by
  have hq : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hc : g.coeff u = 1 := by
    have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
    generalize g.coeff u = c at h0
    revert h0; revert c; decide
  rw [hc]
  have : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact monomial_mul_mem hC u hf (by omega)
theorem absorb : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C :=
  fun _ _ _ hC _ g hf hdeg => absorb_le hC g hf le_rfl le_rfl hdeg
theorem idem_sum {ι : Type} (s : Finset ι) (h : ι → MvPolynomial σ (ZMod 2))
    (hh : ∀ i ∈ s, h i * h i + h i ∈ C) :
    (∑ i ∈ s, h i) * (∑ i ∈ s, h i) + ∑ i ∈ s, h i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have e : (h i + ∑ x ∈ s, h x) * (h i + ∑ x ∈ s, h x) + (h i + ∑ x ∈ s, h x)
        = (h i * h i + h i) + ((∑ x ∈ s, h x) * (∑ x ∈ s, h x) + ∑ x ∈ s, h x) := by
      linear_combination char2_add_self (h i * ∑ x ∈ s, h x)
    rw [e]
    exact C.add_mem (hh i (Finset.mem_insert_self i s))
      (ih fun k hk => hh k (Finset.mem_insert_of_mem hk))
theorem exponent_le_one (u : σ →₀ ℕ) (hu : (u.sum fun _ e => e) ≤ 1) :
    u = 0 ∨ ∃ v, u = Finsupp.single v 1 := by
  classical
  by_cases h0 : u = 0
  · exact Or.inl h0
  right
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨v, ?_⟩
  have hsum : u v + ∑ x ∈ u.support.erase v, u x ≤ 1 := by
    rw [Finset.add_sum_erase _ _ hv]
    exact hu
  have hv1 : u v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hrest : ∑ x ∈ u.support.erase v, u x = 0 := by omega
  ext x
  by_cases hx : x = v
  · subst hx
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hx]
    by_contra hne
    have hmem : x ∈ u.support.erase v :=
      Finset.mem_erase.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩
    exact hne ((Finset.sum_eq_zero_iff.mp hrest) x hmem)
theorem affine_idem' (hC : DegClosed C D) {g : MvPolynomial σ (ZMod 2)}
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  have hsum : g = ∑ u ∈ g.support, monomial u (g.coeff u) := g.as_sum
  have key := idem_sum (C := C) g.support (fun u => monomial u (g.coeff u)) (fun u hu => by
    have hc : g.coeff u = 1 := by
      have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
      generalize g.coeff u = c at h0
      revert h0; revert c; decide
    rw [hc]
    have hdu : (u.sum fun _ e => e) ≤ 1 := (le_totalDegree hu).trans hg
    rcases exponent_le_one u hdu with rfl | ⟨v, rfl⟩
    · have h1 : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [h1, one_mul, char2_add_self]
      exact C.zero_mem
    · exact hC.bool v)
  rw [← hsum] at key
  exact key
theorem affine_idem : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C :=
  fun _ _ _ hC _ hg => affine_idem' hC hg
theorem totalDegree_one_add_le {p : MvPolynomial σ (ZMod 2)} (h : p.totalDegree ≤ 1) :
    (1 + p).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (ha : ∀ u ∈ s, (a u).totalDegree ≤ 1) : (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := 1) ha
  omega
theorem prod_absorb (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ 1) (hB : s.card + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ 1 := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ 1 :=
      totalDegree_one_add_le (hdeg u (Finset.mem_insert_self u s))
    have h2 := absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  have := totalDegree_prod_le Finset.univ qs (fun j _ => h j)
  simpa using this
theorem transfer' (hC : DegClosed C D) {K t r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem g hg' =>
      rw [← mul_assoc]
      exact hg g hg'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact C.add_mem hx hy
    | smul c x _ hx =>
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using hx
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j => totalDegree_span_le hG (hqs j)
  have h1 := prod_absorb hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h2 := absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg => transfer' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} [Fintype V] [DecidableEq V]
  {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t : ℕ}
  {f : MvPolynomial V (ZMod 2)}
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_eqImage_le (L : LinClause V) :
    ∀ g ∈ (fun q => eqPoly q) '' (↑L : Set (LinEq V)), g.totalDegree ≤ 1 := by
  rintro _ ⟨q, _, rfl⟩
  exact totalDegree_eqPoly_le q
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_clausePoly_le (A : Clause V) : (clausePoly A).totalDegree ≤ A.card := by
  rw [clausePoly_eq_prod]
  exact totalDegree_prod_le A _ fun l _ => totalDegree_eqPoly_le _
omit [Fintype V] in
theorem step_ax (hC : DegClosed C D) (A : Clause V) {w : ℕ} (hA : clausePoly A ∈ C)
    (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2)
      ((fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ q ∈ linOfClause A, (∏ j, (1 + qs j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j =>
    totalDegree_span_le (totalDegree_eqImage_le _) (hqs j)
  have hQ : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h1 := prod_absorb hC A
    (fun l : Literal V => eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
    ((∏ j, (1 + qs j)) * f) hQ
    (fun l hl => by
      have := hH _ (Finset.mem_image.2 ⟨l, hl, rfl⟩)
      have e : eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * ((∏ j, (1 + qs j)) * f)
          = (∏ j, (1 + qs j)) * eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * f := by ring
      rw [e]
      exact this)
    (fun l _ => totalDegree_eqPoly_le _) (by omega)
  rw [← clausePoly_eq_prod] at h1
  have h2 := absorb_le hC ((∏ j, (1 + qs j)) * f) hA hQ (totalDegree_clausePoly_le A)
    (by omega)
  have h3 := C.add_mem h1 h2
  have e : clausePoly A * ((∏ j, (1 + qs j)) * f) + (∏ j, (1 + qs j)) * f
      + (∏ j, (1 + qs j)) * f * clausePoly A = (∏ j, (1 + qs j)) * f := by
    linear_combination char2_add_self (clausePoly A * ((∏ j, (1 + qs j)) * f))
  rwa [e] at h3
end Lines
end PEqualNP.Outside.L_pcx_377.H.DegSizeSim

namespace PEqualNP.Outside.L_pcx_377.H.Helpers
namespace MonoRank
open Finset MvPolynomial
open scoped FinsetFamily MonomialOrder
section Combinatorial
variable {σ : Type*} [DecidableEq σ] [Fintype σ]
theorem slice_succ_mul_le (𝒜 : Finset (Finset σ)) (h : IsLowerSet (𝒜 : Set (Finset σ)))
    (j : ℕ) :
    (j + 1) * #(𝒜 # (j + 1)) ≤ (Fintype.card σ - j) * #(𝒜 # j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (j + 1) with hj | hj
  · have h0 : 𝒜 # (j + 1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    simp [h0]
  · have h1 := Finset.local_lubell_yamamoto_meshalkin_inequality_mul
      (Finset.sized_slice (𝒜 := 𝒜) (r := j + 1))
    have hsub : ∂ (𝒜 # (j + 1)) ⊆ 𝒜 # j := by
      intro t ht
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.1 ht
      rw [Finset.mem_slice] at hs ⊢
      refine ⟨h (Finset.erase_subset a s) (Finset.mem_coe.2 hs.1), ?_⟩
      rw [Finset.card_erase_of_mem ha, hs.2]
      rfl
    have h2 := Finset.card_le_card hsub
    have h3 : Fintype.card σ - (j + 1) + 1 = Fintype.card σ - j := by omega
    rw [h3] at h1
    calc (j + 1) * #(𝒜 # (j + 1)) = #(𝒜 # (j + 1)) * (j + 1) := Nat.mul_comm _ _
      _ ≤ #(∂ (𝒜 # (j + 1))) * (Fintype.card σ - j) := h1
      _ ≤ #(𝒜 # j) * (Fintype.card σ - j) := Nat.mul_le_mul_right _ h2
      _ = (Fintype.card σ - j) * #(𝒜 # j) := Nat.mul_comm _ _
theorem slice_succ_mul_choose_le (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (j : ℕ) :
    #(𝒜 # (j + 1)) * (Fintype.card σ).choose j
      ≤ #(𝒜 # j) * (Fintype.card σ).choose (j + 1) := by
  have h1 := slice_succ_mul_le 𝒜 h j
  have h2 := Nat.choose_succ_right_eq (Fintype.card σ) j
  refine Nat.le_of_mul_le_mul_left (?_ : (j + 1) * _ ≤ (j + 1) * _) (Nat.succ_pos j)
  calc (j + 1) * (#(𝒜 # (j + 1)) * (Fintype.card σ).choose j)
      = ((j + 1) * #(𝒜 # (j + 1))) * (Fintype.card σ).choose j := by ring
    _ ≤ ((Fintype.card σ - j) * #(𝒜 # j)) * (Fintype.card σ).choose j :=
        Nat.mul_le_mul_right _ h1
    _ = #(𝒜 # j) * ((Fintype.card σ).choose j * (Fintype.card σ - j)) := by ring
    _ = #(𝒜 # j) * ((Fintype.card σ).choose (j + 1) * (j + 1)) := by rw [h2]
    _ = (j + 1) * (#(𝒜 # j) * (Fintype.card σ).choose (j + 1)) := by ring
omit [DecidableEq σ] [Fintype σ] in
theorem mediant_partial_sums (b c : ℕ → ℕ) (k : ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (h : ∀ j ≤ k, b (j + 1) * c j ≤ b j * c (j + 1)) :
    (∑ j ∈ range (k + 2), b j) * (∑ j ∈ range (k + 1), c j)
      ≤ (∑ j ∈ range (k + 1), b j) * (∑ j ∈ range (k + 2), c j) := by
  have key : ∀ l, l ≤ k + 1 → ∀ j ≤ l, b l * c j ≤ b j * c l := by
    intro l
    induction l with
    | zero =>
      intro _ j hj
      obtain rfl : j = 0 := by omega
      exact le_rfl
    | succ l ih =>
      intro hl j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · exact le_rfl
      have i1 := ih (by omega) j (by omega)
      have i2 := h l (by omega)
      have hp := hc l (by omega)
      refine Nat.le_of_mul_le_mul_left (?_ : c l * _ ≤ c l * _) hp
      calc c l * (b (l + 1) * c j) = (b (l + 1) * c l) * c j := by ring
        _ ≤ (b l * c (l + 1)) * c j := Nat.mul_le_mul_right _ i2
        _ = (b l * c j) * c (l + 1) := by ring
        _ ≤ (b j * c l) * c (l + 1) := Nat.mul_le_mul_right _ i1
        _ = c l * (b j * c (l + 1)) := by ring
  rw [Finset.sum_range_succ b (k + 1), Finset.sum_range_succ c (k + 1)]
  have h1 : b (k + 1) * ∑ j ∈ range (k + 1), c j ≤ (∑ j ∈ range (k + 1), b j) * c (k + 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj =>
      key (k + 1) le_rfl j (by have := Finset.mem_range.1 hj; omega)
  rw [add_mul, mul_add]
  exact Nat.add_le_add_left h1 _
theorem downClosed_partial_sums (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (k : ℕ) :
    (∑ j ∈ range (k + 2), #(𝒜 # j)) * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ (∑ j ∈ range (k + 1), #(𝒜 # j))
          * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (k + 1) with hk | hk
  · have h0 : #(𝒜 # (k + 1)) = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    rw [Finset.sum_range_succ (fun j => #(𝒜 # j)) (k + 1), h0, add_zero]
    exact Nat.mul_le_mul_left _
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega)))
  · exact mediant_partial_sums (fun j => #(𝒜 # j)) (fun j => (Fintype.card σ).choose j) k
      (fun j hj => Nat.choose_pos (by omega)) (fun j _ => slice_succ_mul_choose_le 𝒜 h j)
omit [Fintype σ] in
theorem sum_slice_eq_card_filter (𝒜 : Finset (Finset σ)) (k : ℕ) :
    ∑ j ∈ range (k + 1), #(𝒜 # j) = #(𝒜.filter (fun s => #s ≤ k)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))
    (fun s hs => Finset.mem_range.2 (by have := (Finset.mem_filter.1 hs).2; omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  ext s
  have := Finset.mem_range.1 hj
  simp only [Finset.mem_slice, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
omit [Fintype σ] in
theorem isLowerSet_of_erase (𝒜 : Finset (Finset σ))
    (h : ∀ s ∈ 𝒜, ∀ a ∈ s, s.erase a ∈ 𝒜) : IsLowerSet (𝒜 : Set (Finset σ)) := by
  intro s t hts hs
  have key : ∀ u : Finset σ, u ⊆ s → s \ u ∈ 𝒜 := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro _; simpa using hs
    | insert a u ha ih =>
      intro hu
      rw [Finset.sdiff_insert]
      refine h _ (ih ((Finset.subset_insert a u).trans hu)) a ?_
      exact Finset.mem_sdiff.2 ⟨hu (Finset.mem_insert_self a u), ha⟩
  have h1 := key (s \ t) Finset.sdiff_subset
  rw [Finset.sdiff_sdiff_eq_self hts] at h1
  exact Finset.mem_coe.2 h1
end Combinatorial
section Algebraic
variable {σ : Type*} {F : Type*} [Field F]
def leadSet (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) : Set (σ →₀ ℕ) :=
  {d | ∃ q ∈ Z, q ≠ 0 ∧ m.degree q = d}
theorem degree_sub_lt_of_lead_eq (m : MonomialOrder σ) {f g : MvPolynomial σ F}
    (hd : m.degree f = m.degree g) (hc : m.leadingCoeff f = m.leadingCoeff g)
    (hne : f - g ≠ 0) : m.degree (f - g) ≺[m] m.degree f := by
  apply lt_of_le_of_ne
  · have h1 := m.degree_sub_le (f := f) (g := g)
    rw [← hd, sup_idem] at h1
    exact h1
  · intro h'
    have h'' : m.degree (f - g) = m.degree f := m.toSyn.injective h'
    have h2 := m.degree_mem_support hne
    rw [h'', mem_support_iff, coeff_sub] at h2
    apply h2
    have h3 : g.coeff (m.degree f) = m.leadingCoeff g := by rw [hd]; rfl
    rw [h3, ← hc]
    exact sub_self _
theorem linearIndependent_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) :
    LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
  have hli : LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => monomial (d : σ →₀ ℕ) (1 : F)) := by
    have := (MvPolynomial.basisMonomials σ F).linearIndependent.comp
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => (d : σ →₀ ℕ)) Subtype.val_injective
    simpa [Function.comp_def] using this
  refine hli.map ?_
  rw [Submodule.ker_mkQ, Submodule.disjoint_def]
  intro p hp hZ
  by_contra hne
  have hsupp : p ∈ restrictSupport F ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) := by
    rw [restrictSupport_eq_span, Set.image_eq_range]
    exact hp
  have h1 : m.degree p ∈ ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) :=
    ((mem_restrictSupport_iff F).1 hsupp) (Finset.mem_coe.2 (m.degree_mem_support hne))
  exact h1 ⟨p, hZ, hne, rfl⟩
theorem mkQ_mem_span_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F))
    (p : MvPolynomial σ F) :
    Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
      {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
  suffices H : ∀ a : m.syn, ∀ p : MvPolynomial σ F, m.toSyn (m.degree p) = a →
      Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
        {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) from H _ p rfl
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro p hpa
    by_cases hp : p = 0
    · rw [hp, map_zero]
      exact Submodule.zero_mem _
    have hc : m.leadingCoeff p ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hp
    obtain ⟨g, hgd, hgc, hgmem⟩ : ∃ g : MvPolynomial σ F, m.degree g = m.degree p ∧
        m.leadingCoeff g = m.leadingCoeff p ∧
        Z.mkQ g ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
          {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
      by_cases hd : m.degree p ∈ leadSet m Z
      · obtain ⟨q, hqZ, hq0, hqd⟩ := hd
        have hcq : m.leadingCoeff q ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hq0
        have hr : m.leadingCoeff p / m.leadingCoeff q ≠ 0 := div_ne_zero hc hcq
        have hdeg : m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q) = m.degree p := by
          rw [m.degree_smul_of_isRegular (IsRegular.of_ne_zero hr), hqd]
        refine ⟨(m.leadingCoeff p / m.leadingCoeff q) • q, hdeg, ?_, ?_⟩
        · show ((m.leadingCoeff p / m.leadingCoeff q) • q).coeff
            (m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q)) = _
          rw [hdeg, coeff_smul, smul_eq_mul, ← hqd]
          exact div_mul_cancel₀ _ hcq
        · have : Z.mkQ ((m.leadingCoeff p / m.leadingCoeff q) • q) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Z.smul_mem _ hqZ
          rw [this]
          exact Submodule.zero_mem _
      · classical
        refine ⟨monomial (m.degree p) (m.leadingCoeff p), ?_, ?_, ?_⟩
        · rw [m.degree_monomial, if_neg hc]
        · exact m.leadingCoeff_monomial _
        · have : monomial (m.degree p) (m.leadingCoeff p)
              = m.leadingCoeff p • monomial (m.degree p) (1 : F) := by
            rw [smul_monomial, smul_eq_mul, mul_one]
          rw [this, map_smul]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨m.degree p, ⟨hd, le_rfl⟩, rfl⟩)
    have hsplit : Z.mkQ p = Z.mkQ (p - g) + Z.mkQ g := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ hgmem
    by_cases hpg : p - g = 0
    · rw [hpg, map_zero]
      exact Submodule.zero_mem _
    have hlt : m.degree (p - g) ≺[m] m.degree p :=
      degree_sub_lt_of_lead_eq m hgd.symm hgc.symm hpg
    have h1 := ih (m.toSyn (m.degree (p - g))) (hpa ▸ hlt) (p - g) rfl
    refine Submodule.span_mono (Set.image_mono ?_) h1
    rintro d ⟨hd1, hd2⟩
    exact ⟨hd1, hd2.trans hlt.le⟩
theorem finrank_quotient_comap_eq_finrank_map (Z V : Submodule F (MvPolynomial σ F)) :
    Module.finrank F (V ⧸ Z.comap V.subtype) = Module.finrank F (V.map Z.mkQ) := by
  have h1 : LinearMap.ker (Z.mkQ ∘ₗ V.subtype) = Z.comap V.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h2 : LinearMap.range (Z.mkQ ∘ₗ V.subtype) = V.map Z.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ((Submodule.quotEquivOfEq _ _ h1.symm).trans
    ((Z.mkQ ∘ₗ V.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h2))).finrank_eq
section DegLex
variable [LinearOrder σ] [WellFoundedGT σ]
theorem map_restrictTotalDegree_eq_span (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    (restrictTotalDegree σ F k).map Z.mkQ
      = Submodule.span F (Set.range
          (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
            Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F)))) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ k := (mem_restrictTotalDegree σ k p).1 hp
    refine Submodule.span_mono ?_ (mkQ_mem_span_std MonomialOrder.degLex Z p)
    rintro _ ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have h1 : d.degree ≤ (MonomialOrder.degLex.degree p).degree :=
      Finsupp.DegLex.monotone_degree hd2
    rw [degree_degLexDegree] at h1
    exact ⟨⟨d, hd1, h1.trans hp'⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨d, hd1, hd2⟩, rfl⟩
    refine ⟨monomial d 1, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree, totalDegree_monomial _ one_ne_zero]
    exact hd2
theorem finrank_map_restrictTotalDegree (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
      = Set.ncard {d : σ →₀ ℕ | d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} := by
  have hli : LinearIndependent F
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
    have := (linearIndependent_std MonomialOrder.degLex Z).comp
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        (⟨d.1, d.2.1⟩ : ((leadSet MonomialOrder.degLex Z)ᶜ : Set (σ →₀ ℕ))))
      (by intro a b hab; simp only [Subtype.mk.injEq] at hab; exact Subtype.ext hab)
    simpa [Function.comp_def] using this
  rw [map_restrictTotalDegree_eq_span, Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]
  rfl
noncomputable def ind (s : Finset σ) : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1
omit [WellFoundedGT σ] in
theorem ind_apply (s : Finset σ) (i : σ) : ind s i = if i ∈ s then 1 else 0 := by
  classical
  simp [ind, Finsupp.single_apply]
omit [WellFoundedGT σ] in
theorem ind_degree (s : Finset σ) : (ind s).degree = #s := by
  simp [ind]
omit [WellFoundedGT σ] in
theorem ind_injective : Function.Injective (ind : Finset σ → σ →₀ ℕ) := by
  intro s t h
  ext i
  have h1 := DFunLike.congr_fun h i
  rw [ind_apply, ind_apply] at h1
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
omit [WellFoundedGT σ] in
theorem ind_support_of_le_one (d : σ →₀ ℕ) (h : ∀ i, d i ≤ 1) : ind d.support = d := by
  ext i
  rw [ind_apply]
  have := h i
  by_cases hi : i ∈ d.support
  · rw [if_pos hi]
    have := Finsupp.mem_support_iff.1 hi
    omega
  · rw [if_neg hi]
    exact (Finsupp.notMem_support_iff.1 hi).symm
variable (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
theorem std_le_one
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ) :
    d i ≤ 1 := by
  classical
  by_contra hi
  apply hd
  set e : σ →₀ ℕ := d - Finsupp.single i 2 with he
  have hde : d = e + Finsupp.single i 2 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]; omega
    · simp [he, Finsupp.single_apply, Ne.symm hj]
  have hdeg : e.degree + 2 = d.degree := by
    rw [hde, map_add, Finsupp.degree_single]
  have hq : monomial e (1 : F) * (X i ^ 2 - X i)
      = monomial (e + Finsupp.single i 2) (1 : F) - monomial (e + Finsupp.single i 1) (1 : F) := by
    rw [mul_sub, X_pow_eq_monomial, monomial_mul, X, monomial_mul, mul_one]
  have hlt : MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 1) (1 : F))
      ≺[MonomialOrder.degLex]
      MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 2) (1 : F)) := by
    rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial, if_neg one_ne_zero,
      if_neg one_ne_zero]
    apply MonomialOrder.degLex.toSyn_strictMono
    apply lt_of_le_of_ne
    · exact add_le_add le_rfl (Finsupp.single_le_single.2 (show (1 : ℕ) ≤ 2 by omega))
    · intro h
      have := DFunLike.congr_fun h i
      simp at this
  refine ⟨monomial e (1 : F) * (X i ^ 2 - X i), hB e i (by omega), ?_, ?_⟩
  · rw [hq]
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [hq, MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_monomial,
      if_neg one_ne_zero, ← hde]
theorem std_sub_single
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ)
    (hi : 1 ≤ d i) : d - Finsupp.single i 1 ∉ leadSet MonomialOrder.degLex Z := by
  classical
  rintro ⟨q, hqZ, hq0, hqd⟩
  apply hd
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  have hdeg : 1 + (d - Finsupp.single i 1).degree = d.degree := by
    conv_rhs => rw [hde, map_add, Finsupp.degree_single]
  have hqt : q.totalDegree < K := by
    rw [← degree_degLexDegree, hqd]
    omega
  have hXne : (X i : MvPolynomial σ F) ≠ 0 := X_ne_zero i
  refine ⟨X i * q, hX q hqZ hqt i, mul_ne_zero hXne hq0, ?_⟩
  rw [MonomialOrder.degree_mul hXne hq0, MonomialOrder.degree_X, hqd, ← hde]
end DegLex
end Algebraic
section Combined
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F]
theorem exists_downClosed_family [DecidableEq σ] (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z) :
    ∃ 𝒜 : Finset (Finset σ), IsLowerSet (𝒜 : Set (Finset σ)) ∧ ∀ k ≤ K,
      Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        = ∑ j ∈ range (k + 1), #(𝒜 # j) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  set L := leadSet (F := F) MonomialOrder.degLex Z with hL
  refine ⟨Finset.univ.filter (fun s => ind s ∉ L ∧ #s ≤ K), ?_, ?_⟩
  · apply isLowerSet_of_erase
    intro s hs a ha
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨-, hs1, hs2⟩ := hs
    refine ⟨Finset.mem_univ _, ?_, (Finset.card_erase_le).trans hs2⟩
    have h1 : ind (s.erase a) = ind s - Finsupp.single a 1 := by
      ext j
      rw [Finsupp.tsub_apply, ind_apply, ind_apply, Finsupp.single_apply]
      by_cases hj : a = j
      · subst hj; simp [ha]
      · simp [hj, Ne.symm hj]
    rw [h1]
    exact std_sub_single Z K hX (ind s) hs1 (by rw [ind_degree]; exact hs2) a
      (by rw [ind_apply, if_pos ha])
  · intro k hk
    rw [finrank_map_restrictTotalDegree, sum_slice_eq_card_filter, ← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective _ ind_injective]
    congr 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd1, hd2⟩
      have h1 : ind d.support = d :=
        ind_support_of_le_one d (std_le_one Z K hB d hd1 (hd2.trans hk))
      have h2 : #d.support = d.degree := by rw [← ind_degree, h1]
      refine ⟨d.support, ⟨⟨?_, ?_⟩, ?_⟩, h1⟩
      · rw [h1]; exact hd1
      · omega
      · omega
    · rintro ⟨s, ⟨⟨hs1, _⟩, hs3⟩, rfl⟩
      exact ⟨hs1, by rw [ind_degree]; exact hs3⟩
theorem rank_ratio_monotone (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (k : ℕ) (hk : k + 1 ≤ K) :
    Module.finrank F ((restrictTotalDegree σ F (k + 1)).map Z.mkQ)
        * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  classical
  obtain ⟨𝒜, h𝒜, hc⟩ := exists_downClosed_family Z K hX hB
  rw [hc (k + 1) hk, hc k (by omega)]
  exact downClosed_partial_sums 𝒜 h𝒜 k
end Combined
end MonoRank
end PEqualNP.Outside.L_pcx_377.H.Helpers

namespace PEqualNP.Outside.L_pcx_377.H.Helpers
open Module
section Abstract
variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
theorem threeTerm_finrank [FiniteDimensional F U] (I A B L : Submodule F U)
    (h : L ⊓ (A ⊔ B) ≤ A ⊓ B) :
    finrank F ↥(I ⊓ A) + finrank F ↥(I ⊓ B) + finrank F ↥(I ⊓ L)
      ≤ finrank F ↥I + 2 * finrank F ↥(I ⊓ A ⊓ B) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (I ⊓ A) (I ⊓ B)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq ((I ⊓ A) ⊔ (I ⊓ B)) (I ⊓ L)
  have hPQ : (I ⊓ A) ⊓ (I ⊓ B) = I ⊓ A ⊓ B := by
    rw [← inf_inf_distrib_left, inf_assoc]
  have hup : ((I ⊓ A) ⊔ (I ⊓ B)) ⊔ (I ⊓ L) ≤ I :=
    sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hdown : ((I ⊓ A) ⊔ (I ⊓ B)) ⊓ (I ⊓ L) ≤ I ⊓ A ⊓ B := by
    rw [inf_assoc]
    refine le_inf ?_ ?_
    · exact inf_le_right.trans inf_le_left
    · refine le_trans ?_ h
      exact le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (sup_le_sup inf_le_right inf_le_right))
  have h1 := Submodule.finrank_mono hup
  have h2 := Submodule.finrank_mono hdown
  rw [hPQ] at e1
  omega
variable {G : Type*}
noncomputable def subDim (S : Submodule F U) : ℕ := finrank F ↥S
theorem subDim_mono [FiniteDimensional F U] {S T : Submodule F U} (h : S ≤ T) :
    subDim S ≤ subDim T := Submodule.finrank_mono h
theorem subDim_top : subDim (⊤ : Submodule F U) = finrank F U := finrank_top F U
noncomputable def kerSum [Add G] (K : G → Submodule F U) : G → List G → ℕ
  | c, [] => subDim (K c)
  | c, b :: bs => kerSum K c bs + kerSum K (c + b) bs
def listInf (K : G → Submodule F U) : List G → Submodule F U
  | [] => ⊤
  | b :: bs => K b ⊓ listInf K bs
theorem listInf_le (K : G → Submodule F U) {b : G} :
    ∀ {bs : List G}, b ∈ bs → listInf K bs ≤ K b
  | [], hb => by simp at hb
  | a :: bs, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact inf_le_left
    · exact inf_le_right.trans (listInf_le K hb)
private theorem arith_step (N S1 S2 dI dU d1 d2 d3 dJ dJ' : ℕ)
    (ih1 : 2 * S1 + N * dI ≤ N * dU + 2 * (N * d1))
    (ih2 : 2 * S2 + N * dI ≤ N * dU + 2 * (N * d2))
    (tt : d1 + d2 + d3 ≤ dI + 2 * dJ) (hJ : dJ ≤ dJ') :
    2 * (S1 + S2) + (2 * N) * d3 ≤ (2 * N) * dU + 2 * ((2 * N) * dJ') := by
  nlinarith [Nat.mul_le_mul_left N tt, Nat.mul_le_mul_left N hJ]
theorem kerSum_le [Add G] [FiniteDimensional F U] (K : G → Submodule F U)
    (hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b)
    (hthree : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b)) :
    ∀ (bs : List G) (c : G),
      2 * kerSum K c bs + 2 ^ bs.length * subDim (listInf K bs)
        ≤ 2 ^ bs.length * finrank F U
          + 2 * (2 ^ bs.length * subDim (listInf K bs ⊓ K c))
  | [], c => by
    have h1 : listInf K ([] : List G) = ⊤ := rfl
    have h2 : kerSum K c [] = subDim (K c) := rfl
    rw [h1, h2, top_inf_eq, subDim_top]
    simp only [List.length_nil, pow_zero, one_mul]
    omega
  | b :: bs, c => by
    have ih1 := kerSum_le K hadd hthree bs c
    have ih2 := kerSum_le K hadd hthree bs (c + b)
    have tt : subDim (listInf K bs ⊓ K c) + subDim (listInf K bs ⊓ K (c + b))
        + subDim (K b ⊓ listInf K bs)
        ≤ subDim (listInf K bs) + 2 * subDim (listInf K bs ⊓ K c ⊓ K (c + b)) := by
      have := threeTerm_finrank (listInf K bs) (K c) (K (c + b)) (K b) (hthree c b)
      rw [inf_comm (listInf K bs) (K b)] at this
      exact this
    have hJ : listInf K bs ⊓ K c ⊓ K (c + b) ≤ K b ⊓ listInf K bs ⊓ K c := by
      refine le_inf (le_inf ?_ (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (hadd c b)
    have hJ' := subDim_mono hJ
    have h1 : listInf K (b :: bs) = K b ⊓ listInf K bs := rfl
    have h2 : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [h1, h2, hp]
    have hU := arith_step (2 ^ bs.length) _ _ _ (finrank F U) _ _ _ _ _ ih1 ih2 tt hJ'
    exact hU
theorem exists_le_kerSum [Add G] (K : G → Submodule F U) :
    ∀ (bs : List G) (c : G), ∃ c', 2 ^ bs.length * subDim (K c') ≤ kerSum K c bs
  | [], c => ⟨c, by simp [kerSum]⟩
  | b :: bs, c => by
    obtain ⟨c1, h1⟩ := exists_le_kerSum K bs c
    obtain ⟨c2, h2⟩ := exists_le_kerSum K bs (c + b)
    have e : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [e, hp]
    rcases le_total (subDim (K c1)) (subDim (K c2)) with h | h
    · refine ⟨c1, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
    · refine ⟨c2, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
end Abstract
section Maps
variable {F U W G : Type*} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup W]
  [Module F W] [AddCommGroup G]
theorem exists_two_mul_finrank_ker_le [FiniteDimensional F U] (Φ : G →+ (U →ₗ[F] W))
    (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (bs : List G) :
    ∃ c : G, 2 * finrank F ↥(LinearMap.ker (Φ c))
      ≤ finrank F U + finrank F ↥(listInf (fun c => LinearMap.ker (Φ c)) bs) := by
  set K : G → Submodule F U := fun c => LinearMap.ker (Φ c) with hKdef
  have hcancel : ∀ c b : G, c + (c + b) = b := fun c b => by
    rw [← add_assoc, h2, zero_add]
  have hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b := by
    intro c b f hf
    have h1 : Φ c f = 0 := hf.1
    have h3 : Φ (c + b) f = 0 := hf.2
    have : Φ b f = 0 := by
      rw [map_add, LinearMap.add_apply, h1, zero_add] at h3
      exact h3
    exact this
  have hthree' : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b) := by
    intro c b f hf
    have hb : Φ b f = 0 := hf.1
    refine ⟨?_, ?_⟩
    · exact hthree c (c + b) f (by rw [hcancel]; exact hb) hf.2
    · refine hthree (c + b) c f ?_ ?_
      · rw [add_comm, hcancel]; exact hb
      · have := hf.2
        rwa [sup_comm] at this
  have key := kerSum_le K hadd hthree' bs 0
  obtain ⟨c, hc⟩ := exists_le_kerSum K bs (0 : G)
  refine ⟨c, ?_⟩
  have hle : subDim (listInf K bs ⊓ K 0) ≤ subDim (listInf K bs) := subDim_mono inf_le_left
  have hpos : 0 < 2 ^ bs.length := by positivity
  have t := Nat.mul_le_mul_left (2 ^ bs.length) hle
  have : 2 ^ bs.length * (2 * subDim (K c))
      ≤ 2 ^ bs.length * (finrank F U + subDim (listInf K bs)) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos
theorem rank_retention [FiniteDimensional F U] {W' : Type*} [AddCommGroup W'] [Module F W']
    (Φ : G →+ (U →ₗ[F] W)) (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (S : U →ₗ[F] W') (bs : List G)
    (hS : ∀ f : U, (∀ b ∈ bs, Φ b f = 0) → S f = 0) :
    ∃ c : G, finrank F ↥(LinearMap.range S) ≤ 2 * finrank F ↥(LinearMap.range (Φ c)) := by
  obtain ⟨c, hc⟩ := exists_two_mul_finrank_ker_le Φ h2 hthree bs
  refine ⟨c, ?_⟩
  have hI : listInf (fun c => LinearMap.ker (Φ c)) bs ≤ LinearMap.ker S := by
    intro f hf
    exact hS f fun b hb => listInf_le (fun c => LinearMap.ker (Φ c)) hb hf
  have hI' := Submodule.finrank_mono hI
  have r1 := LinearMap.finrank_range_add_finrank_ker S
  have r2 := LinearMap.finrank_range_add_finrank_ker (Φ c)
  omega
theorem rank_retention_pi {ι U W : Type*} [Fintype ι] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (M : ι → U →ₗ[ZMod 2] W)
    (hthree : ∀ a b : ι → ZMod 2, ∀ f : U, (∑ i, (a i + b i) • M i) f = 0 →
      f ∈ LinearMap.ker (∑ i, a i • M i) ⊔ LinearMap.ker (∑ i, b i • M i) →
      (∑ i, a i • M i) f = 0) :
    ∃ c : ι → ZMod 2, finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi M))
      ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (∑ i, c i • M i)) := by
  classical
  let Φ : (ι → ZMod 2) →+ (U →ₗ[ZMod 2] W) :=
    { toFun := fun c => ∑ i, c i • M i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hsingle : ∀ i : ι, Φ (Pi.single i 1) = M i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • M j = M i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  refine rank_retention Φ h2 (fun a b f h1 h3 => hthree a b f h1 h3) (LinearMap.pi M)
    (Finset.univ.toList.map fun i => Pi.single i 1) ?_
  intro f hf
  funext i
  have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
  rw [hsingle] at this
  simpa using this
end Maps
section Multiplication
open MvPolynomial
variable {σ ι τ : Type*}
noncomputable def mulMap (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) :
    ↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C) :=
  LinearMap.pi fun α => C.mkQ ∘ₗ LinearMap.mulRight (ZMod 2) (q * h α) ∘ₗ U.subtype
theorem mulMap_apply_eq_zero (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) (f : ↥U) :
    mulMap C U h q f = 0 ↔ ∀ α, (f : MvPolynomial σ (ZMod 2)) * q * h α ∈ C := by
  rw [funext_iff]
  refine forall_congr' fun α => ?_
  simp [mulMap, mul_assoc]
noncomputable def comb [Fintype ι] (g : ι → MvPolynomial σ (ZMod 2)) (c : ι → ZMod 2) :
    MvPolynomial σ (ZMod 2) := ∑ i, c i • g i
theorem rank_retention_mul [Fintype ι]
    (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (g : ι → MvPolynomial σ (ZMod 2)) (h : τ → MvPolynomial σ (ZMod 2))
    (hmul : ∀ (c c' : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * comb g c * h α ∈ C → f * comb g c * comb g c' * h α ∈ C)
    (hidem : ∀ (c : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * (comb g c * comb g c + comb g c) * h α ∈ C) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi fun i => mulMap C U h (g i)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (mulMap C U h (comb g c))) := by
  classical
  have hcomb_add : ∀ a b : ι → ZMod 2, comb g (a + b) = comb g a + comb g b := fun a b => by
    simp [comb, add_smul, Finset.sum_add_distrib]
  have hcomb_single : ∀ i : ι, comb g (Pi.single i 1) = g i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • g j = g i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let Φ : (ι → ZMod 2) →+ (↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C)) :=
    { toFun := fun c => mulMap C U h (comb g c)
      map_zero' := by
        ext f α
        simp [mulMap, comb]
      map_add' := fun a b => by
        ext f α
        simp [mulMap, hcomb_add, add_mul, mul_add, mul_assoc] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hthree : ∀ a b : ι → ZMod 2, ∀ f : ↥U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0 := by
    intro a b f hab hf
    obtain ⟨fa, hfa, fb, hfb, rfl⟩ := Submodule.mem_sup.1 hf
    have hfa' : ∀ α, (fa : MvPolynomial σ (ZMod 2)) * comb g a * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g a) fa).1 hfa
    have hfb' : ∀ α, (fb : MvPolynomial σ (ZMod 2)) * comb g b * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g b) fb).1 hfb
    have hab' : ∀ α, ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g (a + b)) (fa + fb)).1 hab
    refine (mulMap_apply_eq_zero C U h (comb g a) (fa + fb)).2 fun α => ?_
    have A1 := hmul a b α fa fa.2 (hfa' α)
    have A2 := hmul b a α fb fb.2 (hfb' α)
    have A3 := hmul (a + b) a α _ (fa + fb).2 (hab' α)
    have A4 := hidem a α _ (fa + fb).2
    have e : ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g a * h α
        = ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * (comb g a * comb g a + comb g a) * h α
          - ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * comb g a * h α
          + ((fa : MvPolynomial σ (ZMod 2)) * comb g a * comb g b * h α
            + (fb : MvPolynomial σ (ZMod 2)) * comb g b * comb g a * h α) := by
      rw [hcomb_add, Submodule.coe_add]
      ring
    rw [e]
    exact C.add_mem (C.sub_mem A4 A3) (C.add_mem A1 A2)
  obtain ⟨c, hc⟩ := rank_retention Φ h2 hthree
    (LinearMap.pi fun i => mulMap C U h (g i))
    (Finset.univ.toList.map fun i => Pi.single i 1) (by
      intro f hf
      funext i
      have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
      have e : Φ (Pi.single i 1) = mulMap C U h (g i) := by
        show mulMap C U h (comb g (Pi.single i 1)) = _
        rw [hcomb_single]
      rw [e] at this
      simpa using this)
  exact ⟨c, hc⟩
noncomputable def affine [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) : MvPolynomial σ (ZMod 2) :=
  C a + ∑ j, C (B j) * X j
theorem comb_affine [Fintype σ] [Fintype ι] (a : ι → ZMod 2) (B : ι → σ → ZMod 2)
    (c : ι → ZMod 2) :
    comb (fun i => affine (a i) (B i)) c
      = affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) := by
  simp only [comb, affine, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · simp [map_sum, smul_eq_C_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_sum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]
theorem affine_totalDegree_le [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    (affine a B).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]
theorem affine_idem [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    affine a B * affine a B + affine a B = ∑ j, C (B j) * (X j * X j + X j) := by
  have ha : ∀ x : ZMod 2, x * x = x := by decide
  have hC : ∀ x : ZMod 2, (C x : MvPolynomial σ (ZMod 2)) * C x = C x := fun x => by
    rw [← C_mul, ha]
  have e1 : (∑ j, (C (B j) : MvPolynomial σ (ZMod 2)) * X j) * (∑ j, C (B j) * X j)
      = ∑ j, C (B j) * (X j * X j) := by
    rw [← sq, CharTwo.sum_sq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
    calc (C (B j) : MvPolynomial σ (ZMod 2)) * X j * (C (B j) * X j)
        = (C (B j) * C (B j)) * (X j * X j) := by ring
      _ = C (B j) * (X j * X j) := by rw [hC]
  rw [affine, CharTwo.add_mul_self, hC, e1]
  have e2 : ∀ u v w : MvPolynomial σ (ZMod 2), u + v + (u + w) = (u + u) + (v + w) :=
    fun u v w => by ring
  rw [e2, CharTwo.add_self_eq_zero, zero_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
theorem rank_retention_closure [Fintype σ] [Fintype ι]
    (Cl U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (D k d : ℕ)
    (hX : ∀ p ∈ Cl, p.totalDegree < D → ∀ j, X j * p ∈ Cl)
    (hBool : ∀ p : MvPolynomial σ (ZMod 2), p.totalDegree + 2 ≤ D →
      ∀ j, p * (X j * X j + X j) ∈ Cl)
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (a : ι → ZMod 2) (B : ι → σ → ZMod 2) (h : τ → MvPolynomial σ (ZMod 2))
    (hh : ∀ α, (h α).totalDegree ≤ d) (hD : d + k + 2 ≤ D) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2)
          ↥(LinearMap.range (LinearMap.pi fun i => mulMap Cl U h (affine (a i) (B i))))
        ≤ 2 * finrank (ZMod 2)
          ↥(LinearMap.range (mulMap Cl U h (comb (fun i => affine (a i) (B i)) c))) := by
  have hmulaff : ∀ p ∈ Cl, p.totalDegree < D → ∀ (a' : ZMod 2) (B' : σ → ZMod 2),
      p * affine a' B' ∈ Cl := by
    intro p hp hdeg a' B'
    have e : p * affine a' B' = a' • p + ∑ j, B' j • (X j * p) := by
      rw [affine, mul_add, Finset.mul_sum]
      congr 1
      · rw [smul_eq_C_mul, mul_comm]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_C_mul]
        ring
    rw [e]
    exact Cl.add_mem (Cl.smul_mem _ hp)
      (Cl.sum_mem fun j _ => Cl.smul_mem _ (hX p hp hdeg j))
  refine rank_retention_mul Cl U (fun i => affine (a i) (B i)) h ?_ ?_
  · intro c c' α f hf hmem
    rw [comb_affine] at hmem ⊢
    rw [comb_affine]
    have hdeg : (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) * h α).totalDegree
        < D := by
      have h1 := totalDegree_mul
        (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)) (h α)
      have h2 := totalDegree_mul f (affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j))
      have h3 := hU f hf
      have h4 := hh α
      have h5 := affine_totalDegree_le (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)
      omega
    have := hmulaff _ hmem hdeg (∑ i, c' i * a i) (fun j => ∑ i, c' i * B i j)
    have e : ∀ u v w x : MvPolynomial σ (ZMod 2), u * v * w * x = u * v * x * w :=
      fun u v w x => by ring
    rw [e]
    exact this
  · intro c α f hf
    rw [comb_affine, affine_idem]
    have e : f * (∑ j, C (∑ i, c i * B i j) * (X j * X j + X j)) * h α
        = ∑ j, (∑ i, c i * B i j) • ((f * h α) * (X j * X j + X j)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]
      ring
    rw [e]
    refine Cl.sum_mem fun j _ => Cl.smul_mem _ (hBool _ ?_ j)
    have h1 := totalDegree_mul f (h α)
    have h3 := hU f hf
    have h4 := hh α
    omega
end Multiplication
end PEqualNP.Outside.L_pcx_377.H.Helpers

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeRank
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
section Glue
variable {σ : Type}
theorem exists_single_add (d : σ →₀ ℕ) (hd : d ≠ 0) :
    ∃ (i : σ) (e : σ →₀ ℕ), d = Finsupp.single i 1 + e ∧ e.degree + 1 = d.degree := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finsupp.ext h)
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp [Ne.symm hj]
  refine ⟨i, d - Finsupp.single i 1, hde, ?_⟩
  have h := congrArg Finsupp.degree hde
  rw [map_add, Finsupp.degree_single] at h
  omega
theorem totalDegree_monomial_one (d : σ →₀ ℕ) :
    (monomial d (1 : ZMod 2)).totalDegree = d.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl
theorem bool_totalDegree_le (v : σ) :
    (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_X]
    omega
theorem monomial_mul_mem {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (hC : DegClosed C D) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree = n → ∀ f ∈ C, n + f.totalDegree ≤ D →
      monomial d (1 : ZMod 2) * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro d hd f hf _
    have h0 : d = 0 := by
      by_contra hne
      obtain ⟨i, e, -, he⟩ := exists_single_add d hne
      omega
    subst h0
    simpa using hf
  | succ n ih =>
    intro d hd f hf hdeg
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, e, hde, he⟩ := exists_single_add d hne
    have h1 := ih e (by omega) f hf (by omega)
    have h2 : (monomial e (1 : ZMod 2) * f).totalDegree + 1 ≤ D := by
      have h3 := totalDegree_mul (monomial e (1 : ZMod 2)) f
      have h4 := totalDegree_monomial_one e
      omega
    have h5 := hC.mulX i _ h1 h2
    have e5 : monomial d (1 : ZMod 2) * f = X i * (monomial e 1 * f) := by
      rw [hde, ← mul_assoc]
      congr 1
      rw [X, monomial_mul_monomial, mul_one]
    rw [e5]
    exact h5
theorem absorb {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ} (hC : DegClosed C D)
    (f g : MvPolynomial σ (ZMod 2)) (hf : f ∈ C) (hdeg : g.totalDegree + f.totalDegree ≤ D) :
    g * f ∈ C := by
  have e : g * f = ∑ v ∈ g.support, g.coeff v • (monomial v (1 : ZMod 2) * f) := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine C.sum_mem fun v hv => C.smul_mem _ (monomial_mul_mem hC _ v rfl f hf ?_)
  have h1 : v.degree ≤ g.totalDegree := le_totalDegree hv
  omega
instance finite_restrictTotalDegree [Finite σ] (k : ℕ) :
    Module.Finite (ZMod 2) ↥(restrictTotalDegree σ (ZMod 2) k) := by
  have hfin : Finite ↥{u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Set.Finite.to_subtype ((Finsupp.finite_of_degree_le k).subset fun u hu => hu)
  exact Module.Finite.of_basis
    (basisRestrictSupport (ZMod 2) {u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k})
theorem errRank_eq_range [Finite σ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (M : Set (MvPolynomial σ (ZMod 2)))
    (k : ℕ) (L : ↥(polyLE σ k) →ₗ[ZMod 2] W)
    (hL : ∀ f : ↥(polyLE σ k), L f = 0 ↔ ∀ m ∈ M, m * (f : MvPolynomial σ (ZMod 2)) ∈ C) :
    finrank (ZMod 2) ↥(LinearMap.range L) = errRank C M k := by
  have hle : errKer C M k ≤ polyLE σ k := inf_le_left
  have hker : LinearMap.ker L = (errKer C M k).comap (polyLE σ k).subtype := by
    ext f
    rw [LinearMap.mem_ker, hL, Submodule.mem_comap, mem_errKer]
    exact ⟨fun h => ⟨(mem_restrictTotalDegree σ k _).1 f.2, h⟩, fun h => h.2⟩
  have r := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at r
  unfold errRank
  omega
noncomputable def annih (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_annih {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ annih C M ↔ ∀ m ∈ M, m * f ∈ C := by
  simp [annih]
theorem errRank_eq_map [Finite σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errRank C M k = finrank (ZMod 2) ↥((polyLE σ k).map (annih C M).mkQ) := by
  rw [← errRank_eq_range C M k ((annih C M).mkQ ∘ₗ (polyLE σ k).subtype)
    (fun f => by simp [mem_annih]), LinearMap.range_comp, Submodule.range_subtype]
theorem iterate_ratio (c N : ℕ → ℕ) (K : ℕ) (hpos : ∀ j, 0 < N j)
    (step : ∀ j, j + 1 ≤ K → c (j + 1) * N j ≤ c j * N (j + 1)) (k : ℕ) :
    ∀ t, k + t ≤ K → c (k + t) * N k ≤ c k * N (k + t) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro hK
    have h1 := ih (by omega)
    have h2 := step (k + t) (by omega)
    have h3 : c (k + t + 1) * N k * N (k + t) ≤ c k * N (k + t + 1) * N (k + t) := by
      calc c (k + t + 1) * N k * N (k + t) = c (k + t + 1) * N (k + t) * N k := by ring
        _ ≤ c (k + t) * N (k + t + 1) * N k := Nat.mul_le_mul_right _ h2
        _ = c (k + t) * N k * N (k + t + 1) := by ring
        _ ≤ c k * N (k + t) * N (k + t + 1) := Nat.mul_le_mul_right _ h1
        _ = c k * N (k + t + 1) * N (k + t) := by ring
    exact Nat.le_of_mul_le_mul_right h3 (hpos (k + t))
theorem exists_affine [Fintype σ] (g : MvPolynomial σ (ZMod 2)) (hg : g.totalDegree ≤ 1) :
    ∃ (a : ZMod 2) (B : σ → ZMod 2), g = affine a B := by
  classical
  refine ⟨g.coeff 0, fun j => g.coeff (Finsupp.single j 1), ?_⟩
  ext d
  by_cases hd : 1 < d.degree
  · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hg hd),
      coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (affine_totalDegree_le _ _) hd)]
  · by_cases h0 : d = 0
    · subst h0
      simp [affine, coeff_C_mul]
    · obtain ⟨i, e, hde, he⟩ := exists_single_add d h0
      have he0 : e = 0 := by
        by_contra hne
        obtain ⟨_, _, -, he'⟩ := exists_single_add e hne
        omega
      subst he0
      rw [add_zero] at hde
      subst hde
      have h0' : ¬ ((0 : σ →₀ ℕ) = Finsupp.single i 1) := fun h => h0 h.symm
      simp [affine, coeff_C_mul, coeff_X, Finsupp.single_left_inj, h0']
end Glue
theorem monoRank_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
      ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
        errRank C (zMul P G) k' * numMono (Fintype.card σ) k
          ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k' := by
  intro σ _ C D a K P G hC hP hG hD
  have hmdeg : ∀ m ∈ zMul P G, m.totalDegree ≤ a + 1 := by
    rintro _ ⟨g, hg, rfl⟩
    show (P * g).totalDegree ≤ a + 1
    have h1 := totalDegree_mul P g
    have h2 := hG g hg
    omega
  have hX : ∀ p ∈ annih C (zMul P G), p.totalDegree < K → ∀ i : σ,
      X i * p ∈ annih C (zMul P G) := by
    intro p hp hdeg i
    rw [mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ annih C (zMul P G) := by
    intro d i hd
    rw [mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := totalDegree_monomial_one d
    have h3 := bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C (zMul P G) (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C (zMul P G) j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [errRank_eq_map, errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (annih C (zMul P G)) K hX hB j hj
  have hpos : ∀ j, 0 < numMono (Fintype.card σ) j := by
    intro j
    unfold numMono
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  intro k k' hkk' hk'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  exact iterate_ratio (fun j => errRank C (zMul P G) j) (fun j => numMono (Fintype.card σ) j)
    K hpos step k t hk'
theorem rankRetention_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
      (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
      b + k + 2 ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) k
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
  classical
  intro σ _ C D b k H G hC hH hG hD
  have haff : ∀ i : ↥G, ∃ (a : ZMod 2) (B : σ → ZMod 2),
      (i : MvPolynomial σ (ZMod 2)) = affine a B := fun i => exists_affine _ (hG i i.2)
  choose a B hab using haff
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  obtain ⟨c, hc⟩ := rank_retention_closure (ι := ↥G) (τ := ↥H) C (polyLE σ k) D k b
    (fun p hp hdeg j => hC.mulX j p hp (by omega))
    (fun p hp j => absorb hC _ _ (hC.bool j) (by
      have h1 := bool_totalDegree_le (σ := σ) j
      omega))
    (fun f hf => (mem_restrictTotalDegree σ k f).1 hf)
    a B hfun (fun α => hH α α.2) hD
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb (fun i => affine (a i) (B i)) c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • affine (a i) (B i) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    rw [← hab i]
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ k) hfun (affine (a i) (B i))))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ k) hfun (affine (a ⟨g, hg⟩) (B ⟨g, hg⟩)) f = 0 :=
        congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ k) hfun _ f).1 hz' ⟨h, hh⟩
      rw [← hab ⟨g, hg⟩] at h1
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ k) hfun (affine (a i) (B i)) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      rw [← hab i]
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ k) hfun (comb (fun i => affine (a i) (B i)) c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
end PEqualNP.Outside.L_pcx_377.H.DegSizeRank

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeGain
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.DegSizePlan
def Stmt41 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'
def Stmt35 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k
section LinearAlgebra
variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']
theorem finrank_eq_map_add_inf_ker (g : V →ₗ[ZMod 2] V') (S : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) S] :
    finrank (ZMod 2) S
      = finrank (ZMod 2) ↥(S.map g) + finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
  have h := (g ∘ₗ S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  have e : finrank (ZMod 2) ↥((LinearMap.ker g).comap S.subtype)
      = finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  omega
theorem finrank_add_le (f : V →ₗ[ZMod 2] V) (A W : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) W] :
    finrank (ZMod 2) A + finrank (ZMod 2) W
      ≤ finrank (ZMod 2) ↥(A ⊓ W.comap f) + finrank (ZMod 2) ↥(A.map f ⊔ W) := by
  have h1 := finrank_eq_map_add_inf_ker (W.mkQ ∘ₗ f) A
  have h2 := finrank_eq_map_add_inf_ker W.mkQ (A.map f ⊔ W)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [Submodule.ker_mkQ, inf_eq_right.mpr le_sup_right] at h2
  have h3 : finrank (ZMod 2) ↥(A.map (W.mkQ ∘ₗ f))
      ≤ finrank (ZMod 2) ↥((A.map f ⊔ W).map W.mkQ) := by
    rw [Submodule.map_comp]
    exact Submodule.finrank_mono (Submodule.map_mono le_sup_left)
  omega
theorem codim_iInf {ι : Type} (E : Submodule (ZMod 2) V) [FiniteDimensional (ZMod 2) E]
    (W : ι → Submodule (ZMod 2) V) (hW : ∀ ν, W ν ≤ E) (S : Finset ι) :
    finrank (ZMod 2) E
      ≤ finrank (ZMod 2) ↥(E ⊓ ⨅ ν ∈ S, W ν)
        + ∑ ν ∈ S, (finrank (ZMod 2) E - finrank (ZMod 2) (W ν)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (⨅ ν ∈ (∅ : Finset ι), W ν) = ⊤ := by simp
    rw [h0, inf_top_eq]
    exact Nat.le_add_right _ _
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha, inf_left_comm]
    have : FiniteDimensional (ZMod 2) ↥(W a) := Submodule.finiteDimensional_of_le (hW a)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W a) (E ⊓ ⨅ ν ∈ s, W ν)
    have h2 : finrank (ZMod 2) ↥(W a ⊔ (E ⊓ ⨅ ν ∈ s, W ν)) ≤ finrank (ZMod 2) E :=
      Submodule.finrank_mono (sup_le (hW a) inf_le_left)
    have h3 : finrank (ZMod 2) (W a) ≤ finrank (ZMod 2) E := Submodule.finrank_mono (hW a)
    omega
end LinearAlgebra
section Poly
variable {σ : Type}
theorem mem_polyLE {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ polyLE σ k ↔ f.totalDegree ≤ k := by
  simp [polyLE, mem_restrictTotalDegree]
theorem deg_mul_le {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)
theorem deg_one_add_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (1 + q).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (q * q + q).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans (max_le (deg_mul_le hq hq) (by omega))
theorem deg_le_one_of_mem_span {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 :=
  mem_polyLE.mp (Submodule.span_le.mpr (fun g hg => mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, 1 :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le (h j))
    _ = t := by simp
theorem eq_zero_of_sum_eq_zero (u : σ →₀ ℕ) (h : (u.sum fun _ e => e) = 0) : u = 0 := by
  rw [Finsupp.sum] at h
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hi
  exact hi ((Finset.sum_eq_zero_iff.mp h) i (Finsupp.mem_support_iff.mpr hi))
theorem exists_single_add (u : σ →₀ ℕ) (h : u ≠ 0) :
    ∃ (v : σ) (u' : σ →₀ ℕ), u = Finsupp.single v 1 + u' ∧
      (u.sum fun _ e => e) = 1 + (u'.sum fun _ e => e) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, u v ≠ 0 := by
    by_contra hcon
    refine h (Finsupp.ext (fun a => ?_))
    by_contra ha
    exact hcon ⟨a, ha⟩
  have hu : u = Finsupp.single v 1 + (u - Finsupp.single v 1) := by
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with hvi
    · subst hvi; omega
    · omega
  refine ⟨v, u - Finsupp.single v 1, hu, ?_⟩
  conv_lhs => rw [hu]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem absorb_monomial (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ) (c : ZMod 2) (f : MvPolynomial σ (ZMod 2)),
      (u.sum fun _ e => e) = n → f ∈ C → n + f.totalDegree ≤ D → monomial u c * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u c f hu hf _
    have h0 : u = 0 := eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : monomial (0 : σ →₀ ℕ) c = MvPolynomial.C c := rfl
    rw [hm, C_mul']
    exact C.smul_mem c hf
  | succ n ih =>
    intro u c f hu hf hd
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
    rw [monomial_single_add, pow_one, mul_assoc]
    have hm := ih u' c f (by omega) hf (by omega)
    refine hC.mulX v _ hm ?_
    have h1 := totalDegree_mul (monomial u' c) f
    have h2 : (monomial u' c).totalDegree ≤ (u'.sum fun _ e => e) := totalDegree_monomial_le u' c
    omega
theorem absorb (hC : DegClosed C D) {f g : MvPolynomial σ (ZMod 2)} (hf : f ∈ C)
    (h : g.totalDegree + f.totalDegree ≤ D) : g * f ∈ C := by
  have e : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    rw [← Finset.sum_mul, support_sum_monomial_coeff]
  rw [e]
  refine C.sum_mem fun u hu => ?_
  have h1 : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact absorb_monomial hC _ u _ f rfl hf (by omega)
theorem idem_monomial (hC : DegClosed C D) (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ 1) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · by_cases h0 : u = 0
    · subst h0
      have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [hm, one_mul, CharTwo.add_self_eq_zero]
      exact C.zero_mem
    · obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
      have hu' : u' = 0 := eq_zero_of_sum_eq_zero u' (by omega)
      subst hu'
      rw [add_zero]
      exact hC.bool v
theorem affine_idem (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ 1) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial hC a (c a) (hs a (Finset.mem_insert_self a s)))
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errKer_le (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errKer C M k ≤ polyLE σ k := by
  unfold errKer
  exact inf_le_left
instance errKer_finite [Fintype σ] (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    FiniteDimensional (ZMod 2) ↥(errKer C M k) :=
  Submodule.finiteDimensional_of_le (errKer_le M k)
theorem mem_errKer_zMul {P : MvPolynomial σ (ZMod 2)} {G : Set (MvPolynomial σ (ZMod 2))}
    {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C (zMul P G) k ↔ f.totalDegree ≤ k ∧ ∀ g ∈ G, P * g * f ∈ C := by
  rw [mem_errKer]
  simp [zMul]
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : ∑ j ∈ Finset.range 1, n.choose j ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have h1 : ∑ j ∈ Finset.range 1, n.choose j = 1 := by simp
  omega
theorem numMono_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : numMono n k ≤ numMono n k' := by
  unfold numMono
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
theorem errRank_one_le [Fintype σ] (hC : DegClosed C D) {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {K : ℕ} (hD : K + 1 ≤ D) :
    errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := mem_polyLE.mp hf.2
    rw [mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem gain (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := h35 σ C D a (K - 1) {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - 1) ≤ 2 * errRank C {P * q} (K - 1) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ 1 := deg_le_one_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := affine_idem hC q hq1
  have hidem2 := deg_idem_le hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - 1) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - 1) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := deg_mul_le hP hfd
      exact absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - 1)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [mem_errKer_zMul]
      have hd0 := deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact absorb hC hidem (by omega)
    · intro f hf
      rw [mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact absorb hC (hf.2 g hg) (by omega)
  have key := finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - 1))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - 1)) ≤ finrank (ZMod 2) (polyLE σ (K - 1)) :=
    Submodule.finrank_mono (errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith {c c' c1 h n K t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - 1) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta n K) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta n K) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast numMono_pos n K
  have hN1 : (numMono n (K - 1) : ℝ) ≤ numMono n K := by
    exact_mod_cast numMono_mono n (Nat.sub_le K 1)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - 1) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta n K := by
    have hle : eta n K ≤ 1 := by
      unfold eta
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta n K ≤ c1 / 2 := by
    unfold eta
    have e1 : (c : ℝ) * (numMono n (K - 1) / (2 * numMono n K))
        = (c * numMono n (K - 1)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta n K) := by linarith
    _ ≤ (h * (1 - eta n K) ^ t) * (1 - eta n K) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta n K) ^ (t + 1) := by ring
theorem greedy (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le hC hG' (by omega)
  | succ t ih =>
    intro hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t :=
      deg_prod_le qs (fun j => deg_le_one_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain h35 σ C D t K _ G hC hP hG hK (by omega)
    have h41' := h41 σ C D t K _ (↑G) hC hP hG' (by omega) (K - 1) K (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith hgain h41' hb
theorem common (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy h41 h35 σ C D K t (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    codim_iInf (polyLE σ K) (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩, fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
end PEqualNP.Outside.L_pcx_377.H.DegSizeGain

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeGainK
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
noncomputable def eta_k (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
theorem eta_k_one (n K : ℕ) : eta_k n K 1 = eta n K := rfl
section Poly
variable {σ : Type}
theorem deg_one_add_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (1 + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (q * q + q).totalDegree ≤ 2 * k :=
  (totalDegree_add _ _).trans (max_le ((DegSizeGain.deg_mul_le hq hq).trans (by omega))
    (by omega))
theorem deg_le_of_mem_span {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k :=
  DegSizeGain.mem_polyLE.mp
    (Submodule.span_le.mpr (fun g hg => DegSizeGain.mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le_k {k t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, k :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le_k (h j))
    _ = t * k := by simp
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem idem_monomial_one (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ), (u.sum fun _ e => e) = n → 2 * n ≤ D →
      monomial u (1 : ZMod 2) * monomial u 1 + monomial u 1 ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    have h0 : u = 0 := DegSizeGain.eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [hm, one_mul, CharTwo.add_self_eq_zero]
    exact C.zero_mem
  | succ n ih =>
    intro u hu hD
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := DegSizeGain.exists_single_add u h0
    have hm' := ih u' (by omega) (by omega)
    have hmd : (monomial u' (1 : ZMod 2)).totalDegree ≤ n := by
      have h2 : (monomial u' (1 : ZMod 2)).totalDegree ≤ (u'.sum fun _ e => e) :=
        totalDegree_monomial_le u' 1
      omega
    have e0 : monomial (Finsupp.single v 1 + u') (1 : ZMod 2) = X v * monomial u' 1 := by
      rw [monomial_single_add, pow_one]
    rw [e0]
    generalize monomial u' (1 : ZMod 2) = m at hm' hmd ⊢
    have e : X v * m * (X v * m) + X v * m
        = (m * m) * (X v * X v + X v) + X v * (m * m + m) := by
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) *
        CharTwo.add_self_eq_zero (X v * (m * m))
    rw [e]
    refine C.add_mem ?_ (hC.mulX v _ hm' ?_)
    · refine DegSizeGain.absorb hC (hC.bool v) ?_
      have h1 := DegSizeGain.deg_mul_le hmd hmd
      have h2 := DegSizeRank.bool_totalDegree_le v
      omega
    · have h1 := deg_idem_le_k hmd
      omega
theorem idem_monomial_k (hC : DegClosed C D) {k : ℕ} (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ k) (hD : 2 * k ≤ D) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · exact idem_monomial_one hC _ u rfl (by omega)
theorem idem_k (hC : DegClosed C D) {k : ℕ} (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ k) (hD : 2 * k ≤ D) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ k) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial_k hC a (c a) (hs a (Finset.mem_insert_self a s)) hD)
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errRank_one_le_k [Fintype σ] (hC : DegClosed C D) {k : ℕ}
    {G : Set (MvPolynomial σ (ZMod 2))} (hG : ∀ g ∈ G, g.totalDegree ≤ k) {K : ℕ}
    (hD : K + k ≤ D) : errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := DegSizeGain.mem_polyLE.mp hf.2
    rw [DegSizeGain.mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact DegSizeGain.absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem monoRank_mul :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b K : ℕ)
      (M : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ m ∈ M, m.totalDegree ≤ b) → b + K ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C M l' * numMono (Fintype.card σ) l
          ≤ errRank C M l * numMono (Fintype.card σ) l' := by
  intro σ _ C D b K M hC hmdeg hD
  have hX : ∀ p ∈ DegSizeRank.annih C M, p.totalDegree < K → ∀ i : σ,
      X i * p ∈ DegSizeRank.annih C M := by
    intro p hp hdeg i
    rw [DegSizeRank.mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ DegSizeRank.annih C M := by
    intro d i hd
    rw [DegSizeRank.mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine DegSizeRank.absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := DegSizeRank.totalDegree_monomial_one d
    have h3 := DegSizeRank.bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C M (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C M j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [DegSizeRank.errRank_eq_map, DegSizeRank.errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (DegSizeRank.annih C M) K hX hB j hj
  intro l l' hll' hl'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hll'
  exact DegSizeRank.iterate_ratio (fun j => errRank C M j)
    (fun j => numMono (Fintype.card σ) j) K (fun j => DegSizeGain.numMono_pos _ j) step l t hl'
theorem monoRank_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → a + K + k ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C (zMul P G) l' * numMono (Fintype.card σ) l
          ≤ errRank C (zMul P G) l * numMono (Fintype.card σ) l' := by
  intro σ _ C D a K k P G hC hP hG hD
  refine monoRank_mul σ C D (a + k) K (zMul P G) hC ?_ (by omega)
  rintro _ ⟨g, hg, rfl⟩
  exact DegSizeGain.deg_mul_le hP (hG g hg)
theorem rankRetention_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D b l k : ℕ) (H : Set (MvPolynomial σ (ZMod 2)))
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ k) →
      b + l + 2 * k ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) l
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
  classical
  intro σ _ C D b l k H G hC hH hG hD
  let gfun : ↥G → MvPolynomial σ (ZMod 2) := fun i => i
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  have hcd : ∀ c : ↥G → ZMod 2, (comb gfun c).totalDegree ≤ k := by
    intro c
    refine DegSizeGain.mem_polyLE.mp ?_
    unfold comb
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (DegSizeGain.mem_polyLE.mpr (hG i i.2))
  have hmul : ∀ (c c' : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * comb gfun c * hfun α ∈ C → f * comb gfun c * comb gfun c' * hfun α ∈ C := by
    intro c c' α f hf hmem
    have e : f * comb gfun c * comb gfun c' * hfun α
        = comb gfun c' * (f * comb gfun c * hfun α) := by ring
    rw [e]
    refine DegSizeGain.absorb hC hmem ?_
    have h1 : (f * comb gfun c * hfun α).totalDegree ≤ l + k + b := DegSizeGain.deg_mul_le
      (DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hcd c)) (hH α α.2)
    have h2 := hcd c'
    omega
  have hidem : ∀ (c : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * (comb gfun c * comb gfun c + comb gfun c) * hfun α ∈ C := by
    intro c α f hf
    have e : f * (comb gfun c * comb gfun c + comb gfun c) * hfun α
        = (f * hfun α) * (comb gfun c * comb gfun c + comb gfun c) := by ring
    rw [e]
    refine DegSizeGain.absorb hC (idem_k hC _ (hcd c) (by omega)) ?_
    have h1 : (f * hfun α).totalDegree ≤ l + b :=
      DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hH α α.2)
    have h2 := deg_idem_le_k (hcd c)
    omega
  obtain ⟨c, hc⟩ := rank_retention_mul (ι := ↥G) (τ := ↥H) C (polyLE σ l) gfun hfun
    hmul hidem
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb gfun c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • (i : MvPolynomial σ (ZMod 2)) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ l) hfun (gfun i)))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ l) hfun (gfun ⟨g, hg⟩) f = 0 := congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ l) hfun _ f).1 hz' ⟨h, hh⟩
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ l) hfun (gfun i) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * gfun i * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ l) hfun (comb gfun c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
theorem gain_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K →
      a + K + 2 * k ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - k)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K k P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := rankRetention_used_k σ C D a (K - k) k {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - k) ≤ 2 * errRank C {P * q} (K - k) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ k := deg_le_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := idem_k hC q hq1 (by omega)
  have hidem2 := deg_idem_le_k hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - k) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - k) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [DegSizeGain.mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := DegSizeGain.deg_mul_le hP hfd
      exact DegSizeGain.absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - k)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [DegSizeGain.mem_errKer_zMul]
      have hd0 := DegSizeGain.deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact DegSizeGain.absorb hC hidem (by omega)
    · intro f hf
      rw [DegSizeGain.mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le_k hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact DegSizeGain.absorb hC (hf.2 g hg) (by omega)
  have key := DegSizeGain.finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - k))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - k)) ≤ finrank (ZMod 2) (polyLE σ (K - k)) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith_k {c c' c1 h n K k t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - k) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta_k n K k) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta_k n K k) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - k) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta_k n K k := by
    have hle : eta_k n K k ≤ 1 := by
      unfold eta_k
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta_k n K k ≤ c1 / 2 := by
    unfold eta_k
    have e1 : (c : ℝ) * (numMono n (K - k) / (2 * numMono n K))
        = (c * numMono n (K - k)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta_k n K k) := by linarith
    _ ≤ (h * (1 - eta_k n K k) ^ t) * (1 - eta_k n K k) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta_k n K k) ^ (t + 1) := by ring
theorem greedy_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t := by
  intro σ _ C D K t k G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le_k hC hG' (by omega)
  | succ t ih =>
    intro hD
    have et : (t + 1) * k = t * k + k := by ring
    rw [et] at hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
      deg_prod_le_k qs (fun j => deg_le_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain_k σ C D (t * k) K k _ G hC hP hG hK (by omega)
    have h41' := monoRank_used_k σ C D (t * k) K k _ (↑G) hC hP hG' (by omega) (K - k) K
      (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith_k hgain h41' hb
theorem common_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      (S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t k ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy_k σ C D K t k (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact DegSizeGain.mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    DegSizeGain.codim_iInf (polyLE σ K)
      (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => DegSizeGain.errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, DegSizeGain.mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩,
    fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (DegSizeGain.mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
theorem stmt41_of_k : DegSizeGain.Stmt41 := by
  intro σ _ C D a K P G hC hP hG hD
  exact monoRank_used_k σ C D a K 1 P G hC hP hG hD
theorem stmt35_of_k : DegSizeGain.Stmt35 := by
  intro σ _ C D b l H G hC hH hG hD
  exact rankRetention_used_k σ C D b l 1 H G hC hH hG (by omega)
theorem gain_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  exact gain_k σ C D a K 1 P G hC hP hG hK (by omega)
theorem greedy_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK hD
  exact greedy_k σ C D K t 1 G hC hG hK (by omega)
theorem common_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  exact common_k σ C D K t 1 ι S G hC h1 hG hK (by omega) hlt
end PEqualNP.Outside.L_pcx_377.H.DegSizeGainK

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeArith
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
section Completeness
variable {V : Type}
noncomputable def fac (a : V → Bool) (v : V) : MvPolynomial V (ZMod 2) :=
  if a v = true then X v else 1 + X v
theorem totalDegree_fac_le (a : V → Bool) (v : V) : (fac a v).totalDegree ≤ 1 := by
  unfold fac
  split_ifs
  · rw [totalDegree_X]
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp
theorem totalDegree_prod_fac_le (a : V → Bool) (S : Finset V) :
    (∏ v ∈ S, fac a v).totalDegree ≤ S.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ v ∈ S, (fac a v).totalDegree ≤ ∑ _v ∈ S, 1 :=
        Finset.sum_le_sum fun v _ => totalDegree_fac_le a v
    _ = S.card := by simp
theorem eval_fac (a : V → Bool) (x : V → ZMod 2) (v : V) :
    eval x (fac a v) = if (x v = 1 ↔ a v = true) then 1 else 0 := by
  unfold fac
  have hx : x v = 0 ∨ x v = 1 := by
    generalize x v = c
    revert c
    decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hx with h | h <;> cases a v <;> simp [h, h11]
theorem complete_deg :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → ¬ Satisfiable F → w ≤ D → Fintype.card V ≤ D →
      PCRefutable (cnfSystem F) D := by
  classical
  intro V _ _ F w D hw hunsat hwD hVD
  have hfals : ∀ a : V → Bool, ∃ A ∈ F, ¬ ClauseSat a A := by
    intro a
    by_contra hb
    exact hunsat ⟨a, fun A hA => by_contra fun hn => hb ⟨A, hA, hn⟩⟩
  have hind : ∀ a : V → Bool, PCDerivable (cnfSystem F) D (∏ v, fac a v) := by
    intro a
    obtain ⟨A, hAF, hA⟩ := hfals a
    have hne : ∀ l ∈ A, a l.1 = !l.2 := by
      intro l hl
      have h0 : ¬ a l.1 = l.2 := fun h => hA ⟨l, hl, h⟩
      revert h0
      cases a l.1 <;> cases l.2 <;> simp
    have hinj : Set.InjOn (fun l : Literal V => l.1) (↑A : Set (Literal V)) := by
      intro l hl l' hl' h
      have h' : l.1 = l'.1 := h
      have h1 := hne l hl
      have h2 := hne l' hl'
      rw [h'] at h1
      have h3 : (!l.2) = !l'.2 := h1.symm.trans h2
      have h4 : l.2 = l'.2 := by simpa using h3
      exact Prod.ext h' h4
    set S : Finset V := A.image (fun l => l.1) with hS
    have hcl : clausePoly A = ∏ v ∈ S, fac a v := by
      rw [hS, Finset.prod_image hinj]
      unfold clausePoly
      refine Finset.prod_congr rfl fun l hl => ?_
      have h1 := hne l hl
      unfold fac
      rw [h1]
      cases l.2 <;> simp
    have hsplit : ∏ v, fac a v = (∏ v ∈ Sᶜ, fac a v) * clausePoly A := by
      rw [hcl, Finset.prod_compl_mul_prod]
    have hdegc : (clausePoly A).totalDegree ≤ S.card := by
      rw [hcl]
      exact totalDegree_prod_fac_le a S
    have hScard : S.card ≤ w := Finset.card_image_le.trans (hw A hAF)
    have hax : PCDerivable (cnfSystem F) D (clausePoly A) :=
      .ax (Or.inr ⟨A, hAF, rfl⟩) (hdegc.trans (hScard.trans hwD))
    rw [hsplit]
    refine pcDerivable_mono (pcDerivable_mul_left hax (∏ v ∈ Sᶜ, fac a v)) ?_ subset_rfl
    refine max_le le_rfl ?_
    have h1 := totalDegree_prod_fac_le a Sᶜ
    have h2 : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    omega
  set p : MvPolynomial V (ZMod 2) := ∑ a : V → Bool, ∏ v, fac a v with hp
  have hpder : PCDerivable (cnfSystem F) D p := pcDerivable_sum _ _ fun a _ => hind a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hvan : ∀ x : V → ZMod 2, eval x (1 + p) = 0 := by
    intro x
    have hx : eval x p = 1 := by
      rw [hp, map_sum]
      simp only [map_prod, eval_fac, Finset.prod_boole]
      rw [Finset.sum_eq_single (fun v => decide (x v = 1))]
      · simp
      · intro b _ hb
        split_ifs with h
        · exfalso
          apply hb
          funext v
          have := h v (Finset.mem_univ v)
          cases hbv : b v <;> simp_all
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [map_add, map_one, hx, h11]
  have hdeg : (1 + p).totalDegree ≤ D := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]
      exact Nat.zero_le _
    · rw [hp]
      refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_prod_fac_le a Finset.univ).trans ?_
      rwa [Finset.card_univ]
  have h1 := BoolVanish.vanish_derivable V (cnfSystem F) D (1 + p)
    (fun v => Or.inl ⟨v, rfl⟩) hdeg hvan
  have h2 := PCDerivable.add h1 hpder
  have e : 1 + p + p = 1 := by
    rw [add_assoc, ← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  rw [e] at h2
  exact h2
end Completeness
section Binomial
theorem numMono_succ (n k : ℕ) : numMono n (k + 1) = numMono n k + n.choose (k + 1) := by
  unfold numMono
  rw [Finset.sum_range_succ]
theorem choose_le_numMono (n k : ℕ) : n.choose k ≤ numMono n k := by
  unfold numMono
  exact Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
    (Finset.self_mem_range_succ k)
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : n.choose 0 ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos k))
  rw [Nat.choose_zero_right] at h
  exact h
theorem numMono_ratio (n k : ℕ) (hk : k ≤ n) :
    (k + 1) * numMono n (k + 1) ≤ (n + 1) * numMono n k := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 := choose_le_numMono n k
  have h3 : n.choose k * (n - k) ≤ numMono n k * (n - k) := Nat.mul_le_mul_right _ h2
  have h4 : numMono n k * (k + 1) + numMono n k * (n - k) = numMono n k * (n + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [numMono_succ]
  calc (k + 1) * (numMono n k + n.choose (k + 1))
      = numMono n k * (k + 1) + n.choose (k + 1) * (k + 1) := by ring
    _ ≤ numMono n k * (k + 1) + numMono n k * (n - k) := by rw [h1]; exact Nat.add_le_add_left h3 _
    _ = (n + 1) * numMono n k := by rw [h4]; ring
end Binomial
end PEqualNP.Outside.L_pcx_377.H.DegSizeArith

namespace PEqualNP.Outside.L_pcx_377.H.LinKPlan
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
section Vanish
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem mem_of_boolDerivable (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hp : PCDerivable (BoolVanish.boolAxioms σ) D p) : p ∈ C := by
  induction hp with
  | ax hp _ =>
    obtain ⟨v, rfl⟩ := hp
    exact hC.bool v
  | zero => exact C.zero_mem
  | add _ _ ih1 ih2 => exact C.add_mem ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases h0 : p = 0
    · subst h0
      simp
    · refine hC.mulX j p ih ?_
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) h0, totalDegree_X] at hdeg
      omega
theorem vanish_mem (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hd : p.totalDegree ≤ D) (hv : ∀ x : σ → ZMod 2, eval x p = 0) : p ∈ C :=
  mem_of_boolDerivable hC
    (BoolVanish.vanish_derivable σ (BoolVanish.boolAxioms σ) D p (fun v => ⟨v, rfl⟩) hd hv)
theorem idem_mul (hC : DegClosed C D) (g h : MvPolynomial σ (ZMod 2)) {b e : ℕ}
    (hh : h.totalDegree ≤ b) (hg : g.totalDegree ≤ e) (hB : b + 2 * e ≤ D) :
    h * (g * g + g) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 : (g * g + g).totalDegree ≤ e + e :=
      (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hg hg) (by omega))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have : ∀ c : ZMod 2, c * c + c = 0 := by decide
    rw [this, mul_zero]
end Vanish
noncomputable def termPoly {V : Type} (T : LinTerm V) : MvPolynomial V (ZMod 2) :=
  ∏ e ∈ T, eqPoly e
section Terms
variable {V : Type}
theorem termPoly_empty : termPoly (∅ : LinTerm V) = 1 := by
  simp [termPoly]
theorem termPoly_singleton (q : LinEq V) : termPoly ({q} : LinTerm V) = eqPoly q := by
  simp [termPoly]
theorem totalDegree_termPoly_le (T : LinTerm V) : (termPoly T).totalDegree ≤ T.card := by
  unfold termPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ e ∈ T, (eqPoly e).totalDegree ≤ ∑ _e ∈ T, 1 :=
        Finset.sum_le_sum fun e _ => totalDegree_eqPoly_le e
    _ = T.card := by simp
theorem eval_eqPoly (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = ∑ v ∈ q.1, x v + (if q.2 = true then 0 else 1) := by
  unfold eqPoly
  rw [map_add, map_sum, eval_C]
  simp only [eval_X]
theorem eval_eqPoly_eq_one_iff (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = 1 ↔ LinEqSat (fun v => decide (x v = 1)) q := by
  rw [eval_eqPoly, linEqSat_iff_sum]
theorem eval_eqPoly_neg (x : V → ZMod 2) (e : LinEq V) :
    eval x (eqPoly (negLinEq e)) = eval x (eqPoly e) + 1 := by
  rw [eval_eqPoly, eval_eqPoly]
  rcases e with ⟨f, b⟩
  show ∑ v ∈ f, x v + (if (!b) = true then 0 else 1)
    = ∑ v ∈ f, x v + (if b = true then 0 else 1) + 1
  generalize ∑ v ∈ f, x v = s
  cases b
  · revert s
    decide
  · revert s
    decide
theorem eval_termPoly_of_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 1 := by
  unfold termPoly
  rw [map_prod]
  exact Finset.prod_eq_one fun e he => (eval_eqPoly_eq_one_iff x e).mpr (h e he)
theorem eval_termPoly_of_not_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : ¬ LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 0 := by
  obtain ⟨e, he, hne⟩ : ∃ e ∈ T, ¬ LinEqSat (fun v => decide (x v = 1)) e := by
    by_contra hcon
    exact h fun e he => by_contra fun hn => hcon ⟨e, he, hn⟩
  unfold termPoly
  rw [map_prod]
  refine Finset.prod_eq_zero he ?_
  rcases zmod2_cases (eval x (eqPoly e)) with h0 | h1
  · exact h0
  · exact absurd ((eval_eqPoly_eq_one_iff x e).mp h1) hne
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_term_mul (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T.card + S.card ≤ D) :
    h * (termPoly T + termPoly T * termPoly S) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have hT := totalDegree_termPoly_le T
    have hS := totalDegree_termPoly_le S
    have h1 : (termPoly T + termPoly T * termPoly S).totalDegree ≤ T.card + S.card :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hS))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [eval_termPoly_of_sat x T hT, eval_termPoly_of_sat x S (himp _ hT)]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem weak_term (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S) (hB : T.card + S.card ≤ D) :
    termPoly T + termPoly T * termPoly S ∈ C := by
  have h := weak_term_mul hC T S himp 1 (b := 0) (by simp) (by omega)
  rwa [one_mul] at h
theorem unsat_term_mul (hC : DegClosed C D) (T : LinTerm V)
    (hT : ∀ a : V → Bool, ¬ LinTermSat a T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card ≤ D) :
    h * termPoly T ∈ C := by
  refine vanish_mem hC ((totalDegree_mul_le' hh (totalDegree_termPoly_le T)).trans hB) ?_
  intro x
  rw [map_mul, eval_termPoly_of_not_sat x T (hT _), mul_zero]
theorem term_neg_mul (hC : DegClosed C D) (T : LinTerm V) (e : LinEq V) (he : e ∈ T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card + 1 ≤ D) :
    h * (termPoly T * eqPoly (negLinEq e)) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_mul_le' (totalDegree_termPoly_le T)
      (totalDegree_eqPoly_le (negLinEq e))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_mul, eval_eqPoly_neg]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [(eval_eqPoly_eq_one_iff x e).mpr (hT e he)]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, mul_zero, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem term_union_mul [DecidableEq V] (hC : DegClosed C D) (T₁ T₂ : LinTerm V)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T₁.card + T₂.card ≤ D) :
    h * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_termPoly_le T₁
    have h2 := totalDegree_termPoly_le T₂
    have h3 := (totalDegree_termPoly_le (T₁ ∪ T₂)).trans (Finset.card_union_le T₁ T₂)
    have h4 : (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂).totalDegree
        ≤ T₁.card + T₂.card :=
      (totalDegree_add _ _).trans (max_le h3 (totalDegree_mul_le' h1 h2))
    exact (totalDegree_mul_le' hh h4).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have h11 : (1 : ZMod 2) + 1 * 1 = 0 := by decide
    by_cases h1 : LinTermSat (fun v => decide (x v = 1)) T₁
    · by_cases h2 : LinTermSat (fun v => decide (x v = 1)) T₂
      · have hu : LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := by
          intro q hq
          rcases Finset.mem_union.mp hq with hq | hq
          · exact h1 q hq
          · exact h2 q hq
        rw [eval_termPoly_of_sat x _ hu, eval_termPoly_of_sat x _ h1,
          eval_termPoly_of_sat x _ h2, h11, mul_zero]
      · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
          h2 fun q hq => hu q (Finset.mem_union_right _ hq)
        rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h2]
        simp
    · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
        h1 fun q hq => hu q (Finset.mem_union_left _ hq)
      rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h1]
      simp
end Terms
section Alt
theorem span_image_sum {ι M : Type} [AddCommGroup M] [Module (ZMod 2) M] (w : ι → M)
    (s : Finset ι) {y : M} (hy : y ∈ Submodule.span (ZMod 2) (w '' (↑s : Set ι))) :
    ∃ I : Finset ι, I ⊆ s ∧ y = ∑ i ∈ I, w i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hy
  obtain ⟨lc, hlc, rfl⟩ := hy
  refine ⟨lc.support, fun d hd => Finset.mem_coe.mp ((Finsupp.mem_supported _ _).mp hlc hd), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h1 : lc d = 1 := by
    generalize lc d = x at h0
    revert x
    decide
  rw [h1, one_smul]
variable {V : Type} [Fintype V] [DecidableEq V]
theorem term_alt (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ ∃ I : Finset (LinEq V), I ⊆ T ∧
      ∑ e ∈ I, (eqPoly e + 1) + ∑ d ∈ J, eqPoly d = 1 := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
        ∪ (eqVec '' (↑Q : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
          ∪ (eqVec '' (↑Q : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
            ∪ (eqVec '' (↑Q : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hT : LinTermSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) T := by
      intro e he
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Or.inl ⟨e, Finset.mem_coe.mpr he, rfl⟩))
      rw [map_add, h1] at this
      generalize φ (eqVec e) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hT
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Or.inr ⟨d, Finset.mem_coe.mpr hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.span_union, Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨I, hI, rfl⟩ := span_image_sum (fun e : LinEq V => eqVec e + (0, 1)) T hy
  obtain ⟨J, hJ, rfl⟩ := span_image_sum eqVec Q hz
  refine ⟨J, hJ, I, hI, ?_⟩
  have hP := congrArg affPoly hyz
  simp only [map_add, map_sum, affPoly_eqVec, affPoly_one] at hP
  exact hP
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_disj_mul (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, I, hI, hid⟩ := term_alt T Q himp
  refine ⟨J, hJ, fun h b hh hB => vanish_mem hC ?_ ?_⟩
  · have hT := totalDegree_termPoly_le T
    have hs : (∑ d ∈ J, eqPoly d).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun d _ => totalDegree_eqPoly_le d
    have h1 : (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d).totalDegree ≤ T.card + 1 :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hs))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · have h0 : eval x (∑ e ∈ I, (eqPoly e + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [map_add, map_one, (eval_eqPoly_eq_one_iff x e).mpr (hT e (hI he))]
        decide
      have h1 : eval x (∑ d ∈ J, eqPoly d) = 1 := by
        have := congrArg (eval x) hid
        rw [map_add, h0, zero_add, map_one] at this
        exact this
      rw [eval_termPoly_of_sat x T hT, h1]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem weak_disj (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) (hB : T.card + 1 ≤ D) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ termPoly T + termPoly T * ∑ d ∈ J, eqPoly d ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T Q himp
  refine ⟨J, hJ, ?_⟩
  have h := hmul 1 0 (by simp) (by omega)
  rwa [one_mul] at h
theorem weak_disj_line (hC : DegClosed C D) (T : LinTerm V) (M : LinKLine V)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q) :
    ∃ J : Finset (LinEq V), (∀ d ∈ J, ({d} : LinTerm V) ∈ M) ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T
    ((M.biUnion id).filter (fun q => ({q} : LinTerm V) ∈ M))
    (fun a ha => by
      obtain ⟨q, hq, hs⟩ := himp a ha
      exact ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩, hq⟩, hs⟩)
  exact ⟨J, fun d hd => (Finset.mem_filter.mp (hJ hd)).2, hmul⟩
end Alt
noncomputable def lineInputs {V : Type} (L : LinKLine V) : Set (MvPolynomial V (ZMod 2)) :=
  (fun T => termPoly T) '' (↑L : Set (LinTerm V))
noncomputable def etaK (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
theorem etaK_one (n K : ℕ) : etaK n K 1 = eta n K := rfl
end PEqualNP.Outside.L_pcx_377.H.LinKPlan

namespace PEqualNP.Outside.L_pcx_377.H.Helpers.LinKOne
open PEqualNP.ProofComplexity
theorem weakening_sound {V : Type} {a : V → Bool} {L M : LinKLine V} (h : IsLinKWeakening L M)
    (hs : LinKLineSat a L) : LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  rcases h T hT with ⟨S, hS, himp⟩ | hb
  · exact ⟨S, hS, himp a hTs⟩
  · obtain ⟨q, hq, hqs⟩ := hb a hTs
    refine ⟨{q}, hq, fun q' hq' => ?_⟩
    rw [Finset.mem_singleton.mp hq']
    exact hqs
end PEqualNP.Outside.L_pcx_377.H.Helpers.LinKOne

namespace PEqualNP.Outside.L_pcx_377.H.DegSizeArithK
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan
open PEqualNP.Outside.L_pcx_377.H.DegSizeGainK (eta_k)
theorem numMono_ratio_iter (n j k : ℕ) (h : j + k ≤ n + 1) :
    (j + 1) ^ k * numMono n (j + k) ≤ (n + 1) ^ k * numMono n j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hr := DegSizeArith.numMono_ratio n (j + k) (by omega)
    calc (j + 1) ^ (k + 1) * numMono n (j + (k + 1))
        = (j + 1) ^ k * ((j + 1) * numMono n (j + k + 1)) := by
          rw [show j + (k + 1) = j + k + 1 from rfl]; ring
      _ ≤ (j + 1) ^ k * ((j + k + 1) * numMono n (j + k + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ (j + 1) ^ k * ((n + 1) * numMono n (j + k)) := Nat.mul_le_mul_left _ hr
      _ = (n + 1) * ((j + 1) ^ k * numMono n (j + k)) := by ring
      _ ≤ (n + 1) * ((n + 1) ^ k * numMono n j) := Nat.mul_le_mul_left _ ih'
      _ = (n + 1) ^ (k + 1) * numMono n j := by ring
theorem eta_k_nonneg (n K k : ℕ) : 0 ≤ eta_k n K k := by
  unfold eta_k
  positivity
theorem eta_k_le_half (n K k : ℕ) : eta_k n K k ≤ 1 / 2 := by
  unfold eta_k
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeArith.numMono_pos n K
  have hle : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith
theorem eta_k_le_one (n K k : ℕ) : eta_k n K k ≤ 1 :=
  (eta_k_le_half n K k).trans (by norm_num)
theorem one_sub_eta_k_nonneg (n K k : ℕ) : 0 ≤ 1 - eta_k n K k := by
  have := eta_k_le_one n K k
  linarith
theorem eta_k_ge (n K k : ℕ) (hk : k ≤ K) (hK : K ≤ n + 1) :
    (1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k ≤ eta_k n K k := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + k := ⟨K - k, by omega⟩
  have hnat := numMono_ratio_iter n j k hK
  unfold eta_k
  rw [Nat.add_sub_cancel]
  have hN : (0 : ℝ) < numMono n (j + k) := by
    exact_mod_cast DegSizeArith.numMono_pos n (j + k)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : ((j : ℝ) + 1) ^ k * (numMono n (j + k) : ℝ)
      ≤ ((n : ℝ) + 1) ^ k * (numMono n j : ℝ) := by exact_mod_cast hnat
  push_cast
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hn k) (by linarith)]
  nlinarith [hr]
theorem asm_of_max (n k w D : ℕ) (S : ℝ)
    (h : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D → 1 ≤ S * (1 - eta_k n K k) ^ t := by
  intro K t hk hb
  apply h K t hk
  have e : 2 * t * k = t * k + t * k := by ring
  rw [e] at hb ⊢
  rcases max_cases (t * k + t * k + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
    rw [h'] <;> omega
theorem exp_le_of_one_le (S x : ℝ) (t : ℕ) (hx : x ≤ 1) (h : 1 ≤ S * (1 - x) ^ t) :
    Real.exp ((t : ℝ) * x) ≤ S := by
  have hp0 : (0 : ℝ) ≤ (1 - x) ^ t := pow_nonneg (by linarith) t
  have hS : 0 ≤ S := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hp0
    linarith
  have hpow : (1 - x) ^ t ≤ Real.exp (-((t : ℝ) * x)) := by
    have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have h2 : (1 - x) ^ t ≤ Real.exp (-x) ^ t := pow_le_pow_left₀ (by linarith) h1 t
    rw [← Real.exp_nat_mul] at h2
    rwa [mul_neg] at h2
  have h3 : 1 ≤ S * Real.exp (-((t : ℝ) * x)) :=
    h.trans (mul_le_mul_of_nonneg_left hpow hS)
  have hpos : 0 < Real.exp ((t : ℝ) * x) := Real.exp_pos _
  calc Real.exp ((t : ℝ) * x) = Real.exp ((t : ℝ) * x) * 1 := (mul_one _).symm
    _ ≤ Real.exp ((t : ℝ) * x) * (S * Real.exp (-((t : ℝ) * x))) :=
        mul_le_mul_of_nonneg_left h3 hpos.le
    _ = S * (Real.exp ((t : ℝ) * x) * Real.exp (-((t : ℝ) * x))) := by ring
    _ = S := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
theorem size_core (n k K t : ℕ) (S : ℝ) (hkK : k ≤ K) (hKn : K ≤ n + 1)
    (h : 1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S := by
  have h1 := exp_le_of_one_le S (eta_k n K k) t (eta_k_le_one n K k) h
  refine le_trans (Real.exp_le_exp.mpr ?_) h1
  exact mul_le_mul_of_nonneg_left (eta_k_ge n K k hkK hKn) (Nat.cast_nonneg t)
theorem size_of_assembly_k (n k w D : ℕ) (S : ℝ)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K t : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hbud : K + 2 * t * k + 2 * k + w ≤ D) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S :=
  size_core n k K t S hkK hKn (hasm K t hkK hbud)
theorem final_aux (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hKw : 8 * K + 8 * w ≤ 5 * D)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ ((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * r ^ k) ≤ S := by
  obtain ⟨t, ht⟩ : ∃ t, t = D / (8 * k) := ⟨_, rfl⟩
  have htk : t * (8 * k) ≤ D := by rw [ht]; exact Nat.div_mul_le_self D (8 * k)
  have ht2 : 2 ≤ t := by rw [ht]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 8 * k * (t + 1) := by rw [ht]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : t * (8 * k) = 8 * (t * k) := by ring
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have e3 : 8 * k * (t + 1) = 8 * (t * k) + 8 * k := by ring
  have h2k : 2 * k ≤ t * k := Nat.mul_le_mul_right k ht2
  have hbud : K + 2 * t * k + 2 * k + w ≤ D := by rw [e2]; omega
  have hDt : D ≤ 12 * (t * k) := by omega
  have hcore := size_of_assembly_k n k w D S hasm K t hkK hKn hbud
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDtR : (D : ℝ) ≤ 12 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have h1 : (D : ℝ) / (24 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hk24 : (0 : ℝ) ≤ (D : ℝ) / (24 * (k : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (24 * (k : ℝ)) * r ^ k
      ≤ (t : ℝ) / 2 * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring
theorem final_of_assembly_k (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (3 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 7 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (3 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr
theorem final_of_assembly_k_w4 (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (6 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 4 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 3 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 3 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (6 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr
theorem exp_beats_poly_k (n k A D c : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hn : 1 ≤ n)
    (hA : n ≤ A * D) :
    (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hAR : (n : ℝ) ≤ (A : ℝ) * (D : ℝ) := by exact_mod_cast hA
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h24 : (0 : ℝ) < 24 * (k : ℝ) := by linarith
  have h24A : (0 : ℝ) < 24 * (k : ℝ) * (A : ℝ) := mul_pos h24 hA0
  have hcA : (0 : ℝ) < (c : ℝ) * (A : ℝ) := mul_pos hc0 hA0
  have hcn : (0 : ℝ) < (c : ℝ) * (n : ℝ) := mul_pos hc0 hn0
  have h1 : (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) ≤ (D : ℝ) / (24 * (k : ℝ)) := by
    rw [div_le_div_iff₀ h24A h24]
    nlinarith [mul_le_mul_of_nonneg_left hAR h24.le]
  have h2 : 1 / ((c : ℝ) * (A : ℝ)) ≤ (D : ℝ) / ((c : ℝ) * (n : ℝ)) := by
    rw [div_le_div_iff₀ hcA hcn]
    nlinarith [mul_le_mul_of_nonneg_left hAR hc0.le]
  have h3 : (0 : ℝ) ≤ 1 / ((c : ℝ) * (A : ℝ)) := by positivity
  calc (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      = (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) * (1 / ((c : ℝ) * (A : ℝ))) ^ k := by
        rw [one_div_pow, div_mul_div_comm, mul_one]
    _ ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ h3 h2 k) (pow_nonneg h3 k) (div_nonneg hD0 h24.le)
theorem final_linear_k (n k w D A : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) * (n : ℝ)) ≤ S := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (final_of_assembly_k n k w D S hk hkD hwD hDn hasm)
  have h := exp_beats_poly_k n k A D 3 hk (by norm_num) (by omega) hA
  push_cast at h
  rw [one_div_mul_eq_div]
  exact h
theorem pow_le_exp_lin (c : ℝ) (hc : 0 < c) (d n : ℕ)
    (hn : ((d + 1).factorial : ℝ) / c ^ (d + 1) ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ Real.exp (c * (n : ℝ)) := by
  have hx : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
  have h := Real.pow_div_factorial_le_exp _ hx (d + 1)
  refine le_trans ?_ h
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [le_div_iff₀ hF]
  have hn' : ((d + 1).factorial : ℝ) ≤ (n : ℝ) * c ^ (d + 1) :=
    (div_le_iff₀ (pow_pos hc _)).mp hn
  calc (n : ℝ) ^ d * ((d + 1).factorial : ℝ) ≤ (n : ℝ) ^ d * ((n : ℝ) * c ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = (c * (n : ℝ)) ^ (d + 1) := by ring
theorem final_superpoly_k (n k w D A d : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (hn : ((d + 1).factorial : ℝ) / (1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) ^ (d + 1)
      ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ S := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hc : (0 : ℝ) < 1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k) := by positivity
  exact (pow_le_exp_lin _ hc d n hn).trans (final_linear_k n k w D A S hk hkD hwD hDn hA hasm)
section Plan
theorem negLinEq_not_sat {V : Type} (a : V → Bool) (e : LinEq V) (h : LinEqSat a e) :
    ¬ LinEqSat a (negLinEq e) := by
  unfold LinEqSat at h
  unfold LinEqSat negLinEq
  intro h'
  cases hb : e.2 <;> simp_all
theorem linK_cut_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKCut C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) : LinKLineSat a R := by
  obtain ⟨T, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases hTT : T' = T
  · subst hTT
    refine ⟨U, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hU, ?_⟩), hsU⟩
    intro hmem
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    exact negLinEq_not_sat a e (hs' e he) (hsU _ (Finset.mem_singleton_self _))
  · exact ⟨T', Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT'⟩), hs'⟩
theorem linK_andIntro_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) :
    LinKLineSat a R := by
  obtain ⟨T₁, T₂, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases h1 : T' = T₁
  · by_cases h2 : U = T₂
    · subst h1 h2
      refine ⟨T' ∪ U, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hs' q hq
      · exact hsU q hq
    · exact ⟨U, Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2, hU⟩)), hsU⟩
  · exact ⟨T', Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1, hT'⟩)), hs'⟩
theorem linK_derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {k : ℕ}
    {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) (ha : ∀ C ∈ F, LinKLineSat a C) :
    ∀ C ∈ π, LinKLineSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | cut _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_cut_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | andIntro _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_andIntro_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | weak _ hC hw _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact LinKOne.weakening_sound hw (ih _ hC)
    · exact ih E hE
theorem linK_refutation_unsat :
    ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (π : List (LinKLine V)),
      IsLinKRefutation k F π → ¬ Satisfiable F := by
  rintro V _ F k π h ⟨a, ha⟩
  have hax : ∀ C ∈ (fun C => linKOfClause C) '' F, LinKLineSat a C := by
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨l, hl, hs⟩ := ha C hC
    refine ⟨{(({l.1} : Finset V), l.2)},
      Finset.mem_image.mpr ⟨(({l.1} : Finset V), l.2), Finset.mem_image.mpr ⟨l, hl, rfl⟩, rfl⟩,
      ?_⟩
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact (linEqSat_singleton a l.1 l.2).mpr hs
  obtain ⟨T, hT, -⟩ := linK_derivation_sound a h.1 hax ∅ h.2
  exact absurd hT (Finset.notMem_empty T)
theorem etaK_le_one : ∀ n K k : ℕ, LinKPlan.etaK n K k ≤ 1 :=
  fun n K k => eta_k_le_one n K k
theorem etaK_ge :
    ∀ n K k : ℕ, k ≤ K → K ≤ n + 1 →
      (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k) ≤ LinKPlan.etaK n K k := by
  intro n K k hk hK
  have h := eta_k_ge n K k hk hK
  rw [div_pow] at h
  have e : (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k)
      = (1 / 2 : ℝ) * ((((K - k + 1 : ℕ) : ℝ)) ^ k / ((n : ℝ) + 1) ^ k) := by ring
  rw [e]
  exact h
theorem final_plan_num (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = D / (4 * k) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = q - 1 := ⟨_, rfl⟩
  have hqk : q * (4 * k) ≤ D := by rw [hq]; exact Nat.div_mul_le_self D (4 * k)
  have hq4 : 4 ≤ q := by rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 4 * k * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : q * (4 * k) = 4 * (q * k) := by ring
  have e3 : 4 * k * (q + 1) = 4 * (q * k) + 4 * k := by ring
  have h4k : 4 * k ≤ q * k := Nat.mul_le_mul_right k hq4
  have etk : t * k = q * k - k := by rw [ht, Nat.sub_mul, one_mul]
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have hbud : K + max (2 * t * k + 2 * k) (t * k + w) ≤ D := by
    rw [e2]
    rcases max_cases (2 * (t * k) + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      rw [h'] <;> omega
  have hDt : D ≤ 8 * (t * k) := by omega
  have haD : 7 * D ≤ 16 * a := by omega
  have hcore := size_core n k K t S (by omega) (by omega) (hasm K t (by omega) hbud)
  rw [← ha] at hcore
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDtR : (D : ℝ) ≤ 8 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have h1 : (D : ℝ) / (16 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hr : (D : ℝ) / (4 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  have hr0 : (0 : ℝ) ≤ (D : ℝ) / (4 * (n : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k
      ≤ (t : ℝ) / 2 * ((a : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * ((a : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring
theorem final_of_assembly_plan :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
      (k w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
      ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
      (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - LinKPlan.etaK (Fintype.card V) K k) ^ t) →
      Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
        ≤ (π.length : ℝ) := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href hasm
  have hunsat : ¬ Satisfiable F := linK_refutation_unsat V F k π href
  have hDn : D < Fintype.card V := by
    by_contra hcon
    exact hnr (DegSizeArith.complete_deg V F w D hw hunsat (by omega) (by omega))
  exact final_plan_num (Fintype.card V) k w D _ hk hkD hwD hDn hasm
end Plan
end PEqualNP.Outside.L_pcx_377.H.DegSizeArithK

namespace PEqualNP.Outside.L_pcx_377.H.LinKSimA
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan PEqualNP.Outside.L_pcx_377.H.LinKPlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem totalDegree_one_add_le_k {p : MvPolynomial σ (ZMod 2)} {k : ℕ}
    (h : p.totalDegree ≤ k) : (1 + p).totalDegree ≤ k := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le_k {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    {k : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ k) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card * k := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := k) ha
  rw [Nat.mul_comm]
  exact this
theorem prod_absorb_k (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ k : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ k) (hB : s.card * k + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.add_mul, Nat.one_mul] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ k := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card * k + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le_k s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ k :=
      totalDegree_one_add_le_k (hdeg u (Finset.mem_insert_self u s))
    have h2 := DegSizeSim.absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le_k {G : Set (MvPolynomial σ (ZMod 2))} {k : ℕ}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le_k {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_le_k Finset.univ qs (fun j _ => h j)
  simpa using this
theorem span_mul_mem {G : Set (MvPolynomial σ (ZMod 2))} {Q : MvPolynomial σ (ZMod 2)}
    (hg : ∀ g ∈ G, g * Q ∈ C) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q * Q ∈ C := by
  induction hq using Submodule.span_induction with
  | mem g hg' => exact hg g hg'
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.add_mem hx hy
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem transfer_k' (hC : DegClosed C D) {K t k r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t * k + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := fun q hq =>
    span_mul_mem (fun g hg' => by
      rw [← mul_assoc]
      exact hg g hg') hq
  have hdq : ∀ j, (qs j).totalDegree ≤ k := fun j => totalDegree_span_le_k hG (hqs j)
  have h1 := prod_absorb_k hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t * k + K :=
    totalDegree_mul_le' (totalDegree_appr_le_k qs hdq) hf
  have h2 := DegSizeSim.absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer_k :
    ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t * k + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg =>
    transfer_k' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t k : ℕ}
  {f : MvPolynomial V (ZMod 2)}
theorem totalDegree_lineInputs_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem totalDegree_lineAppr_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  totalDegree_appr_le_k qs fun j =>
    totalDegree_span_le_k (totalDegree_lineInputs_le hL) (hqs j)
theorem lineInputs_linKOfClause_subset [DecidableEq V] (A : Clause V) :
    lineInputs (linKOfClause A) ⊆ (fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V)) := by
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
  exact ⟨q, Finset.mem_coe.mpr hq, (termPoly_singleton q).symm⟩
theorem step_ax_k' [DecidableEq V] (hC : DegClosed C D) (A : Clause V) {w : ℕ}
    (hA : clausePoly A ∈ C) (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A)))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  refine DegSizeSim.step_ax hC A hA hw qs
    (fun j => Submodule.span_mono (lineInputs_linKOfClause_subset A) (hqs j)) hf hB ?_
  intro q hq
  have := hH {q} (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rwa [termPoly_singleton] at this
theorem step_ax_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C := by
  intro V _ C D K t k w f A qs hC hk hA hw hqs hf hB hH
  have htk : t ≤ t * k := Nat.le_mul_of_pos_right t hk
  exact step_ax_k' hC A hA hw qs hqs hf (by omega) hH
theorem step_cut_k' [DecidableEq V] (hC : DegClosed C D) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2))
    (h1 : ∀ T ∈ L₁, T.card ≤ k) (h2 : ∀ T ∈ L₂, T.card ≤ k) (hM : ∀ T ∈ M, T.card ≤ k)
    (hq1 : ∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁))
    (hq2 : ∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t * k + 2 * k ≤ D) (hcut : IsLinKCut L₁ L₂ M)
    (hP1 : (∏ j, (1 + q₁ j)) * f ∈ C) (hP2 : (∏ j, (1 + q₂ j)) * f ∈ C)
    (hHM : ∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k := totalDegree_lineAppr_le hM qM hqM
  generalize (∏ j, (1 + qM j)) = P at hdM hHM ⊢
  obtain ⟨T, hT1, -, rfl⟩ := hcut
  have hTk : T.card ≤ k := h1 T hT1
  have hτ : (termPoly T).totalDegree ≤ k := (totalDegree_termPoly_le T).trans hTk
  have hQ : (P * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hd1 : (1 + termPoly T).totalDegree ≤ k := totalDegree_one_add_le_k hτ
  have hmul : 2 * t * k = t * k + t * k := by ring
  have hA : (1 + termPoly T) * P * f ∈ C := by
    have hdR : ((1 + termPoly T) * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hd1 hdM
    refine transfer_k' hC q₁ (totalDegree_lineInputs_le h1) hq1 hf hdR (by omega) hP1 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₁ := Finset.mem_coe.mp hS
    by_cases hST : S = T
    · rw [hST]
      have := idem_mul hC (termPoly T) (P * f) hQ hτ (by omega)
      have e1 : termPoly T * ((1 + termPoly T) * P) * f
          = P * f * (termPoly T * termPoly T + termPoly T) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS'⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h1 S hS'))) hf
      have := DegSizeSim.absorb_le hC (1 + termPoly T) hmem hd1 hd (by omega)
      have e1 : termPoly S * ((1 + termPoly T) * P) * f
          = (1 + termPoly T) * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have hB' : termPoly T * P * f ∈ C := by
    have hdR : (termPoly T * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hτ hdM
    refine transfer_k' hC q₂ (totalDegree_lineInputs_le h2) hq2 hf hdR (by omega) hP2 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₂ := Finset.mem_coe.mp hS
    by_cases hSi : S ∈ T.image (fun e => ({negLinEq e} : LinTerm V))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hSi
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
      have := term_neg_mul hC T e he (P * f) hQ (by omega)
      show termPoly {negLinEq e} * (termPoly T * P) * f ∈ C
      rw [termPoly_singleton]
      have e1 : eqPoly (negLinEq e) * (termPoly T * P) * f
          = P * f * (termPoly T * eqPoly (negLinEq e)) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hS', hSi⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h2 S hS'))) hf
      have := DegSizeSim.absorb_le hC (termPoly T) hmem hτ hd (by omega)
      have e1 : termPoly S * (termPoly T * P) * f
          = termPoly T * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have h3 := C.add_mem hA hB'
  have e1 : (1 + termPoly T) * P * f + termPoly T * P * f = P * f := by
    linear_combination char2_add_self (termPoly T * P * f)
  rwa [e1] at h3
theorem step_cut_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
  exact step_cut_k' hC L₁ L₂ M q₁ q₂ qM h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
end Lines
end PEqualNP.Outside.L_pcx_377.H.LinKSimA

namespace PEqualNP.Outside.L_pcx_377.H.LinKSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan PEqualNP.Outside.L_pcx_377.H.LinKPlan
section Abstract
variable {σ : Type}
theorem and_totalDegree_span_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem and_totalDegree_appr_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := Helpers.totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, mul_comm] at this
  exact this
end Abstract
section Lines
variable {V : Type}
theorem and_totalDegree_lineInputs_le {k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem and_totalDegree_lineAppr_le {t k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  and_totalDegree_appr_le qs fun j =>
    and_totalDegree_span_le (and_totalDegree_lineInputs_le L hL) (hqs j)
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem and_half (hC : DegClosed C D) (L M : LinKLine V) (T₀ : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) {K m k : ℕ}
    (hM : ∀ T ∈ M, T.card ≤ k) (hT₀ : T₀.card ≤ k)
    (hP : P.totalDegree ≤ m) (hf : f.totalDegree ≤ K) (hB : K + m + 2 * k ≤ D)
    (htr : ∀ R : MvPolynomial V (ZMod 2), R.totalDegree ≤ m + k →
      (∀ T ∈ L, termPoly T * R * f ∈ C) → R * f ∈ C)
    (hsub : ∀ T ∈ L, T ≠ T₀ → T ∈ M)
    (hHM : ∀ T ∈ M, P * termPoly T * f ∈ C) :
    (1 + termPoly T₀) * P * f ∈ C := by
  have hg0 : (termPoly T₀).totalDegree ≤ k := (totalDegree_termPoly_le T₀).trans hT₀
  have hd1 : (1 + termPoly T₀).totalDegree ≤ k :=
    (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg0)
  refine htr _ ((totalDegree_mul_le' hd1 hP).trans (by omega)) ?_
  intro T hT
  by_cases h0 : T = T₀
  · subst h0
    have h1 := idem_mul hC (termPoly T) (P * f) (totalDegree_mul_le' hP hf) hg0
      (by omega)
    have e : termPoly T * ((1 + termPoly T) * P) * f
        = P * f * (termPoly T * termPoly T + termPoly T) := by ring
    rw [e]
    exact h1
  · have hTM := hsub T hT h0
    have hmem := hHM T hTM
    have hd : (P * termPoly T * f).totalDegree ≤ m + k + K :=
      totalDegree_mul_le'
        (totalDegree_mul_le' hP ((totalDegree_termPoly_le T).trans (hM T hTM))) hf
    have h1 := DegSizeSim.absorb_le hC (1 + termPoly T₀) hmem hd1 hd (by omega)
    have e : termPoly T * ((1 + termPoly T₀) * P) * f
        = (1 + termPoly T₀) * (P * termPoly T * f) := by ring
    rw [e]
    exact h1
end Lines
theorem step_andIntro_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
      (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
      (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
      (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC hL1 hL2 hM hq1 hq2 hqM hf hB hand hP1 hP2 hHM
  obtain ⟨T₁, T₂, hT1, hT2, rfl⟩ := hand
  rw [mul_assoc] at hB
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    and_totalDegree_lineAppr_le _ hM qM hqM
  have hc1 : T₁.card ≤ k := hL1 T₁ hT1
  have hc2 : T₂.card ≤ k := hL2 T₂ hT2
  have hg1 : (termPoly T₁).totalDegree ≤ k := (totalDegree_termPoly_le T₁).trans hc1
  have hg2 : (termPoly T₂).totalDegree ≤ k := (totalDegree_termPoly_le T₂).trans hc2
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hA : (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₁ _ T₁ _ f hM hc1 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₁) q₁ f R hC
        (and_totalDegree_lineInputs_le L₁ hL1) hq1 hf hR (by omega) hP1 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hA2 : (1 + termPoly T₂) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₂ _ T₂ _ f hM hc2 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₂) q₂ f R hC
        (and_totalDegree_lineInputs_le L₂ hL2) hq2 hf hR (by omega) hP2 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hU : (∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f ∈ C :=
    hHM _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hun := term_union_mul hC T₁ T₂ ((∏ j, (1 + qM j)) * f) hQ (by omega)
  have hd2 : ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f).totalDegree ≤ k + t * k + K := by
    have hd : (1 + termPoly T₂).totalDegree ≤ k :=
      (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg2)
    exact totalDegree_mul_le' (totalDegree_mul_le' hd hdM) hf
  have hmid := DegSizeSim.absorb_le hC (termPoly T₁) hA2 hg1 hd2 (by omega)
  have hsum := C.add_mem (C.add_mem hA hmid) (C.add_mem hU hun)
  have e : (∏ j, (1 + qM j)) * f
      = (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f
        + termPoly T₁ * ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f)
        + ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f
          + (∏ j, (1 + qM j)) * f * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂)) := by
    linear_combination
      (-1 : MvPolynomial V (ZMod 2)) * char2_add_self (termPoly T₁ * (∏ j, (1 + qM j)) * f)
      - char2_add_self (termPoly T₁ * termPoly T₂ * (∏ j, (1 + qM j)) * f)
      - char2_add_self ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f)
  rw [e]
  exact hsum
end PEqualNP.Outside.L_pcx_377.H.LinKSim

namespace PEqualNP.Outside.L_pcx_377.H.LinKSim
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan PEqualNP.Outside.L_pcx_377.H.LinKPlan
section Degrees
variable {σ : Type}
theorem weak_span_degree_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem weak_lineInputs_degree_le {V : Type} {k : ℕ} (L : LinKLine V)
    (hL : ∀ T ∈ L, T.card ≤ k) : ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem weak_appr_degree_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, Nat.mul_comm] at this
  exact this
end Degrees
section Cases
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_case_term (hC : DegClosed C D) {K r k : ℕ} (T S : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k) (hS : S.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + 2 * k ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (hS' : P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  have h1 := weak_term_mul hC T S himp (P * f) (b := r + K) (totalDegree_mul_le' hP hf)
    (by omega)
  have hdS : (P * termPoly S * f).totalDegree ≤ r + k + K :=
    totalDegree_mul_le' (totalDegree_mul_le' hP ((totalDegree_termPoly_le S).trans hS)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hS'
    ((totalDegree_termPoly_le T).trans hT) hdS (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * termPoly S) + termPoly T * (P * termPoly S * f) := by
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * termPoly S * f))
  rw [e]
  exact C.add_mem h1 h2
theorem weak_case_disj [Fintype V] [DecidableEq V] (hC : DegClosed C D) {K r k : ℕ}
    (T : LinTerm V) (M : LinKLine V) (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + k + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)
    (hM : ∀ S ∈ M, P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_line (C := C) (D := D) hC T M himp
  have h1 := hmul (P * f) (r + K) (totalDegree_mul_le' hP hf) (by omega)
  have hsum : ∑ d ∈ J, P * eqPoly d * f ∈ C := by
    refine Submodule.sum_mem _ fun d hd => ?_
    have := hM {d} (hJ d hd)
    rwa [termPoly_singleton] at this
  have hds : (∑ d ∈ J, P * eqPoly d * f).totalDegree ≤ r + 1 + K :=
    totalDegree_finsetSum_le fun d _ =>
      totalDegree_mul_le' (totalDegree_mul_le' hP (totalDegree_eqPoly_le d)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hsum
    ((totalDegree_termPoly_le T).trans hT) hds (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)
        + termPoly T * ∑ d ∈ J, P * eqPoly d * f := by
    have e1 : ∑ d ∈ J, P * eqPoly d * f = P * (∑ d ∈ J, eqPoly d) * f := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1]
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * (∑ d ∈ J, eqPoly d) * f))
  rw [e]
  exact C.add_mem h1 h2
end Cases
theorem step_weak_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
      (qL qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
      (∏ j, (1 + qL j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ _ C D K t k f L M qL qM hC hk hL hM hqL hqM hf hB hweak hPL hHM
  have h2 : 2 * t * k = t * k + t * k := by ring
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    weak_appr_degree_le qM fun j =>
      weak_span_degree_le (weak_lineInputs_degree_le M hM) (hqM j)
  refine htransfer V C D K t k (t * k) (lineInputs L) qL f _ hC
    (weak_lineInputs_degree_le L hL) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ L := Finset.mem_coe.mp hT
  rcases hweak T hT' with ⟨S, hS, himp⟩ | himp
  · exact weak_case_term hC T S _ f (hL T hT') (hM S hS) hdM hf (by omega) himp (hHM S hS)
  · exact weak_case_disj hC T M _ f (hL T hT') hdM hf (by omega) himp hHM
end PEqualNP.Outside.L_pcx_377.H.LinKSim

namespace PEqualNP.Outside.L_pcx_377.H.LinKSim
open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.DegSizePlan PEqualNP.Outside.L_pcx_377.H.LinKPlan
def AxRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C
def CutRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def AndRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def WeakRule : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
    (∏ j, (1 + qL j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def SimDrv : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) →
    IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)
def SimRef : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
theorem drv_card_le {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil =>
    intro L hL
    simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
theorem simulation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule) (hweak : WeakRule) :
    SimDrv := by
  intro V _ _ F π k w D K t f qs hk hw hder hB hf
  have hB1 : K + 2 * t * k + 2 * k ≤ D := by
    have := (Nat.add_le_add_left (le_max_left (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hB2 : K + t * k + w ≤ D := by
    have := (Nat.add_le_add_left (le_max_right (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hD2 : 2 ≤ D := by
    have h2 : 2 ≤ 2 * k := by omega
    exact h2.trans ((Nat.le_add_left _ _).trans hB1)
  have hwD : w ≤ D := (Nat.le_add_left _ _).trans hB2
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ hD2 fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ L ∈ ρ, ∀ T ∈ L, (∏ j, (1 + qs L j)) * termPoly T * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 _ ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((DegSizeSim.totalDegree_clausePoly_le A).trans (hAw.trans hwD))
        exact hax V (pcClosure (cnfSystem F) D) D K t k w f A (qs (linKOfClause A))
          hC hk hmem hAw (hs _ List.mem_cons_self) hf hB2 (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @cut ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hcut V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @andIntro ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hand V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M hρ' h1 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hweak V (pcClosure (cnfSystem F) D) D K t k f L1 L (qs L1) (qs L)
          hC hk (drv_card_le hρ' L1 h1) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf hB1 hrule
          (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH
theorem simulation_refutation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule)
    (hweak : WeakRule) : SimRef := by
  intro V _ _ F π k w D K t f qs hk hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation_of hax hcut hand hweak V F π k w D K t f qs hk hw hder hB hf hs hH
    ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa [lineInputs] using this
  simpa [hq] using h
end PEqualNP.Outside.L_pcx_377.H.LinKSim

namespace PEqualNP.Outside.L_pcx_377.H.LinKAsm
open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_377.H.Helpers
  PEqualNP.Outside.L_pcx_377.H.LinKPlan PEqualNP.Outside.L_pcx_377.H.DegSizePlan
def StmtSimRefutation : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
def StmtArith : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t) →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
def StmtAssembly : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π → ¬ PCRefutable (cnfSystem F) D →
    k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t
def StmtGeneral : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
theorem term_card {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | cut _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | weak _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
theorem etaK_le_one (n K k : ℕ) : etaK n K k ≤ 1 := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  unfold etaK
  exact (div_le_one (by positivity)).mpr (by linarith)
theorem assembly (hSim : StmtSimRefutation) : StmtAssembly := by
  classical
  intro V _ _ F π k w D K t hk hw href hnr hkK hB
  by_contra hlt
  rw [not_le] at hlt
  have hk2 : 2 * k ≤ 2 * t * k + 2 * k := Nat.le_add_left _ _
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - etaK (Fintype.card V) K k) ^ t :=
    pow_nonneg (sub_nonneg.mpr (etaK_le_one _ K k)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - DegSizeGainK.eta_k (Fintype.card V) K k) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  have htk : t * k + k ≤ 2 * t * k + 2 * k := by nlinarith
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGainK.common_k V (pcClosure (cnfSystem F) D) D K t k (LinKLine V) π.toFinset
      (fun L => L.image (fun T => termPoly T)) hC h1
      (by
        intro L hL g hg
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hg
        exact le_trans (totalDegree_termPoly_le T)
          (term_card href.1 L (List.mem_toFinset.mp hL) T hT))
      hkK (by omega) hS
  apply hfC
  refine hSim V F π k w D K t f qs hk hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [lineInputs, Finset.coe_image] using this
  · intro L hL T hT
    exact hmem L (List.mem_toFinset.mpr hL) (termPoly T) (Finset.mem_image_of_mem _ hT)
theorem degree_to_size_k (hSim : StmtSimRefutation) (hArith : StmtArith) : StmtGeneral := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href
  exact hArith V F π k w D hw hk hkD hwD hnr href
    (fun K t hkK hB => assembly hSim V F π k w D K t hk hw href hnr hkK hB)
end PEqualNP.Outside.L_pcx_377.H.LinKAsm

namespace PEqualNP.Outside.L_pcx_377.H.LinKSim
open PEqualNP.Outside.L_pcx_377.H.LinKPlan PEqualNP.Outside.L_pcx_377.H.LinKSimA
theorem step_andIntro : AndRule := step_andIntro_of transfer_k
theorem step_weak : WeakRule := step_weak_of transfer_k
theorem simulation : SimDrv := simulation_of step_ax_k step_cut_k step_andIntro step_weak
theorem simulation_refutation : PEqualNP.Outside.L_pcx_377.H.LinKAsm.StmtSimRefutation :=
  simulation_refutation_of step_ax_k step_cut_k step_andIntro step_weak
end PEqualNP.Outside.L_pcx_377.H.LinKSim

namespace PEqualNP.Outside.L_pcx_377.H.LinKFinal
open PEqualNP.ProofComplexity PEqualNP.Expanders
def StmtLinK : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
theorem funGraphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ funGraphPHP G, C.card ≤ max b 2 := by
  intro C hC
  rcases hC with hC | ⟨e, e', -, -, rfl⟩
  · exact PhpFinal.graphPHP_width G b hb C hC
  · exact le_trans Finset.card_le_two (le_max_right _ _)
theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (hxy : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)
theorem degree_facts (n s₀ w : ℕ) (hs : 0 < s₀) (hw : 0 < w) (hn : 4 * (s₀ * w) ≤ n) :
    w * (n / s₀ / w) ≤ n / s₀ ∧ n ≤ 2 * (s₀ * w * (n / s₀ / w)) := by
  refine ⟨Nat.mul_div_le _ _, ?_⟩
  have h1 : n < s₀ * (n / s₀ + 1) := Nat.lt_mul_div_succ n hs
  have h2 : n / s₀ < w * (n / s₀ / w + 1) := Nat.lt_mul_div_succ _ hw
  have h3 : s₀ * (n / s₀ + 1) ≤ s₀ * (w * (n / s₀ / w + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : s₀ * (w * (n / s₀ / w + 1)) = s₀ * w * (n / s₀ / w) + s₀ * w := by ring
  omega
theorem exp_arith (k s₀ w n D card : ℕ) (hk : 1 ≤ k) (hs : 0 < s₀) (hw : 0 < w) (hn : 0 < n)
    (hcard_pos : 0 < card) (hcard : card ≤ 2 * n * w) (hnD : n ≤ 2 * (s₀ * w * D)) :
    (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n ≤
      (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hnD' : (n : ℝ) ≤ 2 * ((s₀ : ℝ) * w * D) := by exact_mod_cast hnD
  have hcard' : (card : ℝ) ≤ 2 * n * w := by exact_mod_cast hcard
  set ρ : ℝ := 1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h1 : (n : ℝ) / (32 * (k : ℝ) * s₀ * w) ≤ (D : ℝ) / (16 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnD' (by positivity : (0 : ℝ) ≤ 16 * (k : ℝ))]
  have h2 : ρ ≤ (D : ℝ) / (4 * (card : ℝ)) := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h8 : 4 * (card : ℝ) ≤ 8 * n * w := by linarith
    have h9 : 8 * (n : ℝ) * w ≤ 16 * ((s₀ : ℝ) * w * D) * w := by
      have := mul_le_mul_of_nonneg_right hnD' (by positivity : (0 : ℝ) ≤ 8 * w)
      linarith
    nlinarith
  have h3 : ρ ^ k ≤ ((D : ℝ) / (4 * (card : ℝ))) ^ k := pow_le_pow_left₀ hρ0 h2 k
  calc ρ ^ k / (32 * (k : ℝ) * s₀ * w) * n = (n : ℝ) / (32 * (k : ℝ) * s₀ * w) * ρ ^ k := by
        ring
    _ ≤ (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k :=
        mul_le_mul h1 h3 (pow_nonneg hρ0 k) (by positivity)
end PEqualNP.Outside.L_pcx_377.H.LinKFinal

namespace PEqualNP.Outside.L_pcx_377.H.LinKWire
theorem general (hSim : LinKAsm.StmtSimRefutation) : LinKFinal.StmtLinK :=
  LinKAsm.degree_to_size_k hSim DegSizeArithK.final_of_assembly_plan
end PEqualNP.Outside.L_pcx_377.H.LinKWire

namespace PEqualNP.Outside.L_pcx_377.H.LinKGrow
open PEqualNP.ProofComplexity PEqualNP.Expanders PEqualNP.Outside.L_pcx_377.H.LinKFinal
theorem graph_bound (hL : StmtLinK) (b s₀ n k w : ℕ) (hw : w = max b 2) (hs₀ : 0 < s₀)
    (hk : 1 ≤ k) (G : BipGraph (n + 1) n) (hLd : LeftDegLe G b)
    (hE : IsBdryExpander G (n / s₀) 2)
    (hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n) (hn2 : 4 * (s₀ * w) + s₀ ≤ n)
    (π : List (LinKLine (GEdge G))) (hπ : IsLinKRefutation k (funGraphPHP G) π) :
    Real.exp ((1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n)
      ≤ (π.length : ℝ) := by
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hsw : 0 < s₀ * w := Nat.mul_pos hs₀ (by omega)
  have hnpos : 0 < n := by omega
  obtain ⟨hwD, hnD⟩ := degree_facts n s₀ w hs₀ (by omega) (by omega)
  set D := n / s₀ / w with hD
  have hDk : 16 * k + 4 * w ≤ D := by
    have h : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ 2 * (s₀ * w) * D := by
      calc 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n := hn1
        _ ≤ 2 * (s₀ * w * D) := hnD
        _ = 2 * (s₀ * w) * D := by ring
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have hs1 : 1 ≤ n / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr (by omega)
  have hLw : LeftDegLe G w := fun i => le_trans (hLd i) hbw
  have hnr := PEqualNP.Outside.L_pcx_377.H.L049 (n + 1) n G (n / s₀) w D hE hLw hs1 hwD
  have hcard_pos : 0 < Fintype.card (GEdge G) := by
    have h := hE {0} (by rw [Finset.card_singleton]; exact hs1)
    rw [Finset.card_singleton] at h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
    unfold uniqueNbrs at hj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj).2
    have hi' : i ∈ Finset.filter (fun i => j ∈ G i) {0} := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact Fintype.card_pos_iff.mpr ⟨⟨(i, j), (Finset.mem_filter.mp hi').2⟩⟩
  have hcard : Fintype.card (GEdge G) ≤ 2 * n * w := by
    have := le_trans (PhpFinal.card_gedge_le G b hLd) (Nat.mul_le_mul_left (n + 1) hbw)
    have h2 : (n + 1) * w ≤ 2 * n * w := Nat.mul_le_mul_right _ (by omega)
    omega
  have hsize := hL (GEdge G) (funGraphPHP G) π k w D
    (fun C hC => hw ▸ funGraphPHP_width G b hLd C hC) hk (by omega) (by omega) hnr hπ
  have harith := exp_arith k s₀ w n D (Fintype.card (GEdge G)) hk hs₀ (by omega) hnpos
    hcard_pos hcard hnD
  exact le_trans (Real.exp_le_exp.mpr harith) hsize
end PEqualNP.Outside.L_pcx_377.H.LinKGrow

namespace PEqualNP.Outside.L_pcx_377

section L_pcx_377_Main

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Expanders

private lemma linEqSat_neg {V : Type} (a : V → Bool) (q : LinEq V) :
    LinEqSat a (negLinEq q) ↔ ¬ LinEqSat a q := by
  rcases q with ⟨f, b⟩
  cases b <;> simp [LinEqSat, negLinEq]

private lemma negLinEq_negLinEq {V : Type} (q : LinEq V) : negLinEq (negLinEq q) = q := by
  rcases q with ⟨f, b⟩
  simp [negLinEq]

private def toZ2 {V : Type} (x : V → Bool) : V → ZMod 2 :=
  fun v => ((x v).toNat : ZMod 2)

private lemma decide_toZ2 {V : Type} (x : V → Bool) :
    (fun v => decide (toZ2 x v = 1)) = x := by
  funext v
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  dsimp only [toZ2]
  cases x v <;> decide

private lemma eval_eqPoly_toZ2_eq_one_iff {V : Type} (x : V → Bool) (q : LinEq V) :
    eval (toZ2 x) (H.Helpers.eqPoly q) = 1 ↔ LinEqSat x q := by
  have h := H.Helpers.linEqSat_iff_sum (toZ2 x) q
  rw [decide_toZ2] at h
  rw [h]
  unfold H.Helpers.eqPoly
  simp [map_add, map_sum, eval_X, eval_C]

private lemma eval_eqPoly_add_one_eq_zero_iff {V : Type} (x : V → Bool) (q : LinEq V) :
    eval (toZ2 x) (H.Helpers.eqPoly q + 1) = 0 ↔ LinEqSat x q := by
  rw [← eval_eqPoly_toZ2_eq_one_iff, map_add, map_one]
  generalize eval (toZ2 x) (H.Helpers.eqPoly q) = z
  revert z; decide

private lemma linKWeak_of_subset {V : Type} {L M : LinKLine V} (h : L ⊆ M) :
    IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

private lemma linKWeak_refl {V : Type} (L : LinKLine V) : IsLinKWeakening L L :=
  linKWeak_of_subset subset_rfl

private lemma linK_concat {V : Type} [DecidableEq V] {k : ℕ} {F : Set (LinKLine V)}
    {π₁ π₂ : List (LinKLine V)}
    (h1 : IsLinKDerivation k IsLinKWeakening F π₁)
    (h2 : IsLinKDerivation k IsLinKWeakening (F ∪ {L | L ∈ π₁}) π₂) :
    IsLinKDerivation k IsLinKWeakening F (π₂ ++ π₁) := by
  induction h2 with
  | nil => exact h1
  | @ax π C hπ hC hk ih =>
    rcases hC with hF | hmem
    · exact IsLinKDerivation.ax ih hF hk
    · exact IsLinKDerivation.weak ih (List.mem_append_right _ hmem) (linKWeak_refl C) hk
  | @cut π C D R _ hC hD hcut hk ih =>
    exact IsLinKDerivation.cut ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hcut hk
  | @andIntro π C D R _ hC hD hand hk ih =>
    exact IsLinKDerivation.andIntro ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hand hk
  | @weak π C D _ hC hw hk ih =>
    exact IsLinKDerivation.weak ih (List.mem_append_left _ hC) hw hk

private lemma linK_derive_cut_eq {V : Type} [DecidableEq V] {k : ℕ} {F : Set (LinKLine V)}
    {π : List (LinKLine V)} (hπ : IsLinKDerivation k IsLinKWeakening F π)
    (M : LinKLine V) (hMk : ∀ T ∈ M, T.card ≤ k) (f : Finset V)
    (h1 : M ∪ {({(f, true)} : LinTerm V)} ∈ π)
    (h2 : M ∪ {({(f, false)} : LinTerm V)} ∈ π) :
    ∃ ext : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening F (ext ++ π) ∧
      M ∈ ext ++ π ∧ ext.length ≤ 1 := by
  by_cases hm1 : ({(f, true)} : LinTerm V) ∈ M
  · refine ⟨[], hπ, ?_, by simp⟩
    have heq : M ∪ {({(f, true)} : LinTerm V)} = M := by
      ext T; simp only [Finset.mem_union, Finset.mem_singleton]
      exact ⟨fun h => h.elim id (fun he => he ▸ hm1), Or.inl⟩
    rwa [heq] at h1
  · by_cases hm2 : ({(f, false)} : LinTerm V) ∈ M
    · refine ⟨[], hπ, ?_, by simp⟩
      have heq : M ∪ {({(f, false)} : LinTerm V)} = M := by
        ext T; simp only [Finset.mem_union, Finset.mem_singleton]
        exact ⟨fun h => h.elim id (fun he => he ▸ hm2), Or.inl⟩
      rwa [heq] at h2
    · have hcut : IsLinKCut (M ∪ {({(f, true)} : LinTerm V)}) (M ∪ {({(f, false)} : LinTerm V)}) M := by
        refine ⟨{(f, true)}, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton.mp he]
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · ext T
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Finset.mem_sdiff,
            Finset.mem_image, exists_eq_left, negLinEq, Bool.not_true]
          constructor
          · intro hT
            refine Or.inl ⟨fun he => hm1 (he ▸ hT), Or.inl hT⟩
          · rintro (⟨hne, hT | rfl⟩ | ⟨hT | rfl, hne⟩)
            · exact hT
            · exact (hne rfl).elim
            · exact hT
            · exact (hne rfl).elim
      exact ⟨[M], IsLinKDerivation.cut hπ h1 h2 hcut hMk, List.mem_cons_self, by simp⟩

private lemma linK_derive_term_taut {V : Type} [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (hπ : IsLinKDerivation k IsLinKWeakening F π) {L0 : LinKLine V} (hL0 : L0 ∈ π) :
    ∀ Q : LinTerm V, Q.card ≤ k →
      ∃ ext : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F (ext ++ π) ∧
        ({Q} ∪ Q.image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π ∧
        ext.length ≤ 3 * Q.card + 1 := by
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro _
    have hw : IsLinKWeakening L0 ({(∅ : LinTerm V)} : LinKLine V) :=
      fun _ _ => Or.inl ⟨∅, Finset.mem_singleton_self _, fun _ _ q hq => (Finset.notMem_empty q hq).elim⟩
    have hcard : ∀ T ∈ ({(∅ : LinTerm V)} : LinKLine V), T.card ≤ k := by
      intro T hT; rw [Finset.mem_singleton.mp hT]; simp
    refine ⟨[{(∅ : LinTerm V)}], IsLinKDerivation.weak hπ hL0 hw hcard, ?_, by simp⟩
    simp
  | @insert q S hqS ih =>
    intro hQk
    rw [Finset.card_insert_of_notMem hqS] at hQk
    rcases ih (by omega) with ⟨ext1, hder1, hmem1, hlen1⟩
    let Lq : LinKLine V := {({q} : LinTerm V), ({negLinEq q} : LinTerm V)}
    have hwq : IsLinKWeakening L0 Lq := by
      intro T _
      refine Or.inr fun a _ => ?_
      by_cases hsat : LinEqSat a q
      · exact ⟨q, Finset.mem_insert_self _ _, hsat⟩
      · exact ⟨negLinEq q, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), (linEqSat_neg a q).mpr hsat⟩
    have hcardq : ∀ T ∈ Lq, T.card ≤ k := by
      intro T hT
      simp only [Lq, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl <;> simpa using hk
    have hder2 : IsLinKDerivation k IsLinKWeakening F (Lq :: (ext1 ++ π)) :=
      IsLinKDerivation.weak hder1 (List.mem_append_right _ hL0) hwq hcardq
    let LS : LinKLine V := {S} ∪ S.image (fun r => ({negLinEq r} : LinTerm V))
    let R : LinKLine V := (Lq.erase {q} ∪ LS.erase S) ∪ {{q} ∪ S}
    have hand : IsLinKAndIntro Lq LS R :=
      ⟨{q}, S, Finset.mem_insert_self _ _, Finset.mem_union_left _ (Finset.mem_singleton_self _), rfl⟩
    let Ltarget : LinKLine V := {insert q S} ∪ (insert q S).image (fun r => ({negLinEq r} : LinTerm V))
    have hRsub : R ⊆ Ltarget := by
      intro T hT
      simp only [R, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, Lq, LS,
        Finset.mem_insert, Finset.mem_image, Ltarget] at hT ⊢
      rcases hT with ((⟨hne, rfl | rfl⟩ | ⟨hne, rfl | ⟨r, hr, rfl⟩⟩) | rfl)
      · exact (hne rfl).elim
      · exact Or.inr ⟨q, Or.inl rfl, rfl⟩
      · exact (hne rfl).elim
      · exact Or.inr ⟨r, Or.inr hr, rfl⟩
      · left; ext e; simp
    have hcardT : ∀ T ∈ Ltarget, T.card ≤ k := by
      intro T hT
      simp only [Ltarget, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hT
      rcases hT with rfl | ⟨r, _, rfl⟩
      · rw [Finset.card_insert_of_notMem hqS]; exact hQk
      · simpa using hk
    have hcardR : ∀ T ∈ R, T.card ≤ k := fun T hT => hcardT T (hRsub hT)
    have hder3 : IsLinKDerivation k IsLinKWeakening F (R :: Lq :: (ext1 ++ π)) :=
      IsLinKDerivation.andIntro hder2 List.mem_cons_self (List.mem_cons_of_mem _ hmem1) hand hcardR
    have hder4 : IsLinKDerivation k IsLinKWeakening F (Ltarget :: R :: Lq :: (ext1 ++ π)) :=
      IsLinKDerivation.weak hder3 List.mem_cons_self (linKWeak_of_subset hRsub) hcardT
    refine ⟨Ltarget :: R :: Lq :: ext1, hder4, List.mem_cons_self, ?_⟩
    simp only [List.length_cons, Finset.card_insert_of_notMem hqS]
    omega

private lemma shift_linKDerivation {V : Type} [DecidableEq V] {k : ℕ}
    (F_base F_ext : Set (LinKLine V)) (M : LinKLine V) (hMk : ∀ T ∈ M, T.card ≤ k)
    {σ : List (LinKLine V)} (hσ : IsLinKDerivation k IsLinKWeakening (F_base ∪ F_ext) σ) :
    ∃ σ' : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening (F_base ∪ (fun L => L ∪ M) '' F_ext) σ' ∧
      (∀ L ∈ σ, L ∪ M ∈ σ') ∧ σ'.length ≤ 2 * σ.length := by
  induction hσ with
  | nil => exact ⟨[], IsLinKDerivation.nil, by simp, by simp⟩
  | @ax π C hπ hC hk ih =>
    rcases ih with ⟨σ', hder', hmem', hlen'⟩
    have hkCM : ∀ T ∈ C ∪ M, T.card ≤ k := fun T hT =>
      (Finset.mem_union.mp hT).elim (hk T) (hMk T)
    rcases hC with hbase | hext
    · have h1 := IsLinKDerivation.ax hder' (Or.inl hbase) hk
      have h2 := IsLinKDerivation.weak h1 List.mem_cons_self (linKWeak_of_subset Finset.subset_union_left) hkCM
      refine ⟨(C ∪ M) :: C :: σ', h2, ?_, by simp; omega⟩
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem' L hm))
    · have h1 := IsLinKDerivation.ax hder' (Or.inr ⟨C, hext, rfl⟩) hkCM
      refine ⟨(C ∪ M) :: σ', h1, ?_, by simp; omega⟩
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem' L hm)
  | @cut π C D R hπ hC hD hcut hk ih =>
    rcases ih with ⟨σ', hder', hmem', hlen'⟩
    rcases hcut with ⟨T, hTC, hneg, rfl⟩
    let R' : LinKLine V := (C ∪ M).erase T ∪ ((D ∪ M) \ T.image (fun e => ({negLinEq e} : LinTerm V)))
    have hcut' : IsLinKCut (C ∪ M) (D ∪ M) R' :=
      ⟨T, Finset.mem_union_left _ hTC, fun e he => Finset.mem_union_left _ (hneg e he), rfl⟩
    have hRsub : R' ⊆ (C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))) ∪ M := by
      intro S hS
      simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff] at hS ⊢
      rcases hS with ⟨hne, hSC | hSM⟩ | ⟨hSD | hSM, hnot⟩
      · exact Or.inl (Or.inl ⟨hne, hSC⟩)
      · exact Or.inr hSM
      · exact Or.inl (Or.inr ⟨hSD, hnot⟩)
      · exact Or.inr hSM
    have hkRM : ∀ S ∈ (C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))) ∪ M, S.card ≤ k :=
      fun S hS => (Finset.mem_union.mp hS).elim (hk S) (hMk S)
    have h1 := IsLinKDerivation.cut hder' (hmem' C hC) (hmem' D hD) hcut' (fun S hS => hkRM S (hRsub hS))
    have h2 := IsLinKDerivation.weak h1 List.mem_cons_self (linKWeak_of_subset hRsub) hkRM
    refine ⟨((C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))) ∪ M) :: R' :: σ',
      h2, ?_, by simp; omega⟩
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem' L hm))
  | @andIntro π C D R hπ hC hD hand hk ih =>
    rcases ih with ⟨σ', hder', hmem', hlen'⟩
    rcases hand with ⟨T1, T2, h1C, h2D, rfl⟩
    let R' : LinKLine V := ((C ∪ M).erase T1 ∪ (D ∪ M).erase T2) ∪ {T1 ∪ T2}
    have hand' : IsLinKAndIntro (C ∪ M) (D ∪ M) R' :=
      ⟨T1, T2, Finset.mem_union_left _ h1C, Finset.mem_union_left _ h2D, rfl⟩
    have hRsub : R' ⊆ ((C.erase T1 ∪ D.erase T2) ∪ {T1 ∪ T2}) ∪ M := by
      intro S hS
      simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hS ⊢
      rcases hS with ((⟨hne, hSC | hSM⟩ | ⟨hne, hSD | hSM⟩) | rfl)
      · exact Or.inl (Or.inl (Or.inl ⟨hne, hSC⟩))
      · exact Or.inr hSM
      · exact Or.inl (Or.inl (Or.inr ⟨hne, hSD⟩))
      · exact Or.inr hSM
      · exact Or.inl (Or.inr rfl)
    have hkRM : ∀ S ∈ ((C.erase T1 ∪ D.erase T2) ∪ {T1 ∪ T2}) ∪ M, S.card ≤ k :=
      fun S hS => (Finset.mem_union.mp hS).elim (hk S) (hMk S)
    have h1 := IsLinKDerivation.andIntro hder' (hmem' C hC) (hmem' D hD) hand' (fun S hS => hkRM S (hRsub hS))
    have h2 := IsLinKDerivation.weak h1 List.mem_cons_self (linKWeak_of_subset hRsub) hkRM
    refine ⟨(((C.erase T1 ∪ D.erase T2) ∪ {T1 ∪ T2}) ∪ M) :: R' :: σ', h2, ?_, by simp; omega⟩
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem' L hm))
  | @weak π C D hπ hC hw hk ih =>
    rcases ih with ⟨σ', hder', hmem', hlen'⟩
    have hw' : IsLinKWeakening (C ∪ M) (D ∪ M) := by
      intro T hT
      rcases Finset.mem_union.mp hT with hTC | hTM
      · rcases hw T hTC with ⟨S, hSD, himp⟩ | hb
        · exact Or.inl ⟨S, Finset.mem_union_left _ hSD, himp⟩
        · exact Or.inr fun a ha => by
            rcases hb a ha with ⟨q, hq, hqa⟩
            exact ⟨q, Finset.mem_union_left _ hq, hqa⟩
      · exact Or.inl ⟨T, Finset.mem_union_right _ hTM, fun _ ha => ha⟩
    have hkDM : ∀ T ∈ D ∪ M, T.card ≤ k := fun T hT =>
      (Finset.mem_union.mp hT).elim (hk T) (hMk T)
    have h1 := IsLinKDerivation.weak hder' (hmem' C hC) hw' hkDM
    refine ⟨(D ∪ M) :: σ', h1, ?_, by simp; omega⟩
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hmem' L hm)

inductive PDT (V : Type)
  | leaf (val : Bool)
  | branch (f : Finset V) (lo hi : PDT V)

private def PDT.depth {V : Type} : PDT V → ℕ
  | .leaf _ => 0
  | .branch _ lo hi => 1 + max lo.depth hi.depth

private noncomputable def PDT.eval {V : Type} (x : V → Bool) : PDT V → Bool
  | .leaf b => b
  | .branch f lo hi =>
      @ite Bool (LinEqSat x (f, true)) (Classical.propDecidable _) (hi.eval x) (lo.eval x)

private def PDT.leaves {V : Type} [DecidableEq V] (val : Bool) (P : LinTerm V) : PDT V → LinKLine V
  | .leaf b => if b = val then {P} else ∅
  | .branch f lo hi => lo.leaves val (insert (f, false) P) ∪ hi.leaves val (insert (f, true) P)

private lemma PDT.leaves_card_le {V : Type} [DecidableEq V] (t : PDT V) (val : Bool) :
    ∀ (P : LinTerm V) (T : LinTerm V), T ∈ t.leaves val P → T.card ≤ P.card + t.depth := by
  induction t with
  | leaf b =>
    intro P T hT
    dsimp only [PDT.leaves, PDT.depth] at hT ⊢
    split_ifs at hT with h
    · rw [Finset.mem_singleton.mp hT]; omega
    · cases hT
  | branch f lo hi ihlo ihhi =>
    intro P T hT
    dsimp only [PDT.leaves, PDT.depth] at hT ⊢
    rcases Finset.mem_union.mp hT with h | h
    · have := ihlo (insert (f, false) P) T h
      have hcard := Finset.card_insert_le (f, false) P
      omega
    · have := ihhi (insert (f, true) P) T h
      have hcard := Finset.card_insert_le (f, true) P
      omega

private lemma PDT.leaves_sound {V : Type} [DecidableEq V] (t : PDT V) (val : Bool) :
    ∀ (P : LinTerm V) (x : V → Bool) (T : LinTerm V),
      T ∈ t.leaves val P → LinTermSat x T → t.eval x = val ∧ LinTermSat x P := by
  induction t with
  | leaf b =>
    intro P x T hT hsat
    dsimp only [PDT.leaves, PDT.eval] at hT ⊢
    split_ifs at hT with h
    · rw [Finset.mem_singleton.mp hT] at hsat; exact ⟨h, hsat⟩
    · cases hT
  | branch f lo hi ihlo ihhi =>
    intro P x T hT hsat
    dsimp only [PDT.leaves, PDT.eval] at hT ⊢
    rcases Finset.mem_union.mp hT with h | h
    · rcases ihlo (insert (f, false) P) x T h hsat with ⟨hev, hP⟩
      have hfls : LinEqSat x (f, false) := hP _ (Finset.mem_insert_self _ _)
      have hnot : ¬ LinEqSat x (f, true) := by
        have := (linEqSat_neg x (f, true)).mp hfls; exact this
      rw [if_neg hnot]
      exact ⟨hev, fun q hq => hP q (Finset.mem_insert_of_mem hq)⟩
    · rcases ihhi (insert (f, true) P) x T h hsat with ⟨hev, hP⟩
      have htr : LinEqSat x (f, true) := hP _ (Finset.mem_insert_self _ _)
      rw [if_pos htr]
      exact ⟨hev, fun q hq => hP q (Finset.mem_insert_of_mem hq)⟩

private lemma branch_list_build {V : Type} [DecidableEq V] (d : ℕ) (g : (V → Bool) → Bool) :
    ∀ (l : List (Finset V)) (P : LinTerm V),
      (∀ P' : LinTerm V, P ⊆ P' →
        (∀ f ∈ l, (f, false) ∈ P' ∨ (f, true) ∈ P') →
        ∃ t : PDT V, t.depth ≤ d ∧ ∀ x, LinTermSat x P' → t.eval x = g x) →
      ∃ t : PDT V, t.depth ≤ l.length + d ∧ ∀ x, LinTermSat x P → t.eval x = g x := by
  intro l
  induction l with
  | nil =>
    intro P hleaf
    rcases hleaf P subset_rfl (by simp) with ⟨t, hd, hev⟩
    exact ⟨t, by simpa using hd, hev⟩
  | cons f rest ih =>
    intro P hleaf
    have hlo : ∃ tlo : PDT V, tlo.depth ≤ rest.length + d ∧
        ∀ x, LinTermSat x (insert (f, false) P) → tlo.eval x = g x :=
      ih (insert (f, false) P) fun P' hsub hall => hleaf P'
        ((Finset.subset_insert _ _).trans hsub) fun f' hf' => by
          rcases List.mem_cons.mp hf' with rfl | hm
          · exact Or.inl (hsub (Finset.mem_insert_self _ _))
          · exact hall f' hm
    have hhi : ∃ thi : PDT V, thi.depth ≤ rest.length + d ∧
        ∀ x, LinTermSat x (insert (f, true) P) → thi.eval x = g x :=
      ih (insert (f, true) P) fun P' hsub hall => hleaf P'
        ((Finset.subset_insert _ _).trans hsub) fun f' hf' => by
          rcases List.mem_cons.mp hf' with rfl | hm
          · exact Or.inr (hsub (Finset.mem_insert_self _ _))
          · exact hall f' hm
    rcases hlo with ⟨tlo, hdlo, hevlo⟩
    rcases hhi with ⟨thi, hdhi, hevhi⟩
    refine ⟨PDT.branch f tlo thi, ?_, ?_⟩
    · dsimp only [PDT.depth]; simp only [List.length_cons]; omega
    · intro x hx
      dsimp only [PDT.eval]
      split_ifs with hft
      · refine hevhi x fun q hq => ?_
        rcases Finset.mem_insert.mp hq with rfl | hm
        · exact hft
        · exact hx q hm
      · refine hevlo x fun q hq => ?_
        rcases Finset.mem_insert.mp hq with rfl | hm
        · exact (linEqSat_neg x (f, true)).mpr hft
        · exact hx q hm

private lemma exists_pdt_aux {V : Type} [Fintype V] [DecidableEq V] (g : (V → Bool) → Bool)
    (q : ℕ) : ∀ (p : ℕ) (P : LinTerm V),
    (∀ x, LinTermSat x P → g x = true →
      ∃ T : LinTerm V, T.card ≤ q ∧ LinTermSat x T ∧ ∀ y, LinTermSat y P → LinTermSat y T → g y = true) →
    (∀ x, LinTermSat x P → g x = false →
      ∃ T : LinTerm V, T.card ≤ p ∧ LinTermSat x T ∧ ∀ y, LinTermSat y P → LinTermSat y T → g y = false) →
    ∃ t : PDT V, t.depth ≤ p * q ∧ ∀ x, LinTermSat x P → t.eval x = g x := by
  classical
  intro p
  induction p with
  | zero =>
    intro P _ h0
    by_cases hex : ∃ x, LinTermSat x P ∧ g x = false
    · rcases hex with ⟨x0, hx0P, hx0f⟩
      rcases h0 x0 hx0P hx0f with ⟨T, hTc, _, hTimp⟩
      have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hTc)
      refine ⟨PDT.leaf false, by simp [PDT.depth], fun x hxP => ?_⟩
      dsimp only [PDT.eval]
      exact (hTimp x hxP (by rw [hTe]; intro r hr; cases hr)).symm
    · push Not at hex
      refine ⟨PDT.leaf true, by simp [PDT.depth], fun x hxP => ?_⟩
      dsimp only [PDT.eval]
      exact (Bool.eq_true_of_not_eq_false (hex x hxP)).symm
  | succ p ih =>
    intro P h1 h0
    by_cases hallf : ∀ x, LinTermSat x P → g x = false
    · refine ⟨PDT.leaf false, by simp [PDT.depth], fun x hxP => (hallf x hxP).symm⟩
    · push Not at hallf
      rcases hallf with ⟨x1, hx1P, hx1ne⟩
      have hx1t : g x1 = true := Bool.eq_true_of_not_eq_false hx1ne
      rcases h1 x1 hx1P hx1t with ⟨T1, hT1c, hx1T1, hT1imp⟩
      let l : List (Finset V) := T1.toList.map Prod.fst
      have hl_len : l.length ≤ q := by
        dsimp only [l]; rw [List.length_map, Finset.length_toList]; exact hT1c
      have hbl : ∃ t : PDT V, t.depth ≤ l.length + p * q ∧ ∀ x, LinTermSat x P → t.eval x = g x := by
        refine branch_list_build (p * q) g l P fun P' hPP' hfix => ?_
        by_cases hallt : ∀ x, LinTermSat x P' → g x = true
        · exact ⟨PDT.leaf true, Nat.zero_le _, fun x hx => (hallt x hx).symm⟩
        · refine ih P' (fun x hxP' hxt => ?_) (fun x hxP' hxf => ?_)
          · rcases h1 x (fun e he => hxP' e (hPP' he)) hxt with ⟨T, hTc, hxT, hTimp⟩
            exact ⟨T, hTc, hxT, fun y hyP' hyT => hTimp y (fun e he => hyP' e (hPP' he)) hyT⟩
          · rcases h0 x (fun e he => hxP' e (hPP' he)) hxf with ⟨T0, hT0c, hxT0, hT0imp⟩
            have hunsat : ∀ a : V → Bool, LinTermSat a (P ∪ T1 ∪ T0) → ∃ r ∈ (∅ : Finset (LinEq V)), LinEqSat a r := by
              intro a ha
              have haP : LinTermSat a P := fun e he => ha e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
              have haT1 : LinTermSat a T1 := fun e he => ha e (Finset.mem_union_left _ (Finset.mem_union_right _ he))
              have haT0 : LinTermSat a T0 := fun e he => ha e (Finset.mem_union_right _ he)
              have ht := hT1imp a haP haT1
              have hf := hT0imp a haP haT0
              rw [ht] at hf; cases hf
            rcases H.LinKPlan.term_alt (P ∪ T1 ∪ T0) ∅ hunsat with ⟨J, hJ, I, hI, hid⟩
            have hJe : J = ∅ := Finset.subset_empty.mp hJ
            rw [hJe, Finset.sum_empty, add_zero] at hid
            let I1 : Finset (LinEq V) := I ∩ (P ∪ T1)
            let I0 : Finset (LinEq V) := I \ (P ∪ T1)
            have hdisj_I : Disjoint I1 I0 :=
              Finset.disjoint_left.mpr fun e h1 h0 => (Finset.mem_sdiff.mp h0).2 (Finset.mem_inter.mp h1).2
            have hun_I : I1 ∪ I0 = I := by
              ext e; simp only [I1, I0, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
              constructor
              · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
              · intro h; exact if hp : e ∈ P ∨ e ∈ T1 then Or.inl ⟨h, hp⟩ else Or.inr ⟨h, hp⟩
            have hI_split : ∑ e ∈ I1, (H.Helpers.eqPoly e + 1) + ∑ e ∈ I0, (H.Helpers.eqPoly e + 1) = 1 := by
              rw [← Finset.sum_union hdisj_I, hun_I]; exact hid
            have hI0_sub : I0 ⊆ T0 := by
              intro e he
              have he1 := (Finset.mem_sdiff.mp he).1
              have he2 := (Finset.mem_sdiff.mp he).2
              rcases Finset.mem_union.mp (hI he1) with h | h
              · exact (he2 h).elim
              · exact h
            have hI0_ne : I0.Nonempty := by
              by_contra hne
              rw [Finset.not_nonempty_iff_eq_empty] at hne
              rw [hne, Finset.sum_empty, add_zero] at hI_split
              have hev1 := congrArg (eval (toZ2 x1)) hI_split
              rw [map_sum, map_one] at hev1
              have hzero : ∑ e ∈ I1, eval (toZ2 x1) (H.Helpers.eqPoly e + 1) = 0 := by
                refine Finset.sum_eq_zero fun e he => ?_
                have hePT := (Finset.mem_inter.mp he).2
                have hsat : LinEqSat x1 e := by
                  rcases Finset.mem_union.mp hePT with hP | hT1
                  · exact hx1P e hP
                  · exact hx1T1 e hT1
                exact (eval_eqPoly_add_one_eq_zero_iff x1 e).mpr hsat
              rw [hzero] at hev1
              exact zero_ne_one hev1
            rcases hI0_ne with ⟨e0, he0I0⟩
            have he0T0 : e0 ∈ T0 := hI0_sub he0I0
            refine ⟨T0.erase e0, ?_, fun e he => hxT0 e (Finset.mem_of_mem_erase he), fun y hyP' hyTe => ?_⟩
            · have := Finset.card_erase_of_mem he0T0; omega
            · have heq_I1 : ∀ e ∈ I1, eval (toZ2 y) (H.Helpers.eqPoly e + 1) = eval (toZ2 x) (H.Helpers.eqPoly e + 1) := by
                intro e he
                have hePT := (Finset.mem_inter.mp he).2
                have hdec : e ∈ P' ∨ negLinEq e ∈ P' := by
                  rcases Finset.mem_union.mp hePT with hP | hT1
                  · exact Or.inl (hPP' hP)
                  · have hfmem : e.1 ∈ l := List.mem_map.mpr ⟨e, Finset.mem_toList.mpr hT1, rfl⟩
                    rcases hfix e.1 hfmem with hf | ht
                    · rcases e with ⟨f, b⟩; cases b
                      · exact Or.inl hf
                      · exact Or.inr hf
                    · rcases e with ⟨f, b⟩; cases b
                      · exact Or.inr ht
                      · exact Or.inl ht
                rcases hdec with hin | hneg
                · have hx1 := (eval_eqPoly_add_one_eq_zero_iff x e).mpr (hxP' e hin)
                  have hy1 := (eval_eqPoly_add_one_eq_zero_iff y e).mpr (hyP' e hin)
                  rw [hx1, hy1]
                · have hnx : ¬ LinEqSat x e := (linEqSat_neg x e).mp (hxP' _ hneg)
                  have hny : ¬ LinEqSat y e := (linEqSat_neg y e).mp (hyP' _ hneg)
                  have hxz : eval (toZ2 x) (H.Helpers.eqPoly e + 1) ≠ 0 :=
                    fun h => hnx ((eval_eqPoly_add_one_eq_zero_iff x e).mp h)
                  have hyz : eval (toZ2 y) (H.Helpers.eqPoly e + 1) ≠ 0 :=
                    fun h => hny ((eval_eqPoly_add_one_eq_zero_iff y e).mp h)
                  rcases H.Helpers.zmod2_cases (eval (toZ2 x) (H.Helpers.eqPoly e + 1)) with hx0 | hx1 <;>
                    rcases H.Helpers.zmod2_cases (eval (toZ2 y) (H.Helpers.eqPoly e + 1)) with hy0 | hy1 <;>
                    simp_all
              have hx_sum : eval (toZ2 x) (∑ e ∈ I1, (H.Helpers.eqPoly e + 1)) +
                  eval (toZ2 x) (∑ e ∈ I0, (H.Helpers.eqPoly e + 1)) = 1 := by
                have := congrArg (eval (toZ2 x)) hI_split; rwa [map_add, map_one] at this
              have hy_sum : eval (toZ2 y) (∑ e ∈ I1, (H.Helpers.eqPoly e + 1)) +
                  eval (toZ2 y) (∑ e ∈ I0, (H.Helpers.eqPoly e + 1)) = 1 := by
                have := congrArg (eval (toZ2 y)) hI_split; rwa [map_add, map_one] at this
              have hx_I0 : eval (toZ2 x) (∑ e ∈ I0, (H.Helpers.eqPoly e + 1)) = 0 := by
                rw [map_sum]; exact Finset.sum_eq_zero fun e he =>
                  (eval_eqPoly_add_one_eq_zero_iff x e).mpr (hxT0 e (hI0_sub he))
              have hI1_eq : eval (toZ2 y) (∑ e ∈ I1, (H.Helpers.eqPoly e + 1)) =
                  eval (toZ2 x) (∑ e ∈ I1, (H.Helpers.eqPoly e + 1)) := by
                rw [map_sum, map_sum]; exact Finset.sum_congr rfl heq_I1
              rw [hx_I0, add_zero] at hx_sum
              rw [hI1_eq, hx_sum] at hy_sum
              have hy_I0 : eval (toZ2 y) (∑ e ∈ I0, (H.Helpers.eqPoly e + 1)) = 0 := by
                generalize eval (toZ2 y) (∑ e ∈ I0, (H.Helpers.eqPoly e + 1)) = z at hy_sum
                revert z hy_sum; decide
              rw [map_sum, ← Finset.add_sum_erase _ _ he0I0] at hy_I0
              have hy_rest : ∑ e ∈ I0.erase e0, eval (toZ2 y) (H.Helpers.eqPoly e + 1) = 0 := by
                refine Finset.sum_eq_zero fun e he => ?_
                have hne := (Finset.mem_erase.mp he).1
                have hmem := hI0_sub (Finset.mem_erase.mp he).2
                exact (eval_eqPoly_add_one_eq_zero_iff y e).mpr (hyTe e (Finset.mem_erase.mpr ⟨hne, hmem⟩))
              rw [hy_rest, add_zero] at hy_I0
              have hye0 : LinEqSat y e0 := (eval_eqPoly_add_one_eq_zero_iff y e0).mp hy_I0
              have hyT0 : LinTermSat y T0 := fun e he => by
                by_cases h : e = e0
                · exact h ▸ hye0
                · exact hyTe e (Finset.mem_erase.mpr ⟨h, he⟩)
              exact hT0imp y (fun e he => hyP' e (hPP' he)) hyT0
      rcases hbl with ⟨t, htd, htev⟩
      refine ⟨t, ?_, htev⟩
      calc t.depth ≤ l.length + p * q := htd
        _ ≤ q + p * q := Nat.add_le_add_right hl_len _
        _ = (p + 1) * q := by ring

private lemma exists_pdt_of_certs {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → Bool) → Bool) (p q : ℕ)
    (hcert : ∀ x : V → Bool, ∃ T : LinTerm V,
      T.card ≤ (if g x then q else p) ∧ LinTermSat x T ∧
      ∀ y : V → Bool, LinTermSat y T → g y = g x) :
    ∃ t : PDT V, t.depth ≤ p * q ∧ ∀ x : V → Bool, t.eval x = g x := by
  rcases exists_pdt_aux g q p ∅
    (fun x _ hxt => by
      rcases hcert x with ⟨T, hTc, hxT, himp⟩
      rw [hxt] at hTc himp; simp only [↓reduceIte] at hTc
      exact ⟨T, hTc, hxT, fun y _ hyT => himp y hyT⟩)
    (fun x _ hxf => by
      rcases hcert x with ⟨T, hTc, hxT, himp⟩
      rw [hxf] at hTc himp; simp only [Bool.false_eq_true, ↓reduceIte] at hTc
      exact ⟨T, hTc, hxT, fun y _ hyT => himp y hyT⟩) with ⟨t, hd, hev⟩
  exact ⟨t, hd, fun x => hev x (fun _ h => (Finset.notMem_empty _ h).elim)⟩

private lemma pdt_resolve {V : Type} [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    {F : Set (LinKLine V)} (Base L1 L2 : LinKLine V) (hBk : ∀ T ∈ Base, T.card ≤ k)
    (t : PDT V) :
    ∀ (π : List (LinKLine V)) (P : LinTerm V),
      IsLinKDerivation k IsLinKWeakening F π → L1 ∈ π → L2 ∈ π →
      (∀ T ∈ L1, T ∈ Base ∨ ∀ a : V → Bool, LinTermSat a T → LinTermSat a P → t.eval a = true) →
      (∀ T ∈ L2, T ∈ Base ∨ ∀ a : V → Bool, LinTermSat a T → LinTermSat a P → t.eval a = false) →
      ∃ ext : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F (ext ++ π) ∧
        (Base ∪ P.image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π ∧
        ext.length ≤ 3 * 2 ^ t.depth - 1 := by
  induction t with
  | leaf b =>
    intro π P hπ hL1 hL2 h1 h2
    let Target : LinKLine V := Base ∪ P.image (fun q => ({negLinEq q} : LinTerm V))
    have hTk : ∀ T ∈ Target, T.card ≤ k := by
      intro T hT
      rcases Finset.mem_union.mp hT with hB | hP
      · exact hBk T hB
      · rcases Finset.mem_image.mp hP with ⟨q, _, rfl⟩; simpa using hk
    cases b
    · have hw : IsLinKWeakening L1 Target := by
        intro T hT
        rcases h1 T hT with hB | himp
        · exact Or.inl ⟨T, Finset.mem_union_left _ hB, fun _ h => h⟩
        · refine Or.inr fun a ha => ?_
          by_contra hno; push Not at hno
          have hP : LinTermSat a P := fun q hq => by
            by_contra hnq
            exact hno (negLinEq q) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
              ((linEqSat_neg a q).mpr hnq)
          have htr := himp a ha hP
          dsimp only [PDT.eval] at htr; cases htr
      exact ⟨[Target], IsLinKDerivation.weak hπ hL1 hw hTk, List.mem_cons_self, by simp [PDT.depth]⟩
    · have hw : IsLinKWeakening L2 Target := by
        intro T hT
        rcases h2 T hT with hB | himp
        · exact Or.inl ⟨T, Finset.mem_union_left _ hB, fun _ h => h⟩
        · refine Or.inr fun a ha => ?_
          by_contra hno; push Not at hno
          have hP : LinTermSat a P := fun q hq => by
            by_contra hnq
            exact hno (negLinEq q) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
              ((linEqSat_neg a q).mpr hnq)
          have hfls := himp a ha hP
          dsimp only [PDT.eval] at hfls; cases hfls
      exact ⟨[Target], IsLinKDerivation.weak hπ hL2 hw hTk, List.mem_cons_self, by simp [PDT.depth]⟩
  | branch f lo hi ihlo ihhi =>
    intro π P hπ hL1 hL2 h1 h2
    have hlo1 : ∀ T ∈ L1, T ∈ Base ∨ ∀ a, LinTermSat a T → LinTermSat a (insert (f, false) P) → lo.eval a = true := by
      intro T hT
      rcases h1 T hT with hB | himp
      · exact Or.inl hB
      · refine Or.inr fun a ha hP => ?_
        have hfls : LinEqSat a (f, false) := hP _ (Finset.mem_insert_self _ _)
        have hnot : ¬ LinEqSat a (f, true) := (linEqSat_neg a (f, true)).mp hfls
        have htr := himp a ha (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        dsimp only [PDT.eval] at htr; rwa [if_neg hnot] at htr
    have hlo2 : ∀ T ∈ L2, T ∈ Base ∨ ∀ a, LinTermSat a T → LinTermSat a (insert (f, false) P) → lo.eval a = false := by
      intro T hT
      rcases h2 T hT with hB | himp
      · exact Or.inl hB
      · refine Or.inr fun a ha hP => ?_
        have hfls : LinEqSat a (f, false) := hP _ (Finset.mem_insert_self _ _)
        have hnot : ¬ LinEqSat a (f, true) := (linEqSat_neg a (f, true)).mp hfls
        have hfl := himp a ha (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        dsimp only [PDT.eval] at hfl; rwa [if_neg hnot] at hfl
    rcases ihlo π (insert (f, false) P) hπ hL1 hL2 hlo1 hlo2 with ⟨ext1, hder1, hmem1, hlen1⟩
    have hhi1 : ∀ T ∈ L1, T ∈ Base ∨ ∀ a, LinTermSat a T → LinTermSat a (insert (f, true) P) → hi.eval a = true := by
      intro T hT
      rcases h1 T hT with hB | himp
      · exact Or.inl hB
      · refine Or.inr fun a ha hP => ?_
        have htrf : LinEqSat a (f, true) := hP _ (Finset.mem_insert_self _ _)
        have htr := himp a ha (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        dsimp only [PDT.eval] at htr; rwa [if_pos htrf] at htr
    have hhi2 : ∀ T ∈ L2, T ∈ Base ∨ ∀ a, LinTermSat a T → LinTermSat a (insert (f, true) P) → hi.eval a = false := by
      intro T hT
      rcases h2 T hT with hB | himp
      · exact Or.inl hB
      · refine Or.inr fun a ha hP => ?_
        have htrf : LinEqSat a (f, true) := hP _ (Finset.mem_insert_self _ _)
        have hfl := himp a ha (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        dsimp only [PDT.eval] at hfl; rwa [if_pos htrf] at hfl
    rcases ihhi (ext1 ++ π) (insert (f, true) P) hder1 (List.mem_append_right _ hL1)
      (List.mem_append_right _ hL2) hhi1 hhi2 with ⟨ext2, hder2, hmem2, hlen2⟩
    let M : LinKLine V := Base ∪ P.image (fun q => ({negLinEq q} : LinTerm V))
    have hMk : ∀ T ∈ M, T.card ≤ k := fun T hT => by
      rcases Finset.mem_union.mp hT with hB | hP
      · exact hBk T hB
      · rcases Finset.mem_image.mp hP with ⟨q, _, rfl⟩; simpa using hk
    have hm1 : M ∪ {({(f, true)} : LinTerm V)} ∈ ext2 ++ ext1 ++ π := by
      have heq : Base ∪ (insert (f, false) P).image (fun q => ({negLinEq q} : LinTerm V)) =
          M ∪ {({(f, true)} : LinTerm V)} := by
        rw [Finset.image_insert]
        dsimp only [M, negLinEq]
        ext T; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Bool.not_false]
        tauto
      rw [← heq, List.append_assoc]; exact List.mem_append_right _ hmem1
    have hm2 : M ∪ {({(f, false)} : LinTerm V)} ∈ ext2 ++ ext1 ++ π := by
      have heq : Base ∪ (insert (f, true) P).image (fun q => ({negLinEq q} : LinTerm V)) =
          M ∪ {({(f, false)} : LinTerm V)} := by
        rw [Finset.image_insert]
        dsimp only [M, negLinEq]
        ext T; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Bool.not_true]
        tauto
      rw [← heq, List.append_assoc]; exact hmem2
    rw [← List.append_assoc] at hder2
    rcases linK_derive_cut_eq hder2 M hMk f hm1 hm2 with ⟨ext3, hder3, hmem3, hlen3⟩
    refine ⟨ext3 ++ ext2 ++ ext1, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hder3
    · simpa [List.append_assoc] using hmem3
    · simp only [List.length_append, PDT.depth]
      have h1pow : 2 ^ lo.depth ≤ 2 ^ max lo.depth hi.depth := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have h2pow : 2 ^ hi.depth ≤ 2 ^ max lo.depth hi.depth := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hpos : 1 ≤ 2 ^ max lo.depth hi.depth := Nat.one_le_pow _ _ (by omega)
      have hp : 2 ^ (1 + max lo.depth hi.depth) = 2 * 2 ^ max lo.depth hi.depth := by
        rw [Nat.add_comm, pow_succ, mul_comm]
      omega

private lemma derive_pdt_branch {V : Type} [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    {F : Set (LinKLine V)} (M : LinKLine V) (hMk : ∀ T ∈ M, T.card ≤ k)
    (g_eval : (V → Bool) → Bool) (val : Bool) (B : ℕ) (P : LinTerm V)
    (L0 : LinKLine V)
    (hfail : ∀ (Q' : LinTerm V) (π' : List (LinKLine V)),
      IsLinKDerivation k IsLinKWeakening F π' → L0 ∈ π' →
      (∀ x, LinTermSat x Q' → g_eval x ≠ val) →
      ∃ ext : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F (ext ++ π') ∧
        (M ∪ (P ∪ Q').image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π' ∧
        ext.length ≤ B)
    (u : PDT V) :
    ∀ (π : List (LinKLine V)) (Q : LinTerm V),
      IsLinKDerivation k IsLinKWeakening F π → L0 ∈ π →
      Q.card + u.depth ≤ k →
      (∀ x, LinTermSat x Q → u.eval x = g_eval x) →
      (∀ T ∈ u.leaves val Q, T ∈ M) →
      ∃ ext : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F (ext ++ π) ∧
        (M ∪ (P ∪ Q).image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π ∧
        ext.length ≤ (B + 3 * k + 3) * 2 ^ u.depth + 2 ^ u.depth - 1 := by
  induction u with
  | leaf b =>
    intro π Q hπ hL0 hQk heq_ev hsub
    by_cases hbv : b = val
    · have hQM : Q ∈ M := hsub Q (by dsimp only [PDT.leaves]; rw [if_pos hbv]; exact Finset.mem_singleton_self _)
      rcases linK_derive_term_taut hk hπ hL0 Q (by dsimp only [PDT.depth] at hQk; omega) with ⟨ext1, hder1, hmem1, hlen1⟩
      let Target : LinKLine V := M ∪ (P ∪ Q).image (fun q => ({negLinEq q} : LinTerm V))
      have hsubT : ({Q} ∪ Q.image (fun q => ({negLinEq q} : LinTerm V))) ⊆ Target := by
        intro T hT
        rcases Finset.mem_union.mp hT with h1 | h2
        · rw [Finset.mem_singleton.mp h1]; exact Finset.mem_union_left _ hQM
        · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hq))
      have hTk : ∀ T ∈ Target, T.card ≤ k := fun T hT => by
        rcases Finset.mem_union.mp hT with hM | hPQ
        · exact hMk T hM
        · rcases Finset.mem_image.mp hPQ with ⟨q, _, rfl⟩; simpa using hk
      have hder2 := IsLinKDerivation.weak hder1 hmem1 (linKWeak_of_subset hsubT) hTk
      refine ⟨Target :: ext1, hder2, List.mem_cons_self, ?_⟩
      dsimp only [PDT.depth] at hQk ⊢; simp only [List.length_cons]; omega
    · rcases hfail Q π hπ hL0 (fun x hx => by rw [← heq_ev x hx]; exact hbv) with ⟨ext1, hder1, hmem1, hlen1⟩
      refine ⟨ext1, hder1, hmem1, ?_⟩
      dsimp only [PDT.depth]; omega
  | branch f lo hi ihlo ihhi =>
    intro π Q hπ hL0 hQk heq_ev hsub
    have hQk_lo : (insert (f, false) Q).card + lo.depth ≤ k := by
      have := Finset.card_insert_le (f, false) Q; dsimp only [PDT.depth] at hQk; omega
    have hQk_hi : (insert (f, true) Q).card + hi.depth ≤ k := by
      have := Finset.card_insert_le (f, true) Q; dsimp only [PDT.depth] at hQk; omega
    have hev_lo : ∀ x, LinTermSat x (insert (f, false) Q) → lo.eval x = g_eval x := by
      intro x hx
      have hfls : LinEqSat x (f, false) := hx _ (Finset.mem_insert_self _ _)
      have hnot : ¬ LinEqSat x (f, true) := (linEqSat_neg x (f, true)).mp hfls
      have h := heq_ev x (fun q hq => hx q (Finset.mem_insert_of_mem hq))
      dsimp only [PDT.eval] at h; rwa [if_neg hnot] at h
    have hev_hi : ∀ x, LinTermSat x (insert (f, true) Q) → hi.eval x = g_eval x := by
      intro x hx
      have htr : LinEqSat x (f, true) := hx _ (Finset.mem_insert_self _ _)
      have h := heq_ev x (fun q hq => hx q (Finset.mem_insert_of_mem hq))
      dsimp only [PDT.eval] at h; rwa [if_pos htr] at h
    have hsub_lo : ∀ T ∈ lo.leaves val (insert (f, false) Q), T ∈ M :=
      fun T hT => hsub T (Finset.mem_union_left _ hT)
    have hsub_hi : ∀ T ∈ hi.leaves val (insert (f, true) Q), T ∈ M :=
      fun T hT => hsub T (Finset.mem_union_right _ hT)
    rcases ihlo π (insert (f, false) Q) hπ hL0 hQk_lo hev_lo hsub_lo with ⟨ext1, hder1, hmem1, hlen1⟩
    rcases ihhi (ext1 ++ π) (insert (f, true) Q) hder1 (List.mem_append_right _ hL0) hQk_hi hev_hi hsub_hi with
      ⟨ext2, hder2, hmem2, hlen2⟩
    let Mcur : LinKLine V := M ∪ (P ∪ Q).image (fun q => ({negLinEq q} : LinTerm V))
    have hMcur_k : ∀ T ∈ Mcur, T.card ≤ k := fun T hT => by
      rcases Finset.mem_union.mp hT with hM | hPQ
      · exact hMk T hM
      · rcases Finset.mem_image.mp hPQ with ⟨q, _, rfl⟩; simpa using hk
    have hm1 : Mcur ∪ {({(f, true)} : LinTerm V)} ∈ ext2 ++ ext1 ++ π := by
      have heq : M ∪ (P ∪ insert (f, false) Q).image (fun q => ({negLinEq q} : LinTerm V)) =
          Mcur ∪ {({(f, true)} : LinTerm V)} := by
        rw [Finset.union_insert, Finset.image_insert]
        dsimp only [Mcur, negLinEq]
        ext T; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Bool.not_false]
        tauto
      rw [← heq, List.append_assoc]; exact List.mem_append_right _ hmem1
    have hm2 : Mcur ∪ {({(f, false)} : LinTerm V)} ∈ ext2 ++ ext1 ++ π := by
      have heq : M ∪ (P ∪ insert (f, true) Q).image (fun q => ({negLinEq q} : LinTerm V)) =
          Mcur ∪ {({(f, false)} : LinTerm V)} := by
        rw [Finset.union_insert, Finset.image_insert]
        dsimp only [Mcur, negLinEq]
        ext T; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Bool.not_true]
        tauto
      rw [← heq, List.append_assoc]; exact hmem2
    rw [← List.append_assoc] at hder2
    rcases linK_derive_cut_eq hder2 Mcur hMcur_k f hm1 hm2 with ⟨ext3, hder3, hmem3, hlen3⟩
    refine ⟨ext3 ++ ext2 ++ ext1, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hder3
    · simpa [List.append_assoc] using hmem3
    · simp only [List.length_append, PDT.depth]
      have h1pow : 2 ^ lo.depth ≤ 2 ^ max lo.depth hi.depth := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have h2pow : 2 ^ hi.depth ≤ 2 ^ max lo.depth hi.depth := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hpos : 1 ≤ 2 ^ max lo.depth hi.depth := Nat.one_le_pow _ _ (by omega)
      have hp : 2 ^ (1 + max lo.depth hi.depth) = 2 * 2 ^ max lo.depth hi.depth := by
        rw [Nat.add_comm, pow_succ, mul_comm]
      have hle1 : (B + 3 * k + 3) * 2 ^ lo.depth + 2 ^ lo.depth - 1 ≤
          (B + 3 * k + 3) * 2 ^ max lo.depth hi.depth + 2 ^ max lo.depth hi.depth - 1 := by
        have := Nat.mul_le_mul_left (B + 3 * k + 3) h1pow; omega
      have hle2 : (B + 3 * k + 3) * 2 ^ hi.depth + 2 ^ hi.depth - 1 ≤
          (B + 3 * k + 3) * 2 ^ max lo.depth hi.depth + 2 ^ max lo.depth hi.depth - 1 := by
        have := Nat.mul_le_mul_left (B + 3 * k + 3) h2pow; omega
      rw [hp]
      have hmul : (B + 3 * k + 3) * (2 * 2 ^ max lo.depth hi.depth) =
          2 * ((B + 3 * k + 3) * 2 ^ max lo.depth hi.depth) := by ring
      omega

private lemma derive_phi_taut_aux {V : Type} [DecidableEq V] {a k : ℕ} (hk : 1 ≤ k)
    (pdt : V ⊕ Fin a → PDT V) (hpdt_d : ∀ w, (pdt w).depth ≤ k)
    {F : Set (LinKLine V)} (E : Clause (V ⊕ Fin a)) (L0 : LinKLine V) :
    let clauseLine : Clause (V ⊕ Fin a) → LinKLine V := fun C => C.biUnion (fun l => (pdt l.1).leaves l.2 ∅)
    ∀ (lits : List (Literal (V ⊕ Fin a))) (P : LinTerm V) (π : List (LinKLine V)),
      IsLinKDerivation k IsLinKWeakening F π → L0 ∈ π →
      (∀ l ∈ lits, l ∈ E) →
      (∀ x : V → Bool, LinTermSat x P → ∃ l ∈ lits, (pdt l.1).eval x = l.2) →
      ∃ ext : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening F (ext ++ π) ∧
        (clauseLine E ∪ P.image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π ∧
        ext.length ≤ (3 * k + 4) * (3 * 2 ^ k) ^ lits.length := by
  intro clauseLine lits
  have hEk : ∀ T ∈ clauseLine E, T.card ≤ k := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨l, _, hTl⟩
    have := PDT.leaves_card_le (pdt l.1) l.2 ∅ T hTl
    have hd := hpdt_d l.1
    simp only [Finset.card_empty, zero_add] at this
    omega
  induction lits with
  | nil =>
    intro P π hπ hL0 _ hcov
    let Target : LinKLine V := clauseLine E ∪ P.image (fun q => ({negLinEq q} : LinTerm V))
    have hTk : ∀ T ∈ Target, T.card ≤ k := fun T hT => by
      rcases Finset.mem_union.mp hT with hM | hP
      · exact hEk T hM
      · rcases Finset.mem_image.mp hP with ⟨q, _, rfl⟩; simpa using hk
    have hw : IsLinKWeakening L0 Target := by
      intro T _
      refine Or.inr fun x _ => ?_
      by_contra hno; push Not at hno
      have hxP : LinTermSat x P := fun q hq => by
        by_contra hnq
        exact hno (negLinEq q) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
          ((linEqSat_neg x q).mpr hnq)
      rcases hcov x hxP with ⟨_, hl, _⟩
      cases hl
    refine ⟨[Target], IsLinKDerivation.weak hπ hL0 hw hTk, List.mem_cons_self, by simp⟩
  | cons l rest ih =>
    intro P π hπ hL0 hlsub hcov
    let B : ℕ := (3 * k + 4) * (3 * 2 ^ k) ^ rest.length
    have hfail : ∀ (Q' : LinTerm V) (π' : List (LinKLine V)),
        IsLinKDerivation k IsLinKWeakening F π' → L0 ∈ π' →
        (∀ x, LinTermSat x Q' → (pdt l.1).eval x ≠ l.2) →
        ∃ ext : List (LinKLine V),
          IsLinKDerivation k IsLinKWeakening F (ext ++ π') ∧
          (clauseLine E ∪ (P ∪ Q').image (fun q => ({negLinEq q} : LinTerm V))) ∈ ext ++ π' ∧
          ext.length ≤ B := by
      intro Q' π' hπ' hL0' hne
      refine ih (P ∪ Q') π' hπ' hL0' (fun l' hl' => hlsub l' (List.mem_cons_of_mem _ hl')) fun x hx => ?_
      have hxP : LinTermSat x P := fun q hq => hx q (Finset.mem_union_left _ hq)
      have hxQ' : LinTermSat x Q' := fun q hq => hx q (Finset.mem_union_right _ hq)
      rcases hcov x hxP with ⟨l', hl', hev⟩
      rcases List.mem_cons.mp hl' with rfl | hrest
      · exact (hne x hxQ' hev).elim
      · exact ⟨l', hrest, hev⟩
    have hlE : l ∈ E := hlsub l List.mem_cons_self
    have hsub_M : ∀ T ∈ (pdt l.1).leaves l.2 ∅, T ∈ clauseLine E :=
      fun T hT => Finset.mem_biUnion.mpr ⟨l, hlE, hT⟩
    rcases derive_pdt_branch hk (clauseLine E) hEk (fun x => (pdt l.1).eval x) l.2 B P L0 hfail
      (pdt l.1) π ∅ hπ hL0 (by simp [hpdt_d l.1]) (fun _ _ => rfl) hsub_M with
      ⟨ext, hder, hmem, hlen⟩
    rw [Finset.union_empty] at hmem
    refine ⟨ext, hder, hmem, ?_⟩
    have hpow_le : 2 ^ (pdt l.1).depth ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (hpdt_d l.1)
    have hB_ge : 3 * k + 4 ≤ B := by
      dsimp only [B]
      have h1 : 1 ≤ (3 * 2 ^ k) ^ rest.length := Nat.one_le_pow _ _ (by positivity)
      nlinarith
    have hstep : (B + 3 * k + 3) * 2 ^ (pdt l.1).depth + 2 ^ (pdt l.1).depth - 1 ≤ (3 * 2 ^ k) * B := by
      have h1 : (B + 3 * k + 3) * 2 ^ (pdt l.1).depth + 2 ^ (pdt l.1).depth = (B + 3 * k + 4) * 2 ^ (pdt l.1).depth := by ring
      have h2 : (B + 3 * k + 4) * 2 ^ (pdt l.1).depth ≤ (2 * B) * 2 ^ k :=
        Nat.mul_le_mul (by omega) hpow_le
      have h3 : (2 * B) * 2 ^ k ≤ (3 * 2 ^ k) * B := by
        calc (2 * B) * 2 ^ k = 2 * (B * 2 ^ k) := by ring
          _ ≤ 3 * (B * 2 ^ k) := Nat.mul_le_mul_right _ (by omega)
          _ = (3 * 2 ^ k) * B := by ring
      omega
    have hpow_succ : (3 * k + 4) * (3 * 2 ^ k) ^ (l :: rest).length = (3 * 2 ^ k) * B := by
      dsimp only [B]; simp only [List.length_cons, pow_succ]; ring
    omega

private def stripMenu {V : Type} [DecidableEq V] {a h : ℕ}
    (C : Clause ((V ⊕ Fin a) ⊕ Fin h)) : Clause (V ⊕ Fin a) :=
  C.biUnion fun l => match l.1 with | Sum.inl w => {(w, l.2)} | Sum.inr _ => ∅

private lemma mem_stripMenu_iff {V : Type} [DecidableEq V] {a h : ℕ}
    (C : Clause ((V ⊕ Fin a) ⊕ Fin h)) (l : Literal (V ⊕ Fin a)) :
    l ∈ stripMenu C ↔ (Sum.inl l.1, l.2) ∈ C := by
  simp only [stripMenu, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨w | u, b⟩, hmem, hl⟩
    · simp only [Finset.mem_singleton] at hl; rcases hl with rfl; exact hmem
    · simp at hl
  · intro hmem
    exact ⟨(Sum.inl l.1, l.2), hmem, Finset.mem_singleton_self _⟩

private lemma stripMenu_card_le {V : Type} [DecidableEq V] {a h : ℕ}
    (C : Clause ((V ⊕ Fin a) ⊕ Fin h)) :
    (stripMenu C).card ≤ (C.filter (fun l => l.1.isLeft)).card := by
  refine Finset.card_le_card_of_injOn (fun l => (Sum.inl l.1, l.2)) ?_ ?_
  · intro l hl
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(mem_stripMenu_iff C l).mp (Finset.mem_coe.mp hl), rfl⟩)
  · intro l1 _ l2 _ heq
    cases l1; cases l2
    simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
    exact Prod.ext heq.1 heq.2

private def isSatByMenu {V : Type} {a h : ℕ} (m : Fin h → Bool)
    (C : Clause ((V ⊕ Fin a) ⊕ Fin h)) : Prop :=
  ∃ u : Fin h, (Sum.inr u, m u) ∈ C

private lemma stripMenu_sat_of_not_menu {V : Type} [DecidableEq V] {a h : ℕ}
    (m : Fin h → Bool) (x : V ⊕ Fin a → Bool) (C : Clause ((V ⊕ Fin a) ⊕ Fin h))
    (hns : ¬ isSatByMenu m C) (hsat : ClauseSat (Sum.elim x m) C) :
    ClauseSat x (stripMenu C) := by
  rcases hsat with ⟨⟨w | u, b⟩, hmem, hval⟩
  · exact ⟨(w, b), (mem_stripMenu_iff C (w, b)).mpr hmem, hval⟩
  · dsimp only [Sum.elim_inr] at hval
    rw [← hval] at hmem
    exact (hns ⟨u, hmem⟩).elim

private lemma translate_menu_derivation {V : Type} [DecidableEq V] {a h k : ℕ} (hk : 1 ≤ k)
    (F : Set (Clause V)) (extra : Set (Clause ((V ⊕ Fin a) ⊕ Fin h)))
    (m : Fin h → Bool) (pdt : V ⊕ Fin a → PDT V)
    (hpdt_d : ∀ w, (pdt w).depth ≤ k)
    (hpdt_inl : ∀ v : V, pdt (Sum.inl v) = PDT.branch {v} (PDT.leaf false) (PDT.leaf true))
    (A : Finset (Clause (V ⊕ Fin a)))
    {π : List (Clause ((V ⊕ Fin a) ⊕ Fin h))}
    (hπ : IsDerivation ((fun cl : Clause V => cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2))) '' F ∪ extra) π)
    (hA : ∀ C ∈ π, C ∈ extra → ¬ isSatByMenu m C → stripMenu C ∈ A) :
    let clauseLine : Clause (V ⊕ Fin a) → LinKLine V := fun C => C.biUnion (fun l => (pdt l.1).leaves l.2 ∅)
    ∃ σ : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening
        ((fun C => linKOfClause C) '' F ∪ clauseLine '' (↑A : Set (Clause (V ⊕ Fin a)))) σ ∧
      (∀ C ∈ π, ¬ isSatByMenu m C → clauseLine (stripMenu C) ∈ σ) ∧
      σ.length ≤ (3 * 2 ^ k) * π.length := by
  classical
  intro clauseLine
  have hcl_k : ∀ C : Clause (V ⊕ Fin a), ∀ T ∈ clauseLine C, T.card ≤ k := by
    intro C T hT
    rcases Finset.mem_biUnion.mp hT with ⟨l, _, hTl⟩
    have := PDT.leaves_card_le (pdt l.1) l.2 ∅ T hTl
    have hd := hpdt_d l.1
    simp only [Finset.card_empty, zero_add] at this
    omega
  have hlift_eq : ∀ C0 : Clause V,
      clauseLine (stripMenu (C0.image (fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2)))) =
      linKOfClause C0 := by
    intro C0
    ext T
    simp only [clauseLine, Finset.mem_biUnion, mem_stripMenu_iff, Finset.mem_image, linKOfClause, linOfClause]
    constructor
    · rintro ⟨⟨lw, lb⟩, ⟨⟨l0v, l0b⟩, hl0, hpair⟩, hTl⟩
      simp only [Prod.mk.injEq, Sum.inl.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      rw [hpdt_inl l0v] at hTl
      cases hb : l0b <;> simp [hb, PDT.leaves] at hTl
      · subst hTl; exact ⟨({l0v}, false), ⟨(l0v, l0b), hl0, by simp [hb]⟩, by ext; simp⟩
      · subst hTl; exact ⟨({l0v}, true), ⟨(l0v, l0b), hl0, by simp [hb]⟩, by ext; simp⟩
    · rintro ⟨q, ⟨l0, hl0, rfl⟩, rfl⟩
      refine ⟨(Sum.inl l0.1, l0.2), ⟨l0, hl0, rfl⟩, ?_⟩
      rw [hpdt_inl l0.1]
      cases l0.2 <;> simp [PDT.leaves]
  induction hπ with
  | nil => exact ⟨[], IsLinKDerivation.nil, by simp, by simp⟩
  | @ax π C hder hC ih =>
    rcases ih (fun C' hC' => hA C' (List.mem_cons_of_mem _ hC')) with ⟨σ, hσ, hmem, hlen⟩
    by_cases hsat : isSatByMenu m C
    · refine ⟨σ, hσ, ?_, by simp only [List.length_cons]; rw [Nat.mul_succ]; omega⟩
      intro C' hC' hns
      rcases List.mem_cons.mp hC' with rfl | hm
      · exact (hns hsat).elim
      · exact hmem C' hm hns
    · have hax_mem : clauseLine (stripMenu C) ∈
          (fun C => linKOfClause C) '' F ∪ clauseLine '' (↑A : Set (Clause (V ⊕ Fin a))) := by
        rcases hC with ⟨C0, hC0, rfl⟩ | hCe
        · left; exact ⟨C0, hC0, (hlift_eq C0).symm⟩
        · right; exact ⟨stripMenu C, Finset.mem_coe.mpr (hA C List.mem_cons_self hCe hsat), rfl⟩
      refine ⟨clauseLine (stripMenu C) :: σ, IsLinKDerivation.ax hσ hax_mem (hcl_k _), ?_, ?_⟩
      · intro C' hC' hns
        rcases List.mem_cons.mp hC' with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmem C' hm hns)
      · simp only [List.length_cons]
        have hpos : 1 ≤ 3 * 2 ^ k := by have := Nat.one_le_pow k 2 (by omega); omega
        nlinarith
  | @res π C D R hder hC hD hres ih =>
    rcases ih (fun C' hC' => hA C' (List.mem_cons_of_mem _ hC')) with ⟨σ, hσ, hmem, hlen⟩
    by_cases hsatR : isSatByMenu m R
    · refine ⟨σ, hσ, ?_, by simp only [List.length_cons]; rw [Nat.mul_succ]; omega⟩
      intro C' hC' hns
      rcases List.mem_cons.mp hC' with rfl | hm
      · exact (hns hsatR).elim
      · exact hmem C' hm hns
    · rcases hres with ⟨w, hwC, hwD, rfl⟩
      rcases w with z | u
      · have hnsC : ¬ isSatByMenu m C := by
          rintro ⟨u, hu⟩
          refine hsatR ⟨u, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hu⟩)⟩
          intro h; cases h
        have hnsD : ¬ isSatByMenu m D := by
          rintro ⟨u, hu⟩
          refine hsatR ⟨u, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hu⟩)⟩
          intro h; cases h
        let Base := clauseLine (stripMenu (C.erase (Sum.inl z, true) ∪ D.erase (Sum.inl z, false)))
        have h1 : ∀ T ∈ clauseLine (stripMenu C), T ∈ Base ∨
            ∀ a : V → Bool, LinTermSat a T → LinTermSat a ∅ → (pdt z).eval a = true := by
          intro T hT
          rcases Finset.mem_biUnion.mp hT with ⟨l, hlC, hTl⟩
          by_cases hlz : l = (z, true)
          · subst hlz
            exact Or.inr fun a ha _ => (PDT.leaves_sound (pdt z) true ∅ a T hTl ha).1
          · left
            refine Finset.mem_biUnion.mpr ⟨l, ?_, hTl⟩
            rw [mem_stripMenu_iff] at hlC ⊢
            refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hlC⟩)
            intro heq; apply hlz
            cases l; simp only [Prod.mk.injEq, Sum.inl.injEq] at heq; exact Prod.ext heq.1 heq.2
        have h2 : ∀ T ∈ clauseLine (stripMenu D), T ∈ Base ∨
            ∀ a : V → Bool, LinTermSat a T → LinTermSat a ∅ → (pdt z).eval a = false := by
          intro T hT
          rcases Finset.mem_biUnion.mp hT with ⟨l, hlD, hTl⟩
          by_cases hlz : l = (z, false)
          · subst hlz
            exact Or.inr fun a ha _ => (PDT.leaves_sound (pdt z) false ∅ a T hTl ha).1
          · left
            refine Finset.mem_biUnion.mpr ⟨l, ?_, hTl⟩
            rw [mem_stripMenu_iff] at hlD ⊢
            refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hlD⟩)
            intro heq; apply hlz
            cases l; simp only [Prod.mk.injEq, Sum.inl.injEq] at heq; exact Prod.ext heq.1 heq.2
        rcases pdt_resolve hk Base (clauseLine (stripMenu C)) (clauseLine (stripMenu D))
          (hcl_k _) (pdt z) σ ∅ hσ (hmem C hC hnsC) (hmem D hD hnsD) h1 h2 with
          ⟨ext, hder', hmem', hlen'⟩
        simp only [Finset.image_empty, Finset.union_empty] at hmem'
        refine ⟨ext ++ σ, hder', ?_, ?_⟩
        · intro C' hC' hns
          rcases List.mem_cons.mp hC' with rfl | hm
          · exact hmem'
          · exact List.mem_append_right _ (hmem C' hm hns)
        · simp only [List.length_append, List.length_cons]
          have hpow : 2 ^ (pdt z).depth ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (hpdt_d z)
          rw [Nat.mul_succ]; omega
      · cases hmu : m u
        · have hnsC : ¬ isSatByMenu m C := by
            rintro ⟨u', hu'⟩
            refine hsatR ⟨u', Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hu'⟩)⟩
            intro heq
            simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
            rcases heq with ⟨rfl, htr⟩
            rw [hmu] at htr; cases htr
          have hsub : clauseLine (stripMenu C) ⊆ clauseLine (stripMenu (C.erase (Sum.inr u, true) ∪ D.erase (Sum.inr u, false))) := by
            refine Finset.biUnion_subset_biUnion_of_subset_left _ fun l hl => ?_
            rw [mem_stripMenu_iff] at hl ⊢
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(by intro h; cases h), hl⟩)
          let Rline := clauseLine (stripMenu (C.erase (Sum.inr u, true) ∪ D.erase (Sum.inr u, false)))
          refine ⟨Rline :: σ, IsLinKDerivation.weak hσ (hmem C hC hnsC) (linKWeak_of_subset hsub) (hcl_k _), ?_, ?_⟩
          · intro C' hC' hns
            rcases List.mem_cons.mp hC' with rfl | hm
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmem C' hm hns)
          · simp only [List.length_cons]
            have hpos : 1 ≤ 3 * 2 ^ k := by have := Nat.one_le_pow k 2 (by omega); omega
            rw [Nat.mul_succ]; omega
        · have hnsD : ¬ isSatByMenu m D := by
            rintro ⟨u', hu'⟩
            refine hsatR ⟨u', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hu'⟩)⟩
            intro heq
            simp only [Prod.mk.injEq, Sum.inr.injEq] at heq
            rcases heq with ⟨rfl, hfl⟩
            rw [hmu] at hfl; cases hfl
          have hsub : clauseLine (stripMenu D) ⊆ clauseLine (stripMenu (C.erase (Sum.inr u, true) ∪ D.erase (Sum.inr u, false))) := by
            refine Finset.biUnion_subset_biUnion_of_subset_left _ fun l hl => ?_
            rw [mem_stripMenu_iff] at hl ⊢
            exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨(by intro h; cases h), hl⟩)
          let Rline := clauseLine (stripMenu (C.erase (Sum.inr u, true) ∪ D.erase (Sum.inr u, false)))
          refine ⟨Rline :: σ, IsLinKDerivation.weak hσ (hmem D hD hnsD) (linKWeak_of_subset hsub) (hcl_k _), ?_, ?_⟩
          · intro C' hC' hns
            rcases List.mem_cons.mp hC' with rfl | hm
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmem C' hm hns)
          · simp only [List.length_cons]
            have hpos : 1 ≤ 3 * 2 ^ k := by have := Nat.one_le_pow k 2 (by omega); omega
            rw [Nat.mul_succ]; omega

private lemma combine_advice_refutations {V : Type} [DecidableEq V] {a t r k M L0_len : ℕ}
    (hk : 1 ≤ k) (F : Set (Clause V)) (hFne : ∃ C0 : Clause V, C0 ∈ F)
    (pdt : V ⊕ Fin a → PDT V) (hpdt_d : ∀ w, (pdt w).depth ≤ k)
    (As : Fin t → Finset (Clause (V ⊕ Fin a)))
    (hAc : ∀ j : Fin t, (As j).card ≤ M)
    (hAr : ∀ j : Fin t, ∀ D ∈ As j, D.card ≤ r)
    (σs : Fin t → List (LinKLine V))
    (hσs_der : ∀ j : Fin t,
      IsLinKDerivation k IsLinKWeakening
        ((fun C => linKOfClause C) '' F ∪ (fun C : Clause (V ⊕ Fin a) => C.biUnion (fun l => (pdt l.1).leaves l.2 ∅)) '' (↑(As j) : Set (Clause (V ⊕ Fin a)))) (σs j))
    (hσs_emp : ∀ j : Fin t, (∅ : LinKLine V) ∈ σs j)
    (hσs_len : ∀ j : Fin t, (σs j).length ≤ L0_len) :
    let clauseLine : Clause (V ⊕ Fin a) → LinKLine V := fun C => C.biUnion (fun l => (pdt l.1).leaves l.2 ∅)
    let K0 : ℕ := 1 + (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) + 2 * L0_len
    ∀ s ≤ t, ∀ E : Clause (V ⊕ Fin a), E.card + s * r ≤ t * r →
      (∀ x : V → Bool, (∃ j : Fin t, j.val < s ∧ ∀ D ∈ As j, ClauseSat (fun w => (pdt w).eval x) D) ∨
        ClauseSat (fun w => (pdt w).eval x) E) →
      ∃ ρ : List (LinKLine V),
        IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) ρ ∧
        clauseLine E ∈ ρ ∧
        ρ.length ≤ (M + 1) ^ s * K0 := by
  classical
  intro clauseLine K0 s
  have hcl_k : ∀ C : Clause (V ⊕ Fin a), ∀ T ∈ clauseLine C, T.card ≤ k := by
    intro C T hT
    rcases Finset.mem_biUnion.mp hT with ⟨l, _, hTl⟩
    have := PDT.leaves_card_le (pdt l.1) l.2 ∅ T hTl
    have hd := hpdt_d l.1
    simp only [Finset.card_empty, zero_add] at this
    omega
  have hcl_union : ∀ C1 C2 : Clause (V ⊕ Fin a), clauseLine (C1 ∪ C2) = clauseLine C1 ∪ clauseLine C2 :=
    fun C1 C2 => Finset.union_biUnion
  induction s with
  | zero =>
    intro _ E hEc hsem
    rcases hFne with ⟨C0, hC0⟩
    have hax0 : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) [linKOfClause C0] := by
      refine IsLinKDerivation.ax IsLinKDerivation.nil ⟨C0, hC0, rfl⟩ ?_
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨q, _, rfl⟩
      simpa using hk
    have hcov : ∀ x : V → Bool, LinTermSat x ∅ → ∃ l ∈ E.toList, (pdt l.1).eval x = l.2 := by
      intro x _
      rcases hsem x with ⟨_, hlt, _⟩ | ⟨l, hlE, hev⟩
      · omega
      · exact ⟨l, Finset.mem_toList.mpr hlE, hev⟩
    rcases derive_phi_taut_aux hk pdt hpdt_d E (linKOfClause C0) E.toList ∅ [linKOfClause C0]
      hax0 List.mem_cons_self (fun l hl => Finset.mem_toList.mp hl) hcov with
      ⟨ext, hder, hmem, hlen⟩
    simp only [Finset.image_empty, Finset.union_empty] at hmem
    refine ⟨ext ++ [linKOfClause C0], hder, hmem, ?_⟩
    simp only [List.length_append, List.length_singleton, pow_zero, one_mul, Finset.length_toList] at hlen ⊢
    have hpow : (3 * 2 ^ k) ^ E.card ≤ (3 * 2 ^ k) ^ (t * r) :=
      Nat.pow_le_pow_right (by have := Nat.one_le_pow k 2 (by omega); omega) (by omega)
    have hmul : (3 * k + 4) * (3 * 2 ^ k) ^ E.card ≤ (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) :=
      Nat.mul_le_mul_left _ hpow
    dsimp only [K0]; omega
  | succ s ih =>
    intro hs E hEc hsem
    let js : Fin t := ⟨s, hs⟩
    have hstep_list : ∀ Ds : List (Clause (V ⊕ Fin a)), (∀ D ∈ Ds, D ∈ As js) →
        ∃ ρ0 : List (LinKLine V),
          IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) ρ0 ∧
          (∀ D ∈ Ds, clauseLine D ∪ clauseLine E ∈ ρ0) ∧
          ρ0.length ≤ Ds.length * ((M + 1) ^ s * K0) := by
      intro Ds
      induction Ds with
      | nil => intro _; exact ⟨[], IsLinKDerivation.nil, by simp, by simp⟩
      | cons D rest ihD =>
        intro hDs
        rcases ihD (fun D' hD' => hDs D' (List.mem_cons_of_mem _ hD')) with ⟨ρ1, hder1, hmem1, hlen1⟩
        have hD_in : D ∈ As js := hDs D List.mem_cons_self
        have hED_card : (E ∪ D).card + s * r ≤ t * r := by
          have := Finset.card_union_le E D
          have hDr := hAr js D hD_in
          have hsr : (s + 1) * r = s * r + r := by ring
          omega
        have hED_sem : ∀ x : V → Bool, (∃ j : Fin t, j.val < s ∧ ∀ D' ∈ As j, ClauseSat (fun w => (pdt w).eval x) D') ∨
            ClauseSat (fun w => (pdt w).eval x) (E ∪ D) := by
          intro x
          rcases hsem x with ⟨j, hjlt, hjsat⟩ | ⟨l, hlE, hev⟩
          · by_cases hjs : j.val < s
            · exact Or.inl ⟨j, hjs, hjsat⟩
            · have hjeq : j = js := Fin.ext (by dsimp only [js]; omega)
              rw [hjeq] at hjsat
              rcases hjsat D hD_in with ⟨l, hlD, hev⟩
              exact Or.inr ⟨l, Finset.mem_union_right _ hlD, hev⟩
          · exact Or.inr ⟨l, Finset.mem_union_left _ hlE, hev⟩
        rcases ih (by omega) (E ∪ D) hED_card hED_sem with ⟨ρD, hderD, hmemD, hlenD⟩
        have hder_comb : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) (ρD ++ ρ1) :=
          linK_concat hder1 (by
            have hmono : ∀ (S1 S2 : Set (LinKLine V)) (π : List (LinKLine V)),
                S1 ⊆ S2 → IsLinKDerivation k IsLinKWeakening S1 π → IsLinKDerivation k IsLinKWeakening S2 π := by
              intro S1 S2 π hsub hder
              induction hder with
              | nil => exact IsLinKDerivation.nil
              | ax _ hax hk ih => exact IsLinKDerivation.ax ih (hsub hax) hk
              | cut _ h1 h2 hc hk ih => exact IsLinKDerivation.cut ih h1 h2 hc hk
              | andIntro _ h1 h2 ha hk ih => exact IsLinKDerivation.andIntro ih h1 h2 ha hk
              | weak _ h1 hw hk ih => exact IsLinKDerivation.weak ih h1 hw hk
            exact hmono _ _ ρD Set.subset_union_left hderD)
        refine ⟨ρD ++ ρ1, hder_comb, ?_, ?_⟩
        · intro D' hD'
          rcases List.mem_cons.mp hD' with rfl | hm
          · rw [hcl_union, Finset.union_comm] at hmemD
            exact List.mem_append_left _ hmemD
          · exact List.mem_append_right _ (hmem1 D' hm)
        · simp only [List.length_append, List.length_cons]
          nlinarith
    rcases hstep_list (As js).toList (fun D hD => Finset.mem_toList.mp hD) with ⟨ρ0, hder0, hmem0, hlen0⟩
    rcases shift_linKDerivation ((fun C => linKOfClause C) '' F)
      (clauseLine '' (↑(As js) : Set (Clause (V ⊕ Fin a)))) (clauseLine E) (hcl_k E) (hσs_der js) with
      ⟨σ', hder', hmem', hlen'⟩
    have hsub_ax : ((fun C => linKOfClause C) '' F ∪
        (fun L => L ∪ clauseLine E) '' (clauseLine '' (↑(As js) : Set (Clause (V ⊕ Fin a))))) ⊆
        ((fun C => linKOfClause C) '' F ∪ {L | L ∈ ρ0}) := by
      rintro L (hF | ⟨_, ⟨D, hD, rfl⟩, rfl⟩)
      · exact Or.inl hF
      · exact Or.inr (hmem0 D (Finset.mem_toList.mpr (Finset.mem_coe.mp hD)))
    have hder_shift : IsLinKDerivation k IsLinKWeakening
        ((fun C => linKOfClause C) '' F ∪ {L | L ∈ ρ0}) σ' := by
      have hmono : ∀ (S1 S2 : Set (LinKLine V)) (π : List (LinKLine V)),
          S1 ⊆ S2 → IsLinKDerivation k IsLinKWeakening S1 π → IsLinKDerivation k IsLinKWeakening S2 π := by
        intro S1 S2 π hsub hder
        induction hder with
        | nil => exact IsLinKDerivation.nil
        | ax _ hax hk ih => exact IsLinKDerivation.ax ih (hsub hax) hk
        | cut _ h1 h2 hc hk ih => exact IsLinKDerivation.cut ih h1 h2 hc hk
        | andIntro _ h1 h2 ha hk ih => exact IsLinKDerivation.andIntro ih h1 h2 ha hk
        | weak _ h1 hw hk ih => exact IsLinKDerivation.weak ih h1 hw hk
      exact hmono _ _ σ' hsub_ax hder'
    have hcomb := linK_concat hder0 hder_shift
    have hE_in : clauseLine E ∈ σ' ++ ρ0 := by
      have h := hmem' ∅ (hσs_emp js)
      rw [Finset.empty_union] at h
      exact List.mem_append_left _ h
    refine ⟨σ' ++ ρ0, hcomb, hE_in, ?_⟩
    simp only [List.length_append, Finset.length_toList] at hlen0 ⊢
    have hAs_le : (As js).card ≤ M := hAc js
    have hσ_le : (σs js).length ≤ L0_len := hσs_len js
    have h1 : 1 ≤ (M + 1) ^ s := Nat.one_le_pow _ _ (by omega)
    have hK0_ge : 2 * L0_len ≤ K0 := by dsimp only [K0]; omega
    have hpow_s : (M + 1) ^ (s + 1) * K0 = M * ((M + 1) ^ s * K0) + (M + 1) ^ s * K0 := by
      rw [pow_succ]; ring
    have hA_mul : (As js).card * ((M + 1) ^ s * K0) ≤ M * ((M + 1) ^ s * K0) :=
      Nat.mul_le_mul_right _ hAs_le
    have hK_mul : K0 ≤ (M + 1) ^ s * K0 := Nat.le_mul_of_pos_left K0 h1
    omega

private lemma two_pow_le_exp_nat (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  calc (2 : ℝ) ^ m ≤ (Real.exp 1) ^ m := pow_le_pow_left₀ (by norm_num) h2 m
    _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul, mul_one]

private lemma k_mul_k_add_one_le_two_mul_four_pow (k : ℕ) : k * (k + 1) ≤ 2 * 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k' =>
      have h1 : (k' + 2) * (k' + 3) ≤ 4 * ((k' + 1) * (k' + 2)) := by nlinarith
      calc (k' + 2) * (k' + 3) ≤ 4 * ((k' + 1) * (k' + 2)) := h1
        _ ≤ 4 * (2 * 4 ^ (k' + 1)) := Nat.mul_le_mul_left 4 ih
        _ = 2 * 4 ^ (k' + 2) := by rw [pow_succ]; ring

private def pigeonCl {m N : ℕ} (G : BipGraph m N) (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

private lemma exists_funGraphPHP_finset {n b : ℕ} (G : BipGraph (n + 1) n)
    (hL : LeftDegLe G b) (hR : RightDegLe G b) :
    ∃ Ff : Finset (Clause (GEdge G)),
      (∀ cl, cl ∈ Ff ↔ cl ∈ funGraphPHP G) ∧
      Ff.card ≤ (n + 1) + n * b ^ 2 + (n + 1) * b ^ 2 := by
  classical
  let P := (Finset.univ : Finset (Fin (n + 1))).image (pigeonCl G)
  let Hpairs := (Finset.univ : Finset (GEdge G × GEdge G)).filter (fun p => p.1.1.2 = p.2.1.2 ∧ p.1.1.1 ≠ p.2.1.1)
  let Fpairs := (Finset.univ : Finset (GEdge G × GEdge G)).filter (fun p => p.1.1.1 = p.2.1.1 ∧ p.1.1.2 ≠ p.2.1.2)
  let Hcl := Hpairs.image (fun p => ({(p.1, false), (p.2, false)} : Clause (GEdge G)))
  let Fcl := Fpairs.image (fun p => ({(p.1, false), (p.2, false)} : Clause (GEdge G)))
  refine ⟨P ∪ Hcl ∪ Fcl, ?_, ?_⟩
  · intro cl
    simp only [Finset.mem_union, P, Hcl, Fcl, Finset.mem_image, Finset.mem_univ, true_and,
      Hpairs, Fpairs, Finset.mem_filter, funGraphPHP, graphPHP, Set.mem_union, Set.mem_setOf_eq, pigeonCl]
    constructor
    · rintro ((⟨i, rfl⟩ | ⟨⟨e, e'⟩, ⟨h1, h2⟩, rfl⟩) | ⟨⟨e, e'⟩, ⟨h1, h2⟩, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨e, e', h1, h2, rfl⟩)
      · exact Or.inr ⟨e, e', h1, h2, rfl⟩
    · rintro ((⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩) | ⟨e, e', h1, h2, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨(e, e'), ⟨h1, h2⟩, rfl⟩)
      · exact Or.inr ⟨(e, e'), ⟨h1, h2⟩, rfl⟩
  · have hP : P.card ≤ n + 1 := Finset.card_image_le.trans (by simp)
    have hH : Hcl.card ≤ n * b ^ 2 := by
      refine Finset.card_image_le.trans ?_
      let T : Finset (Σ j : Fin n, Fin (n + 1) × Fin (n + 1)) :=
        (Finset.univ : Finset (Fin n)).sigma (fun j => rightNbrs G j ×ˢ rightNbrs G j)
      have hinj : Hpairs.card ≤ T.card := by
        refine Finset.card_le_card_of_injOn (fun p => (⟨p.1.1.2, (p.1.1.1, p.2.1.1)⟩ : Σ j : Fin n, Fin (n + 1) × Fin (n + 1))) ?_ ?_
        · intro p hp
          have h12 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2.1
          refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1.2⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; rw [h12]; exact p.2.2⟩
        · intro p1 hp1 p2 hp2 heq
          have h1b := (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).2.1
          have h2b := (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).2.1
          have hj : p1.1.1.2 = p2.1.1.2 := congrArg Sigma.fst heq
          have hp_eq : (p1.1.1.1, p1.2.1.1) = (p2.1.1.1, p2.2.1.1) := by
            have := eq_of_heq (Sigma.mk.inj_iff.mp heq).2; exact this
          have hf : p1.1.1.1 = p2.1.1.1 := (Prod.mk.inj hp_eq).1
          have hs : p1.2.1.1 = p2.2.1.1 := (Prod.mk.inj hp_eq).2
          exact Prod.ext (Subtype.ext (Prod.ext hf hj)) (Subtype.ext (Prod.ext hs (h1b.symm.trans (hj.trans h2b))))
      calc Hpairs.card ≤ T.card := hinj
        _ = ∑ j : Fin n, (rightNbrs G j ×ˢ rightNbrs G j).card := Finset.card_sigma _ _
        _ ≤ ∑ _j : Fin n, b ^ 2 := Finset.sum_le_sum fun j _ => by
            calc (rightNbrs G j ×ˢ rightNbrs G j).card = (rightNbrs G j).card * (rightNbrs G j).card := Finset.card_product _ _
              _ ≤ b * b := Nat.mul_le_mul (hR j) (hR j)
              _ = b ^ 2 := (sq b).symm
        _ = n * b ^ 2 := by simp
    have hF : Fcl.card ≤ (n + 1) * b ^ 2 := by
      refine Finset.card_image_le.trans ?_
      let T : Finset (Σ i : Fin (n + 1), Fin n × Fin n) :=
        (Finset.univ : Finset (Fin (n + 1))).sigma (fun i => G i ×ˢ G i)
      have hinj : Fpairs.card ≤ T.card := by
        refine Finset.card_le_card_of_injOn (fun p => (⟨p.1.1.1, (p.1.1.2, p.2.1.2)⟩ : Σ i : Fin (n + 1), Fin n × Fin n)) ?_ ?_
        · intro p hp
          have h12 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2.1
          refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩)
          · exact p.1.2
          · dsimp only; rw [h12]; exact p.2.2
        · intro p1 hp1 p2 hp2 heq
          have h1b := (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).2.1
          have h2b := (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).2.1
          have hi : p1.1.1.1 = p2.1.1.1 := congrArg Sigma.fst heq
          have hp_eq : (p1.1.1.2, p1.2.1.2) = (p2.1.1.2, p2.2.1.2) := by
            have := eq_of_heq (Sigma.mk.inj_iff.mp heq).2; exact this
          have hf : p1.1.1.2 = p2.1.1.2 := (Prod.mk.inj hp_eq).1
          have hs : p1.2.1.2 = p2.2.1.2 := (Prod.mk.inj hp_eq).2
          exact Prod.ext (Subtype.ext (Prod.ext hi hf)) (Subtype.ext (Prod.ext (h1b.symm.trans (hi.trans h2b)) hs))
      calc Fpairs.card ≤ T.card := hinj
        _ = ∑ i : Fin (n + 1), (G i ×ˢ G i).card := Finset.card_sigma _ _
        _ ≤ ∑ _i : Fin (n + 1), b ^ 2 := Finset.sum_le_sum fun i _ => by
            calc (G i ×ˢ G i).card = (G i).card * (G i).card := Finset.card_product _ _
              _ ≤ b * b := Nat.mul_le_mul (hL i) (hL i)
              _ = b ^ 2 := (sq b).symm
        _ = (n + 1) * b ^ 2 := by simp
    calc (P ∪ Hcl ∪ Fcl).card ≤ (P ∪ Hcl).card + Fcl.card := Finset.card_union_le _ _
      _ ≤ (P.card + Hcl.card) + Fcl.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (n + 1) + n * b ^ 2 + (n + 1) * b ^ 2 := by omega

private lemma funGraphPHP_unsat {n : ℕ} (G : BipGraph (n + 1) n) (x : GEdge G → Bool) :
    ∃ cl ∈ funGraphPHP G, ¬ ClauseSat x cl := by
  by_contra hall
  push Not at hall
  have hex : ∀ i : Fin (n + 1), ∃ e : GEdge G, e.1.1 = i ∧ x e = true := by
    intro i
    have hsat := hall (pigeonCl G i) (Or.inl (Or.inl ⟨i, rfl⟩))
    rcases hsat with ⟨l, hl, hxl⟩
    have hlf := (Finset.mem_filter.mp hl).2
    exact ⟨l.1, hlf.1, hxl.trans hlf.2⟩
  let φ : Fin (n + 1) → Fin n := fun i => (Classical.choose (hex i)).1.2
  have hinj : Function.Injective φ := by
    intro i1 i2 heq
    by_contra hne
    let e1 := Classical.choose (hex i1)
    let e2 := Classical.choose (hex i2)
    have h1 := Classical.choose_spec (hex i1)
    have h2 := Classical.choose_spec (hex i2)
    have hcl : ({(e1, false), (e2, false)} : Clause (GEdge G)) ∈ funGraphPHP G :=
      Or.inl (Or.inr ⟨e1, e2, heq, by rw [h1.1, h2.1]; exact hne, rfl⟩)
    rcases hall _ hcl with ⟨l, hl, hxl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · rw [h1.2] at hxl; cases hxl
    · rw [h2.2] at hxl; cases hxl
  have hle := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at hle
  omega

private lemma funGraphPHP_nonempty_and_nontaut {n s : ℕ} (G : BipGraph (n + 1) n)
    (hE : IsBdryExpander G s 2) (hs : 1 ≤ s) {cl : Clause (GEdge G)} (hcl : cl ∈ funGraphPHP G) :
    cl.Nonempty ∧ ∀ v : GEdge G, ¬ ((v, true) ∈ cl ∧ (v, false) ∈ cl) := by
  rcases hcl with (⟨i, rfl⟩ | ⟨e, e', _, _, rfl⟩) | ⟨e, e', _, _, rfl⟩
  · constructor
    · have h1 := hE {i} (by simp [hs])
      rw [Finset.card_singleton] at h1
      have hpos : 0 < (uniqueNbrs G {i}).card := by omega
      rcases Finset.card_pos.mp hpos with ⟨j, hj⟩
      have hj1 := (Finset.mem_filter.mp hj).2
      have hpos2 : 0 < (({i} : Finset (Fin (n + 1))).filter (fun i' => j ∈ G i')).card := by omega
      rcases Finset.card_pos.mp hpos2 with ⟨i', hi'⟩
      have hi'1 := Finset.mem_singleton.mp (Finset.mem_filter.mp hi').1
      have hjG : j ∈ G i := hi'1 ▸ (Finset.mem_filter.mp hi').2
      exact ⟨(⟨(i, j), hjG⟩, true), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    · intro v ⟨_, hf⟩
      have := (Finset.mem_filter.mp hf).2.2
      cases this
  · exact ⟨⟨(e, false), Finset.mem_insert_self _ _⟩, fun v ⟨ht, _⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.true_eq_false, and_false, or_self] at ht⟩
  · exact ⟨⟨(e, false), Finset.mem_insert_self _ _⟩, fun v ⟨ht, _⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.true_eq_false, and_false, or_self] at ht⟩

private lemma resolve_clause_to_suffix {V : Type} [DecidableEq V] {h : ℕ}
    (Fset : Set (Clause (V ⊕ Fin h))) (S : Clause (V ⊕ Fin h))
    (hS_right : ∀ l ∈ S, l.1.isRight)
    (cl : Clause V) (hcl_ne : cl.Nonempty)
    (hcl_nt : ∀ v : V, ¬ ((v, true) ∈ cl ∧ (v, false) ∈ cl))
    (hcl_ax : cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin h), l.2)) ∈ Fset)
    (hex_ax : ∀ l ∈ cl, insert ((Sum.inl l.1 : V ⊕ Fin h), !l.2) S ∈ Fset)
    (π0 : List (Clause (V ⊕ Fin h))) (hπ0 : IsDerivation Fset π0) :
    ∃ ext : List (Clause (V ⊕ Fin h)),
      IsDerivation Fset (ext ++ π0) ∧
      S ∈ ext ++ π0 ∧
      ext.length ≤ 2 * cl.card + 1 ∧
      ∀ D ∈ ext, D.card ≤ cl.card + S.card := by
  let liftLit : Literal V → Literal (V ⊕ Fin h) := fun l => (Sum.inl l.1, l.2)
  have hstep : ∀ (rem : Finset (Literal V)) (π : List (Clause (V ⊕ Fin h))),
      rem ⊆ cl →
      IsDerivation Fset π →
      (rem.image liftLit ∪ S ∈ π ∨ (rem = cl ∧ rem.image liftLit ∈ π)) →
      ∃ ext : List (Clause (V ⊕ Fin h)),
        IsDerivation Fset (ext ++ π) ∧
        S ∈ ext ++ π ∧
        ext.length ≤ 2 * rem.card ∧
        ∀ D ∈ ext, D.card ≤ rem.card + S.card := by
    intro rem
    induction rem using Finset.induction_on with
    | empty =>
      intro π _ hπ hmem
      rcases hmem with h1 | ⟨hcl_e, _⟩
      · simp only [Finset.image_empty, Finset.empty_union] at h1
        exact ⟨[], hπ, h1, by simp, by simp⟩
      · exfalso; rw [← hcl_e] at hcl_ne; exact Finset.not_nonempty_empty hcl_ne
    | @insert l s hls ih =>
      intro π hsub hπ hmem
      have hlcl : l ∈ cl := hsub (Finset.mem_insert_self _ _)
      have hssub : s ⊆ cl := (Finset.subset_insert _ _).trans hsub
      let Ex : Clause (V ⊕ Fin h) := insert (Sum.inl l.1, !l.2) S
      have hEx_in : Ex ∈ Fset := hex_ax l hlcl
      have hder1 : IsDerivation Fset (Ex :: π) := IsDerivation.ax hπ hEx_in
      have hEx_card : Ex.card ≤ (insert l s).card + S.card := by
        dsimp only [Ex]
        have h1 := Finset.card_insert_le (Sum.inl l.1, !l.2) S
        rw [Finset.card_insert_of_notMem hls]; omega
      have hEx_erase : Ex.erase (Sum.inl l.1, !l.2) = S := by
        ext x; simp only [Ex, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hne, rfl | hxS⟩
          · exact (hne rfl).elim
          · exact hxS
        · intro hxS
          refine ⟨?_, Or.inr hxS⟩
          intro heq; have hr := hS_right x hxS; rw [heq] at hr; cases hr
      have himg_erase : ((insert l s).image liftLit).erase (liftLit l) = s.image liftLit := by
        ext x; simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_insert]
        constructor
        · rintro ⟨hne, ⟨l', rfl | hl's, rfl⟩⟩
          · exact (hne rfl).elim
          · exact ⟨l', hl's, rfl⟩
        · rintro ⟨l', hl's, rfl⟩
          refine ⟨?_, ⟨l', Or.inr hl's, rfl⟩⟩
          intro heq; apply hls
          rcases l with ⟨lv, lb⟩; rcases l' with ⟨l'v, l'b⟩
          simp only [liftLit, Prod.mk.injEq, Sum.inl.injEq] at heq
          rcases heq with ⟨rfl, rfl⟩; exact hl's
      have hnotS : liftLit l ∉ S := fun h => by have hr := hS_right _ h; cases hr
      have hres_exist : ∃ Ccur ∈ π, IsResolvent Ccur Ex (s.image liftLit ∪ S) ∨ IsResolvent Ex Ccur (s.image liftLit ∪ S) := by
        rcases hmem with hUS | ⟨_, hU⟩
        · refine ⟨(insert l s).image liftLit ∪ S, hUS, ?_⟩
          have hUnion_erase : ((insert l s).image liftLit ∪ S).erase (liftLit l) = s.image liftLit ∪ S := by
            rw [Finset.erase_union_distrib, himg_erase, Finset.erase_eq_of_notMem hnotS]
          cases hb : l.2
          · right
            refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
            · dsimp only [Ex]; rw [hb]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, Finset.mem_insert_self _ _, by simp [liftLit, hb]⟩)
            · have he1 : Ex.erase (Sum.inl l.1, true) = S := by simpa [hb] using hEx_erase
              have he2 : ((insert l s).image liftLit ∪ S).erase (Sum.inl l.1, false) = s.image liftLit ∪ S := by
                simpa [liftLit, hb] using hUnion_erase
              rw [he1, he2]; ext x; simp only [Finset.mem_union]; tauto
          · left
            refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, Finset.mem_insert_self _ _, by simp [liftLit, hb]⟩)
            · dsimp only [Ex]; rw [hb]; exact Finset.mem_insert_self _ _
            · have he1 : ((insert l s).image liftLit ∪ S).erase (Sum.inl l.1, true) = s.image liftLit ∪ S := by
                simpa [liftLit, hb] using hUnion_erase
              have he2 : Ex.erase (Sum.inl l.1, false) = S := by simpa [hb] using hEx_erase
              rw [he1, he2]; ext x; simp only [Finset.mem_union]; tauto
        · refine ⟨(insert l s).image liftLit, hU, ?_⟩
          cases hb : l.2
          · right
            refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
            · dsimp only [Ex]; rw [hb]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_image.mpr ⟨l, Finset.mem_insert_self _ _, by simp [liftLit, hb]⟩
            · have he1 : Ex.erase (Sum.inl l.1, true) = S := by simpa [hb] using hEx_erase
              have he2 : ((insert l s).image liftLit).erase (Sum.inl l.1, false) = s.image liftLit := by
                simpa [liftLit, hb] using himg_erase
              rw [he1, he2, Finset.union_comm]
          · left
            refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
            · exact Finset.mem_image.mpr ⟨l, Finset.mem_insert_self _ _, by simp [liftLit, hb]⟩
            · dsimp only [Ex]; rw [hb]; exact Finset.mem_insert_self _ _
            · have he1 : ((insert l s).image liftLit).erase (Sum.inl l.1, true) = s.image liftLit := by
                simpa [liftLit, hb] using himg_erase
              have he2 : Ex.erase (Sum.inl l.1, false) = S := by simpa [hb] using hEx_erase
              rw [he1, he2]
      rcases hres_exist with ⟨Ccur, hCcur, hres | hres⟩
      · have hder2 : IsDerivation Fset ((s.image liftLit ∪ S) :: Ex :: π) :=
          IsDerivation.res hder1 (List.mem_cons_of_mem _ hCcur) List.mem_cons_self hres
        rcases ih ((s.image liftLit ∪ S) :: Ex :: π) hssub hder2 (Or.inl List.mem_cons_self) with
          ⟨ext', hder', hmem', hlen', hwid'⟩
        refine ⟨ext' ++ [s.image liftLit ∪ S, Ex], ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hder'
        · simpa [List.append_assoc] using hmem'
        · simp only [List.length_append, List.length_cons, List.length_nil, Finset.card_insert_of_notMem hls]; omega
        · intro D hD
          rcases List.mem_append.mp hD with h1 | h2
          · have := hwid' D h1; rw [Finset.card_insert_of_notMem hls]; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl
            · calc (s.image liftLit ∪ S).card ≤ (s.image liftLit).card + S.card := Finset.card_union_le _ _
                _ ≤ s.card + S.card := Nat.add_le_add_right Finset.card_image_le _
                _ ≤ (insert l s).card + S.card := by rw [Finset.card_insert_of_notMem hls]; omega
            · exact hEx_card
      · have hder2 : IsDerivation Fset ((s.image liftLit ∪ S) :: Ex :: π) :=
          IsDerivation.res hder1 List.mem_cons_self (List.mem_cons_of_mem _ hCcur) hres
        rcases ih ((s.image liftLit ∪ S) :: Ex :: π) hssub hder2 (Or.inl List.mem_cons_self) with
          ⟨ext', hder', hmem', hlen', hwid'⟩
        refine ⟨ext' ++ [s.image liftLit ∪ S, Ex], ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hder'
        · simpa [List.append_assoc] using hmem'
        · simp only [List.length_append, List.length_cons, List.length_nil, Finset.card_insert_of_notMem hls]; omega
        · intro D hD
          rcases List.mem_append.mp hD with h1 | h2
          · have := hwid' D h1; rw [Finset.card_insert_of_notMem hls]; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl
            · calc (s.image liftLit ∪ S).card ≤ (s.image liftLit).card + S.card := Finset.card_union_le _ _
                _ ≤ s.card + S.card := Nat.add_le_add_right Finset.card_image_le _
                _ ≤ (insert l s).card + S.card := by rw [Finset.card_insert_of_notMem hls]; omega
            · exact hEx_card
  have hder0 : IsDerivation Fset (cl.image liftLit :: π0) := IsDerivation.ax hπ0 hcl_ax
  rcases hstep cl (cl.image liftLit :: π0) subset_rfl hder0 (Or.inr ⟨rfl, List.mem_cons_self⟩) with
    ⟨ext, hder, hmem, hlen, hwid⟩
  refine ⟨ext ++ [cl.image liftLit], ?_, ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using hder
  · simpa [List.append_assoc] using hmem
  · simp only [List.length_append, List.length_singleton]; omega
  · intro D hD
    rcases List.mem_append.mp hD with h1 | h2
    · exact hwid D h1
    · rw [List.mem_singleton.mp h2]
      exact Finset.card_image_le.trans (Nat.le_add_right _ _)

private lemma upper_bound_chain {n b s : ℕ} (G : BipGraph (n + 1) n)
    (hL : LeftDegLe G b) (hR : RightDegLe G b) (hE : IsBdryExpander G s 2) (hs : 1 ≤ s) :
    let V := GEdge G
    let F := funGraphPHP G
    let w := max b 2
    ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
      (extra : Finset (Clause (V ⊕ Fin h)))
      (π : List (Clause (V ⊕ Fin h))),
      let lift := fun cl : Clause V => cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin h), l.2))
      (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
      (∀ x : V → Bool, ∃ j : Fin t, Satisfies (Sum.elim x (menu j)) (↑extra : Set (Clause (V ⊕ Fin h)))) ∧
      IsRefutation (Set.image lift F ∪ (↑extra : Set (Clause (V ⊕ Fin h)))) π ∧
      h + t + extra.card + π.length ≤ (3 * w + 6) * ((n + 1) + n * b ^ 2 + (n + 1) * b ^ 2) + 3 ∧
      ∀ D ∈ π, D.card ≤ w + 2 := by
  classical
  intro V F w
  rcases exists_funGraphPHP_finset G hL hR with ⟨Ff, hFf_mem, hFf_card⟩
  let L : List (Clause V) := Ff.toList
  have hL_len : L.length = Ff.card := Finset.length_toList Ff
  have hL_pos : 1 ≤ L.length := by
    have hp0 : pigeonCl G 0 ∈ Ff := (hFf_mem _).mpr (Or.inl (Or.inl ⟨0, rfl⟩))
    have hpos : 0 < Ff.card := Finset.card_pos.mpr ⟨_, hp0⟩
    omega
  let M := L.length
  let menu : Fin M → Fin M → Bool := fun j i => decide (j.val ≤ i.val)
  let suff : Fin M → Clause (V ⊕ Fin M) := fun j =>
    if h0 : j.val = 0 then {(Sum.inr j, false)}
    else {(Sum.inr ⟨j.val - 1, by omega⟩, true), (Sum.inr j, false)}
  let rootCl : Clause (V ⊕ Fin M) := {(Sum.inr ⟨M - 1, by omega⟩, true)}
  let extraFor : Fin M → Finset (Clause (V ⊕ Fin M)) := fun j =>
    (L[j.val]'j.isLt).image (fun l => insert (Sum.inl l.1, !l.2) (suff j))
  let extra : Finset (Clause (V ⊕ Fin M)) :=
    insert rootCl ((Finset.univ : Finset (Fin M)).biUnion extraFor)
  let lift := fun cl : Clause V => cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin M), l.2))
  let Fset : Set (Clause (V ⊕ Fin M)) := Set.image lift F ∪ (↑extra : Set (Clause (V ⊕ Fin M)))
  have hcl_wid : ∀ j : Fin M, (L[j.val]'j.isLt).card ≤ w := fun j =>
    H.LinKFinal.funGraphPHP_width G b hL _ ((hFf_mem _).mp (Finset.mem_toList.mp (List.getElem_mem j.isLt)))
  have hextra_ok : ∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1 := by
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hbu
    · refine ⟨by simp [rootCl], ?_⟩
      have : rootCl.filter (fun l => l.1.isLeft) = ∅ := by simp [rootCl]
      rw [this]; simp
    · rcases Finset.mem_biUnion.mp hbu with ⟨j, _, hDj⟩
      rcases Finset.mem_image.mp hDj with ⟨l, _, rfl⟩
      have hsuff_card : (suff j).card ≤ 2 := by
        dsimp only [suff]; split_ifs
        · simp
        · exact Finset.card_le_two
      have hsuff_flt : (suff j).filter (fun l' => l'.1.isLeft) = ∅ := by
        dsimp only [suff]; split_ifs <;> simp
      refine ⟨(Finset.card_insert_le _ _).trans (by omega), ?_⟩
      rw [Finset.filter_insert]; simp [hsuff_flt]
  have hextra_card : extra.card ≤ 1 + w * M := by
    calc extra.card ≤ 1 + ((Finset.univ : Finset (Fin M)).biUnion extraFor).card := by
          dsimp only [extra]
          have := Finset.card_insert_le rootCl ((Finset.univ : Finset (Fin M)).biUnion extraFor); omega
      _ ≤ 1 + ∑ j : Fin M, (extraFor j).card := Nat.add_le_add_left Finset.card_biUnion_le 1
      _ ≤ 1 + ∑ _j : Fin M, w := Nat.add_le_add_left (Finset.sum_le_sum fun j _ =>
          Finset.card_image_le.trans (hcl_wid j)) 1
      _ = 1 + w * M := by simp [Nat.mul_comm]
  have hmenu_sat : ∀ x : V → Bool, ∃ j : Fin M, Satisfies (Sum.elim x (menu j)) (↑extra : Set (Clause (V ⊕ Fin M))) := by
    intro x
    rcases funGraphPHP_unsat G x with ⟨cl, hclF, hnsat⟩
    have hclL : cl ∈ L := Finset.mem_toList.mpr ((hFf_mem cl).mpr hclF)
    rcases List.getElem_of_mem hclL with ⟨idx, hidx, rfl⟩
    let j0 : Fin M := ⟨idx, hidx⟩
    refine ⟨j0, fun D hD => ?_⟩
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hD) with rfl | hbu
    · refine ⟨(Sum.inr ⟨M - 1, by omega⟩, true), Finset.mem_singleton_self _, ?_⟩
      simp only [Sum.elim_inr, menu, decide_eq_true_eq]; omega
    · rcases Finset.mem_biUnion.mp hbu with ⟨j, _, hDj⟩
      rcases Finset.mem_image.mp hDj with ⟨l, hl, rfl⟩
      by_cases hjj : j.val = j0.val
      · have hjeq : j = j0 := Fin.ext hjj
        subst hjeq
        have hne : x l.1 ≠ l.2 := fun heq => hnsat ⟨l, hl, heq⟩
        refine ⟨(Sum.inl l.1, !l.2), Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inl]
        cases hxl : x l.1 <;> cases hlb : l.2 <;> simp_all
      · by_cases hlt : j.val < j0.val
        · refine ⟨(Sum.inr j, false), Finset.mem_insert_of_mem ?_, ?_⟩
          · dsimp only [suff]; split_ifs
            · exact Finset.mem_singleton_self _
            · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · simp only [Sum.elim_inr, menu, decide_eq_false_iff_not]; omega
        · have hgt : j0.val < j.val := by omega
          have hjne0 : j.val ≠ 0 := by omega
          refine ⟨(Sum.inr ⟨j.val - 1, by omega⟩, true), Finset.mem_insert_of_mem ?_, ?_⟩
          · dsimp only [suff]; rw [dif_neg hjne0]; exact Finset.mem_insert_self _ _
          · simp only [Sum.elim_inr, menu, decide_eq_true_eq]; omega
  have hchain : ∀ k (hk : k < M),
      ∃ πk : List (Clause (V ⊕ Fin M)),
        IsDerivation Fset πk ∧
        ({(Sum.inr ⟨k, hk⟩, false)} : Clause (V ⊕ Fin M)) ∈ πk ∧
        πk.length ≤ (k + 1) * (2 * w + 2) ∧
        ∀ D ∈ πk, D.card ≤ w + 2 := by
    intro k
    induction k with
    | zero =>
      intro hk
      let j0 : Fin M := ⟨0, hk⟩
      have hjF : L[0]'hk ∈ F := (hFf_mem _).mp (Finset.mem_toList.mp (List.getElem_mem hk))
      rcases funGraphPHP_nonempty_and_nontaut G hE hs hjF with ⟨hne, hnt⟩
      have hsuff0 : suff j0 = {(Sum.inr j0, false)} := by simp [suff, j0]
      rcases resolve_clause_to_suffix Fset (suff j0) (by rw [hsuff0]; simp) (L[0]'hk) hne hnt
        (Or.inl ⟨L[0]'hk, hjF, rfl⟩)
        (fun l hl => Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨j0, Finset.mem_univ _, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩))))
        [] IsDerivation.nil with ⟨ext, hder, hmem, hlen, hwid⟩
      rw [List.append_nil] at hder hmem
      rw [hsuff0] at hmem hwid
      have hw0 : (L[0]'hk).card ≤ w := hcl_wid j0
      refine ⟨ext, hder, hmem, ?_, ?_⟩
      · omega
      · intro D hD
        have := hwid D hD; simp only [Finset.card_singleton] at this; omega
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨πk, hderk, hmemk, hlenk, hwidk⟩
      let jk : Fin M := ⟨k + 1, hk⟩
      have hjF : L[k + 1]'hk ∈ F := (hFf_mem _).mp (Finset.mem_toList.mp (List.getElem_mem hk))
      rcases funGraphPHP_nonempty_and_nontaut G hE hs hjF with ⟨hne, hnt⟩
      have hsuffk : suff jk = {(Sum.inr ⟨k, by omega⟩, true), (Sum.inr jk, false)} := by
        dsimp only [suff, jk]; simp
      have hsr : ∀ l ∈ suff jk, l.1.isRight := by rw [hsuffk]; simp
      rcases resolve_clause_to_suffix Fset (suff jk) hsr (L[k + 1]'hk) hne hnt
        (Or.inl ⟨L[k + 1]'hk, hjF, rfl⟩)
        (fun l hl => Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨jk, Finset.mem_univ _, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩))))
        πk hderk with ⟨ext, hder1, hmem1, hlen1, hwid1⟩
      have hres : IsResolvent (suff jk) {(Sum.inr ⟨k, by omega⟩, false)} {(Sum.inr jk, false)} := by
        refine ⟨Sum.inr ⟨k, by omega⟩, ?_, Finset.mem_singleton_self _, ?_⟩
        · rw [hsuffk]; exact Finset.mem_insert_self _ _
        · rw [hsuffk, Finset.erase_singleton, Finset.union_empty]
          ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hx; subst hx
            refine ⟨?_, Or.inr rfl⟩
            intro heq; have h2 := congrArg Prod.snd heq; cases h2
          · rintro ⟨hne, rfl | rfl⟩
            · exact (hne rfl).elim
            · rfl
      have hder2 := IsDerivation.res hder1 hmem1 (List.mem_append_right _ hmemk) hres
      have hwk : (L[k + 1]'hk).card ≤ w := hcl_wid jk
      refine ⟨{(Sum.inr jk, false)} :: (ext ++ πk), hder2, List.mem_cons_self, ?_, ?_⟩
      · simp only [List.length_cons, List.length_append]
        nlinarith
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hm
        · simp
        · rcases List.mem_append.mp hm with h1 | h2
          · have := hwid1 D h1
            have hsc : (suff jk).card ≤ 2 := by rw [hsuffk]; exact Finset.card_le_two
            omega
          · exact hwidk D h2
  rcases hchain (M - 1) (by omega) with ⟨π1, hder1, hmem1, hlen1, hwid1⟩
  have hroot_ax : rootCl ∈ Fset := Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hder2 := IsDerivation.ax hder1 hroot_ax
  have hres_final : IsResolvent rootCl {(Sum.inr ⟨M - 1, by omega⟩, false)} (∅ : Clause (V ⊕ Fin M)) := by
    refine ⟨Sum.inr ⟨M - 1, by omega⟩, Finset.mem_singleton_self _, Finset.mem_singleton_self _, ?_⟩
    simp [rootCl]
  have hder3 := IsDerivation.res hder2 List.mem_cons_self (List.mem_cons_of_mem _ hmem1) hres_final
  refine ⟨M, M, menu, extra, (∅ : Clause (V ⊕ Fin M)) :: rootCl :: π1, hextra_ok, hmenu_sat,
    ⟨hder3, List.mem_cons_self⟩, ?_, ?_⟩
  · simp only [List.length_cons]
    have hM_le : M ≤ (n + 1) + n * b ^ 2 + (n + 1) * b ^ 2 := by dsimp only [M]; rw [hL_len]; exact hFf_card
    have h1 : (M - 1 + 1) * (2 * w + 2) = M * (2 * w + 2) := by congr 1; omega
    rw [h1] at hlen1
    nlinarith
  · intro D hD
    rcases List.mem_cons.mp hD with rfl | hm
    · simp
    · rcases List.mem_cons.mp hm with rfl | hm2
      · simp [rootCl]
      · exact hwid1 D hm2

private lemma lower_bound_arith
    {n k t r ell s0 w C pi_len rho_len : ℕ}
    (hs0 : 0 < s0) (hw2 : 2 ≤ w) (hk1 : 1 ≤ k) (ht : 0 < t)
    (hClb : 65536 * s0 ^ 2 * w ^ 3 ≤ C)
    (hpi_le : pi_len + 1 ≤ 2 ^ ell)
    (hρ_len : rho_len ≤ (pi_len + 1) ^ t * (1 + (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) + 2 * ((3 * 2 ^ k) * pi_len)))
    (hbound : Real.exp ((1 / (16 * (s0 : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s0 * w) * n) ≤ rho_len) :
    n ≤ C ^ k * t * (r + ell + 1) := by
  have hρ_pow : rho_len ≤ 2 ^ (6 * (k + 1) * t * (r + ell + 1)) := by
    have h1 : (pi_len + 1) ^ t ≤ 2 ^ (t * ell) := by
      calc (pi_len + 1) ^ t ≤ (2 ^ ell) ^ t := Nat.pow_le_pow_left hpi_le t
        _ = 2 ^ (t * ell) := by rw [← pow_mul, mul_comm]
    have h3_le : 3 * 2 ^ k ≤ 2 ^ (k + 2) := by rw [pow_add]; omega
    have h2 : (3 * 2 ^ k) ^ (t * r) ≤ 2 ^ ((k + 2) * (t * r)) := by
      calc (3 * 2 ^ k) ^ (t * r) ≤ (2 ^ (k + 2)) ^ (t * r) := Nat.pow_le_pow_left h3_le _
        _ = 2 ^ ((k + 2) * (t * r)) := by rw [← pow_mul]
    have h3k4 : 3 * k + 4 ≤ 2 ^ (2 * k + 2) := by
      have : ∀ m : ℕ, 3 * m + 4 ≤ 2 ^ (2 * m + 2) := by
        intro m; induction m with
        | zero => simp
        | succ m' ihm =>
          have hpow : 2 ^ (2 * (m' + 1) + 2) = 4 * 2 ^ (2 * m' + 2) := by
            rw [show 2 * (m' + 1) + 2 = (2 * m' + 2) + 2 by omega, pow_add]; ring
          omega
      exact this k
    have hL0_le : 2 * ((3 * 2 ^ k) * pi_len) ≤ 2 ^ (k + 3 + ell) := by
      calc 2 * ((3 * 2 ^ k) * pi_len) ≤ 2 * (2 ^ (k + 2) * 2 ^ ell) := by
            have := Nat.mul_le_mul h3_le (show pi_len ≤ 2 ^ ell by omega); omega
        _ = 2 ^ (k + 3 + ell) := by rw [pow_add, pow_add, pow_succ]; ring
    have hK0_le : 1 + (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) + 2 * ((3 * 2 ^ k) * pi_len) ≤
        2 ^ ((k + 2) * (t * r) + 2 * k + 4 + ell) := by
      have ha : (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) ≤ 2 ^ ((k + 2) * (t * r) + 2 * k + 2) := by
        calc (3 * k + 4) * (3 * 2 ^ k) ^ (t * r)
            ≤ 2 ^ (2 * k + 2) * 2 ^ ((k + 2) * (t * r)) := Nat.mul_le_mul h3k4 h2
          _ = 2 ^ ((k + 2) * (t * r) + 2 * k + 2) := by rw [← pow_add]; congr 1; omega
      have hb : 2 ^ ((k + 2) * (t * r) + 2 * k + 2) ≤ 2 ^ ((k + 2) * (t * r) + 2 * k + 3 + ell) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hc : 2 ^ (k + 3 + ell) ≤ 2 ^ ((k + 2) * (t * r) + 2 * k + 3 + ell) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hp1 : 2 ^ ((k + 2) * (t * r) + 2 * k + 4 + ell) =
          2 * 2 ^ ((k + 2) * (t * r) + 2 * k + 3 + ell) := by
        rw [show (k + 2) * (t * r) + 2 * k + 4 + ell = ((k + 2) * (t * r) + 2 * k + 3 + ell) + 1 by omega, pow_succ, mul_comm]
      have hp2 : 2 ^ ((k + 2) * (t * r) + 2 * k + 2) + 1 ≤ 2 ^ ((k + 2) * (t * r) + 2 * k + 3 + ell) := by
        have hq : 2 ^ ((k + 2) * (t * r) + 2 * k + 3 + ell) ≥ 2 * 2 ^ ((k + 2) * (t * r) + 2 * k + 2) := by
          have := Nat.pow_le_pow_right (by omega : 0 < 2)
            (show (k + 2) * (t * r) + 2 * k + 2 + 1 ≤ (k + 2) * (t * r) + 2 * k + 3 + ell by omega)
          rw [pow_succ, mul_comm] at this; exact this
        have hpos : 1 ≤ 2 ^ ((k + 2) * (t * r) + 2 * k + 2) := Nat.one_le_pow _ _ (by omega)
        omega
      omega
    have hexp_le : t * ell + ((k + 2) * (t * r) + 2 * k + 4 + ell) ≤ 6 * (k + 1) * t * (r + ell + 1) := by
      have ha : (k + 2) * (t * r) ≤ 2 * (k + 1) * (t * r) :=
        Nat.mul_le_mul_right (t * r) (by omega)
      have hb : t * ell + ell ≤ 2 * (t * ell) := by
        have : ell ≤ t * ell := Nat.le_mul_of_pos_left ell ht; omega
      have hc : 2 * k + 4 ≤ 4 * (k + 1) * t := by
        have h4 : 2 * k + 4 ≤ 4 * (k + 1) := by omega
        exact h4.trans (Nat.le_mul_of_pos_right _ ht)
      have hsum : 2 * (k + 1) * (t * r) + 2 * (t * ell) + 4 * (k + 1) * t ≤ 6 * (k + 1) * t * (r + ell + 1) := by
        have h1 : 2 * (t * ell) ≤ 6 * (k + 1) * (t * ell) := Nat.mul_le_mul_right (t * ell) (by omega)
        have h2 : 2 * (k + 1) * (t * r) ≤ 6 * (k + 1) * (t * r) := Nat.mul_le_mul_right _ (by omega)
        have h3 : 4 * (k + 1) * t ≤ 6 * (k + 1) * t := Nat.mul_le_mul_right _ (by omega)
        have heq : 6 * (k + 1) * t * (r + ell + 1) =
            6 * (k + 1) * (t * r) + 6 * (k + 1) * (t * ell) + 6 * (k + 1) * t := by ring
        omega
      omega
    calc rho_len ≤ (pi_len + 1) ^ t * (1 + (3 * k + 4) * (3 * 2 ^ k) ^ (t * r) + 2 * ((3 * 2 ^ k) * pi_len)) := hρ_len
      _ ≤ 2 ^ (t * ell) * 2 ^ ((k + 2) * (t * r) + 2 * k + 4 + ell) := Nat.mul_le_mul h1 hK0_le
      _ = 2 ^ (t * ell + ((k + 2) * (t * r) + 2 * k + 4 + ell)) := by rw [← pow_add]
      _ ≤ 2 ^ (6 * (k + 1) * t * (r + ell + 1)) := Nat.pow_le_pow_right (by omega) hexp_le
  have hreal : Real.exp ((1 / (16 * (s0 : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s0 * w) * n) ≤
      Real.exp ((6 * (k + 1) * t * (r + ell + 1) : ℕ) : ℝ) := by
    calc _ ≤ (rho_len : ℝ) := hbound
      _ ≤ ((2 ^ (6 * (k + 1) * t * (r + ell + 1)) : ℕ) : ℝ) := by exact_mod_cast hρ_pow
      _ = (2 : ℝ) ^ (6 * (k + 1) * t * (r + ell + 1)) := by push_cast; rfl
      _ ≤ Real.exp ((6 * (k + 1) * t * (r + ell + 1) : ℕ) : ℝ) := two_pow_le_exp_nat _
  have hexp_cmp := Real.exp_le_exp.mp hreal
  have hden_pos : (0 : ℝ) < (16 * (s0 : ℝ) * (w : ℝ) ^ 2) ^ k * (32 * (k : ℝ) * s0 * w) := by
    have hs0R : (0 : ℝ) < s0 := by exact_mod_cast hs0
    have hwR : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    positivity
  have hmulR : (n : ℝ) ≤ ((6 * (k + 1) * t * (r + ell + 1) : ℕ) : ℝ) *
      ((16 * (s0 : ℝ) * (w : ℝ) ^ 2) ^ k * (32 * (k : ℝ) * s0 * w)) := by
    have hrew : (1 / (16 * (s0 : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s0 * w) * n =
        (n : ℝ) / ((16 * (s0 : ℝ) * (w : ℝ) ^ 2) ^ k * (32 * (k : ℝ) * s0 * w)) := by
      rw [one_div_pow, div_div, div_mul_eq_mul_div, one_mul]
    rw [hrew, div_le_iff₀ hden_pos] at hexp_cmp
    exact hexp_cmp
  have hnat : n ≤ 6 * (k + 1) * t * (r + ell + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w)) := by
    have hcast : ((6 * (k + 1) * t * (r + ell + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w)) : ℕ) : ℝ) =
        ((6 * (k + 1) * t * (r + ell + 1) : ℕ) : ℝ) *
        ((16 * (s0 : ℝ) * (w : ℝ) ^ 2) ^ k * (32 * (k : ℝ) * s0 * w)) := by
      push_cast; ring
    rw [← hcast] at hmulR
    exact_mod_cast hmulR
  have hcoef : 6 * (k + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w)) ≤ C ^ k := by
    have hkk := k_mul_k_add_one_le_two_mul_four_pow k
    have h1 : 6 * (k + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w)) =
        (192 * s0 * w) * (k * (k + 1)) * (16 * s0 * w ^ 2) ^ k := by ring
    rw [h1]
    have h2 : (192 * s0 * w) * (k * (k + 1)) ≤ (384 * s0 * w) * 4 ^ k := by
      calc (192 * s0 * w) * (k * (k + 1)) ≤ (192 * s0 * w) * (2 * 4 ^ k) := Nat.mul_le_mul_left _ hkk
        _ = (384 * s0 * w) * 4 ^ k := by ring
    have h3 : 384 * s0 * w ≤ (384 * s0 * w) ^ k := Nat.le_self_pow (by omega) _
    have h4 : (384 * s0 * w) * 4 ^ k * (16 * s0 * w ^ 2) ^ k ≤
        (384 * s0 * w) ^ k * 4 ^ k * (16 * s0 * w ^ 2) ^ k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    have h5 : (384 * s0 * w) ^ k * 4 ^ k * (16 * s0 * w ^ 2) ^ k =
        (384 * s0 * w * 4 * (16 * s0 * w ^ 2)) ^ k := by rw [← mul_pow, ← mul_pow]
    have h6 : 384 * s0 * w * 4 * (16 * s0 * w ^ 2) ≤ C := by
      have hrew : 384 * s0 * w * 4 * (16 * s0 * w ^ 2) = 24576 * (s0 ^ 2 * w ^ 3) := by ring
      have hrew2 : 65536 * s0 ^ 2 * w ^ 3 = 65536 * (s0 ^ 2 * w ^ 3) := by ring
      rw [hrew]
      rw [hrew2] at hClb
      exact (Nat.mul_le_mul_right (s0 ^ 2 * w ^ 3) (by omega)).trans hClb
    calc (192 * s0 * w) * (k * (k + 1)) * (16 * s0 * w ^ 2) ^ k
        ≤ (384 * s0 * w) * 4 ^ k * (16 * s0 * w ^ 2) ^ k := Nat.mul_le_mul_right _ h2
      _ ≤ (384 * s0 * w) ^ k * 4 ^ k * (16 * s0 * w ^ 2) ^ k := h4
      _ = (384 * s0 * w * 4 * (16 * s0 * w ^ 2)) ^ k := h5
      _ ≤ C ^ k := Nat.pow_le_pow_left h6 k
  have hrearr : 6 * (k + 1) * t * (r + ell + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w)) =
      (6 * (k + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w))) * t * (r + ell + 1) := by ring
  rw [hrearr] at hnat
  calc n ≤ (6 * (k + 1) * ((16 * s0 * w ^ 2) ^ k * (32 * k * s0 * w))) * t * (r + ell + 1) := hnat
    _ ≤ C ^ k * t * (r + ell + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef)

private lemma main :
    ∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
        PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
        let V := PEqualNP.Expanders.GEdge G
        let F := PEqualNP.Expanders.funGraphPHP G
        (∀ (a h t r p q : ℕ) (f : (V → Bool) → Fin a → Bool)
        (menu : Fin t → Fin h → Bool),
          let W := (V ⊕ Fin a) ⊕ Fin h
          let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
            cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
          let k := max 1 (p*q)
          0 < t →
          (∀ (x : V → Bool) (i : Fin a), ∃ T : PEqualNP.ProofComplexity.LinTerm V,
            T.card ≤ (if f x i then q else p) ∧ PEqualNP.ProofComplexity.LinTermSat x T ∧
            ∀ y : V → Bool, PEqualNP.ProofComplexity.LinTermSat y T → f y i = f x i) →
          ∀ extra : Set (PEqualNP.ProofComplexity.Clause W),
            (∀ D ∈ extra, (D.filter (fun l => l.1.isLeft)).card ≤ r) →
            (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
              (Sum.elim (Sum.elim x (f x)) (menu j)) extra) →
            ∀ π : List (PEqualNP.ProofComplexity.Clause W),
              PEqualNP.ProofComplexity.IsRefutation (Set.image lift F ∪ extra) π →
              n ≤ C^k * t * (r + Nat.clog 2 (π.length+1) + 1)) ∧
        ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
            (extra : Finset (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))
            (π : List (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h))),
          let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
            cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin h), l.2))
          (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
          (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
            (Sum.elim x (menu j)) (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) ∧
          PEqualNP.ProofComplexity.IsRefutation
            (Set.image lift F ∪ (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) π ∧
          h + t + extra.card + π.length ≤ C*n ∧ ∀ D ∈ π, D.card ≤ C := by
  classical
  have hL : H.LinKFinal.StmtLinK := H.LinKWire.general H.LinKSim.simulation_refutation
  rcases H.L043 with ⟨b, s0, n0_exp, hs0, hG_ex⟩
  let w : ℕ := max b 2
  have hw2 : 2 ≤ w := le_max_right b 2
  have hbw : b ≤ w := le_max_left b 2
  let C_lb : ℕ := 65536 * s0 ^ 2 * w ^ 3
  let C_ub : ℕ := (3 * w + 6) * (3 * b ^ 2 + 2) + w + 10
  let C : ℕ := max (max C_lb C_ub) (4 * s0 * w * (16 + 4 * w) + 2)
  let n0 : ℕ := max (max n0_exp (4 * (s0 * w) + s0)) 1
  have hC2 : 2 ≤ C := by omega
  refine ⟨C, n0, hC2, fun n hn => ?_⟩
  have hn_exp : n0_exp ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn_2 : 4 * (s0 * w) + s0 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  rcases hG_ex n hn_exp with ⟨G, hLd, hRd, hE⟩
  have hLdC : LeftDegLe G C := fun i => (hLd i).trans (hbw.trans (by omega))
  have hRdC : RightDegLe G C := fun j => (hRd j).trans (hbw.trans (by omega))
  refine ⟨G, hLdC, hRdC, ?_, ?_⟩
  · intro a h t r p q f menu W lift k ht hcert extra hr hmenu π href
    let V := GEdge G
    let F := funGraphPHP G
    have hk1 : 1 ≤ k := le_max_left 1 (p * q)
    let ell := Nat.clog 2 (π.length + 1)
    by_cases hn_small : n < 2 * (s0 * w) * (16 * k + 4 * w)
    · have h1 : 2 * (s0 * w) * (16 * k + 4 * w) ≤ C * k := by
        have hC_ge : 4 * s0 * w * (16 + 4 * w) ≤ C := by omega
        have h16 : 16 * k + 4 * w ≤ (16 + 4 * w) * k := by nlinarith
        nlinarith
      have hCk : C * k ≤ C ^ k := by
        have hC4 : 4 ≤ C := by
          have : 4 * s0 * w * (16 + 4 * w) + 2 ≤ C := le_max_right _ _
          have : 1 ≤ s0 * w := by nlinarith
          nlinarith
        have h2k : k ≤ C ^ (k - 1) := by
          rcases Nat.exists_eq_add_of_le hk1 with ⟨m, hm⟩
          have hkm : k = m + 1 := by omega
          rw [hkm, Nat.add_sub_cancel]
          have hle : ∀ t0 : ℕ, t0 + 1 ≤ 4 ^ t0 := by
            intro t0
            induction t0 with
            | zero => simp
            | succ t' ih =>
              have h1 : 1 ≤ 4 ^ t' := Nat.one_le_pow _ _ (by omega)
              rw [pow_succ]; omega
          exact (hle m).trans (Nat.pow_le_pow_left hC4 m)
        have hpow : C ^ k = C * C ^ (k - 1) := by
          rcases Nat.exists_eq_add_of_le hk1 with ⟨m, hm⟩
          have hkm : k = m + 1 := by omega
          rw [hkm, Nat.add_sub_cancel, pow_succ, mul_comm]
        rw [hpow]; exact Nat.mul_le_mul_left C h2k
      have htr : 1 ≤ t * (r + ell + 1) := by nlinarith
      nlinarith
    · push Not at hn_small
      have hpdt_a : ∀ i : Fin a, ∃ t : PDT V, t.depth ≤ p * q ∧ ∀ x : V → Bool, t.eval x = f x i :=
        fun i => exists_pdt_of_certs (fun x => f x i) p q (fun x => hcert x i)
      let pdt : V ⊕ Fin a → PDT V := fun w =>
        match w with
        | Sum.inl v => PDT.branch {v} (PDT.leaf false) (PDT.leaf true)
        | Sum.inr i => Classical.choose (hpdt_a i)
      have hpdt_d : ∀ w, (pdt w).depth ≤ k := by
        rintro (v | i)
        · dsimp only [pdt, PDT.depth]; omega
        · exact (Classical.choose_spec (hpdt_a i)).1.trans (le_max_right 1 (p * q))
      have hpdt_ev : ∀ x : V → Bool, ∀ w : V ⊕ Fin a, (pdt w).eval x = Sum.elim x (f x) w := by
        intro x w
        rcases w with v | i
        · dsimp only [pdt, PDT.eval, Sum.elim_inl]
          have hiff : LinEqSat x ({v}, true) ↔ x v = true := by
            simp only [LinEqSat, Finset.filter_singleton]
            cases hx : x v <;> simp
          split_ifs with hs
          · exact (hiff.mp hs).symm
          · exact (Bool.eq_false_of_not_eq_true (fun h => hs (hiff.mpr h))).symm
        · exact (Classical.choose_spec (hpdt_a i)).2 x
      let As : Fin t → Finset (Clause (V ⊕ Fin a)) := fun j =>
        (π.filter (fun C => @decide (C ∈ extra ∧ ¬ isSatByMenu (menu j) C) (Classical.propDecidable _))).toFinset.image stripMenu
      have hAc : ∀ j : Fin t, (As j).card ≤ π.length := fun j =>
        Finset.card_image_le.trans ((List.toFinset_card_le _).trans (List.length_filter_le _ _))
      have hAr : ∀ j : Fin t, ∀ D ∈ As j, D.card ≤ r := by
        intro j D hD
        rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
        have hC' := List.mem_filter.mp (List.mem_toFinset.mp hC)
        have hCe : C ∈ extra := (@of_decide_eq_true _ (Classical.propDecidable _) hC'.2).1
        exact (stripMenu_card_le C).trans (hr C hCe)
      have htr_j : ∀ j : Fin t, ∃ σ : List (LinKLine V),
          IsLinKDerivation k IsLinKWeakening
            ((fun C => linKOfClause C) '' F ∪ (fun C : Clause (V ⊕ Fin a) => C.biUnion (fun l => (pdt l.1).leaves l.2 ∅)) '' (↑(As j) : Set (Clause (V ⊕ Fin a)))) σ ∧
          (∅ : LinKLine V) ∈ σ ∧ σ.length ≤ (3 * 2 ^ k) * π.length := by
        intro j
        rcases translate_menu_derivation hk1 F extra (menu j) pdt hpdt_d (fun _ => rfl) (As j) href.1
          (fun C hC hCe hns => Finset.mem_image.mpr ⟨C, List.mem_toFinset.mpr (List.mem_filter.mpr
            ⟨hC, @decide_eq_true _ (Classical.propDecidable _) ⟨hCe, hns⟩⟩), rfl⟩) with
          ⟨σ, hder, hmem, hlen⟩
        have hemp : (∅ : LinKLine V) ∈ σ := by
          have h := hmem ∅ href.2 (by rintro ⟨u, hu⟩; cases hu)
          simpa [stripMenu] using h
        exact ⟨σ, hder, hemp, hlen⟩
      let σs : Fin t → List (LinKLine V) := fun j => Classical.choose (htr_j j)
      have hFne : ∃ C0 : Clause V, C0 ∈ F := ⟨pigeonCl G 0, Or.inl (Or.inl ⟨0, rfl⟩)⟩
      have hsem0 : ∀ x : V → Bool,
          (∃ j : Fin t, j.val < t ∧ ∀ D ∈ As j, ClauseSat (fun w => (pdt w).eval x) D) ∨
          ClauseSat (fun w => (pdt w).eval x) (∅ : Clause (V ⊕ Fin a)) := by
        intro x
        left
        rcases hmenu x with ⟨j, hj⟩
        refine ⟨j, j.isLt, fun D hD => ?_⟩
        rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
        have hC' := List.mem_filter.mp (List.mem_toFinset.mp hC)
        have hCprop := @of_decide_eq_true _ (Classical.propDecidable _) hC'.2
        have hsat := stripMenu_sat_of_not_menu (menu j) (Sum.elim x (f x)) C hCprop.2 (hj C hCprop.1)
        have heq_f : (fun w => (pdt w).eval x) = Sum.elim x (f x) := funext (hpdt_ev x)
        rw [heq_f]; exact hsat
      rcases combine_advice_refutations hk1 F hFne pdt hpdt_d As hAc hAr σs
        (fun j => (Classical.choose_spec (htr_j j)).1)
        (fun j => (Classical.choose_spec (htr_j j)).2.1)
        (fun j => (Classical.choose_spec (htr_j j)).2.2)
        t le_rfl ∅ (by simp) hsem0 with ⟨ρ, hρ_der, hρ_emp, hρ_len⟩
      simp only [Finset.biUnion_empty] at hρ_emp
      have hbound := H.LinKGrow.graph_bound hL b s0 n k w rfl hs0 hk1 G hLd hE hn_small hn_2 ρ ⟨hρ_der, hρ_emp⟩
      have hpi_le : π.length + 1 ≤ 2 ^ ell := Nat.le_pow_clog (by omega) (π.length + 1)
      have hClb : 65536 * s0 ^ 2 * w ^ 3 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
      exact lower_bound_arith hs0 hw2 hk1 ht hClb hpi_le hρ_len hbound
  · have hs1 : 1 ≤ n / s0 := (Nat.le_div_iff_mul_le hs0).mpr (by omega)
    rcases upper_bound_chain G hLd hRd hE hs1 with ⟨h, t, menu, extra, π, h1, h2, h3, h4, h5⟩
    refine ⟨h, t, menu, extra, π, h1, h2, h3, ?_, ?_⟩
    · have hCub : C_ub ≤ C := (le_max_right _ _).trans (le_max_left _ _)
      have hlin : (n + 1) + n * b ^ 2 + (n + 1) * b ^ 2 ≤ (3 * b ^ 2 + 2) * n := by nlinarith
      have hbound1 : (3 * w + 6) * ((n + 1) + n * b ^ 2 + (n + 1) * b ^ 2) + 3 ≤ C_ub * n := by
        dsimp only [C_ub]
        have := Nat.mul_le_mul_left (3 * w + 6) hlin
        nlinarith
      exact h4.trans (hbound1.trans (Nat.mul_le_mul_right n hCub))
    · intro D hD
      have hCub : C_ub ≤ C := (le_max_right _ _).trans (le_max_left _ _)
      have := h5 D hD
      dsimp only [C_ub] at hCub
      omega

end L_pcx_377_Main

end PEqualNP.Outside.L_pcx_377


theorem PEqualNP.Outside.L_pcx_377 :
∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.Expanders.funGraphPHP G
    (∀ (a h t r p q : ℕ) (f : (V → Bool) → Fin a → Bool)
    (menu : Fin t → Fin h → Bool),
      let W := (V ⊕ Fin a) ⊕ Fin h
      let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
      let k := max 1 (p*q)
      0 < t →
      (∀ (x : V → Bool) (i : Fin a), ∃ T : PEqualNP.ProofComplexity.LinTerm V,
        T.card ≤ (if f x i then q else p) ∧ PEqualNP.ProofComplexity.LinTermSat x T ∧
        ∀ y : V → Bool, PEqualNP.ProofComplexity.LinTermSat y T → f y i = f x i) →
      ∀ extra : Set (PEqualNP.ProofComplexity.Clause W),
        (∀ D ∈ extra, (D.filter (fun l => l.1.isLeft)).card ≤ r) →
        (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
          (Sum.elim (Sum.elim x (f x)) (menu j)) extra) →
        ∀ π : List (PEqualNP.ProofComplexity.Clause W),
          PEqualNP.ProofComplexity.IsRefutation (Set.image lift F ∪ extra) π →
          n ≤ C^k * t * (r + Nat.clog 2 (π.length+1) + 1)) ∧
    ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
        (extra : Finset (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))
        (π : List (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h))),
      let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
        cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin h), l.2))
      (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
      (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
        (Sum.elim x (menu j)) (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) ∧
      PEqualNP.ProofComplexity.IsRefutation
        (Set.image lift F ∪ (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) π ∧
      h + t + extra.card + π.length ≤ C*n ∧ ∀ D ∈ π, D.card ≤ C :=
  PEqualNP.Outside.L_pcx_377.main
