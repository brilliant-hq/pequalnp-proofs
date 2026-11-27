import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_861_aux

open scoped BigOperators

abbrev F2 := ZMod 2

lemma card_submodule (d : Nat) (U : Submodule F2 (Fin d → F2)) :
    Nat.card U = 2 ^ Module.finrank F2 U := by
  classical
  rw [Nat.card_eq_fintype_card (α := ↥U),
      Module.card_eq_pow_finrank (K := F2) (V := ↥U), ZMod.card]

noncomputable def ortho (d : Nat) (O : Submodule F2 (Fin d → F2)) : Submodule F2 (Fin d → F2) :=
  (O.map (dotProductEquiv F2 (Fin d)).toLinearMap).dualCoannihilator

lemma mem_ortho (d : Nat) (O : Submodule F2 (Fin d → F2)) (z : Fin d → F2) :
    z ∈ ortho d O ↔ ∀ v ∈ O, dotProduct v z = 0 := by
  simp only [ortho, Submodule.mem_dualCoannihilator, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · intro h v hv
    exact h _ ⟨v, hv, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩
    exact h v hv

lemma finrank_ortho (d : Nat) (O : Submodule F2 (Fin d → F2)) :
    Module.finrank F2 O + Module.finrank F2 (ortho d O) = d := by
  have h1 : Module.finrank F2 (O.map (dotProductEquiv F2 (Fin d)).toLinearMap) =
      Module.finrank F2 O :=
    LinearEquiv.finrank_map_eq (dotProductEquiv F2 (Fin d)) O
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (O.map (dotProductEquiv F2 (Fin d)).toLinearMap)
  rw [Module.finrank_fin_fun, h1] at h2
  exact h2

lemma finrank_le_d (d : Nat) (O : Submodule F2 (Fin d → F2)) :
    Module.finrank F2 O ≤ d := by
  have h := finrank_ortho d O
  omega

lemma card_piece (d : Nat) (O : Submodule F2 (Fin d → F2)) (x : Fin d → F2)
    [DecidablePred fun y : Fin d → F2 => ∀ v ∈ O, dotProduct v (y - x) = 0] :
    (Finset.univ.filter fun y : Fin d → F2 => ∀ v ∈ O, dotProduct v (y - x) = 0).card =
      2 ^ (d - Module.finrank F2 O) := by
  have heq : (Finset.univ.filter fun y : Fin d → F2 => ∀ v ∈ O, dotProduct v (y - x) = 0).card =
      Nat.card (ortho d O) := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine
      { toFun := fun y => ⟨y.1 - x, (mem_ortho d O _).2 (Finset.mem_filter.mp y.2).2⟩
        invFun := fun z => ⟨z.1 + x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [add_sub_cancel_right] using (mem_ortho d O z.1).1 z.2⟩⟩
        left_inv := fun y => Subtype.ext (sub_add_cancel y.1 x)
        right_inv := fun z => Subtype.ext (add_sub_cancel_right z.1 x) }
  rw [heq, card_submodule]
  have h := finrank_ortho d O
  congr 1
  omega

lemma finrank_map_mkQ_add_inf {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (O B : Submodule F2 V) :
    Module.finrank F2 (B.map O.mkQ) + Module.finrank F2 (O ⊓ B : Submodule F2 V) =
      Module.finrank F2 B := by
  have hr : LinearMap.range (O.mkQ.domRestrict B) = B.map O.mkQ :=
    LinearMap.range_domRestrict _ _
  have hk : LinearMap.ker (O.mkQ.domRestrict B) = (O ⊓ B).comap B.subtype := by
    ext ⟨x, hx⟩
    simp [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (O.mkQ.domRestrict B)
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at hrn
  exact hrn

lemma map_mkQ_inf_of_le_left {V : Type*} [AddCommGroup V] [Module F2 V]
    (O A B : Submodule F2 V) (hOA : O ≤ A) :
    (A.map O.mkQ) ⊓ (B.map O.mkQ) = (A ⊓ B).map O.mkQ := by
  apply le_antisymm
  · rintro q ⟨hqA, hqB⟩
    rcases Submodule.mem_map.mp hqA with ⟨a, ha, rfl⟩
    rcases Submodule.mem_map.mp hqB with ⟨b, hb, hba⟩
    have hsub : b - a ∈ O := by
      have : O.mkQ (b - a) = 0 := by rw [map_sub, hba, sub_self]
      exact (Submodule.ker_mkQ O) ▸ this
    have hbA : b ∈ A := by
      have := A.add_mem ha (hOA hsub)
      simpa [add_sub_cancel] using this
    exact Submodule.mem_map.mpr ⟨b, ⟨hbA, hb⟩, hba⟩
  · exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)

lemma map_mkQ_inf_of_le_right {V : Type*} [AddCommGroup V] [Module F2 V]
    (O A B : Submodule F2 V) (hOB : O ≤ B) :
    (A.map O.mkQ) ⊓ (B.map O.mkQ) = (A ⊓ B).map O.mkQ := by
  rw [inf_comm, map_mkQ_inf_of_le_left O B A hOB, inf_comm]

lemma finrank_bot_mkQ_inf {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (A B : Submodule F2 V) :
    Module.finrank F2 (((A.map (⊥ : Submodule F2 V).mkQ) ⊓ (B.map (⊥ : Submodule F2 V).mkQ)) :
        Submodule F2 (V ⧸ (⊥ : Submodule F2 V))) =
      Module.finrank F2 (A ⊓ B : Submodule F2 V) := by
  rw [map_mkQ_inf_of_le_left ⊥ A B bot_le]
  have h := finrank_map_mkQ_add_inf (⊥ : Submodule F2 V) (A ⊓ B)
  have hbot : (⊥ : Submodule F2 V) ⊓ (A ⊓ B) = ⊥ := bot_inf_eq _
  rw [hbot, finrank_bot, add_zero] at h
  exact h

lemma cover_card_le {α : Type*} [Fintype α] [DecidableEq α] {n : Nat}
    (P : Fin n → Finset α) (hcov : ∀ y : α, ∃ i : Fin n, y ∈ P i) :
    Fintype.card α ≤ ∑ i : Fin n, (P i).card ∧
    (∑ i : Fin n, (P i).card = Fintype.card α ↔
      ∀ i j : Fin n, i ≠ j → Disjoint (P i) (P j)) := by
  have huniv : Finset.univ.biUnion P = Finset.univ := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    exact hcov y
  have hle : Fintype.card α ≤ ∑ i : Fin n, (P i).card := by
    calc Fintype.card α = (Finset.univ : Finset α).card := rfl
      _ = (Finset.univ.biUnion P).card := by rw [huniv]
      _ ≤ ∑ i : Fin n, (P i).card := Finset.card_biUnion_le
  refine ⟨hle, ?_⟩
  constructor
  · intro heq i j hij
    by_contra hnd
    rw [Finset.not_disjoint_iff] at hnd
    rcases hnd with ⟨y, hyi, hyj⟩
    have hdecomp : Finset.univ.biUnion P = P i ∪ (Finset.univ.erase i).biUnion P := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase, Finset.mem_univ,
        true_and, and_true]
      constructor
      · rintro ⟨k, hzk⟩
        by_cases hki : k = i
        · left; subst hki; exact hzk
        · right; exact ⟨k, hki, hzk⟩
      · rintro (hz | ⟨k, _, hzk⟩)
        · exact ⟨i, hz⟩
        · exact ⟨k, hzk⟩
    have hy_rest : y ∈ (Finset.univ.erase i).biUnion P :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩, hyj⟩
    have hlt_u : (P i ∪ (Finset.univ.erase i).biUnion P).card <
        (P i).card + ((Finset.univ.erase i).biUnion P).card := by
      have hadd := Finset.card_union_add_card_inter (P i) ((Finset.univ.erase i).biUnion P)
      have hpos : 0 < (P i ∩ (Finset.univ.erase i).biUnion P).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨hyi, hy_rest⟩⟩
      omega
    have hrest_le : ((Finset.univ.erase i).biUnion P).card ≤
        ∑ k ∈ Finset.univ.erase i, (P k).card := Finset.card_biUnion_le
    have hsum_split : ∑ k : Fin n, (P k).card = (P i).card + ∑ k ∈ Finset.univ.erase i, (P k).card :=
      (Finset.add_sum_erase Finset.univ (fun k => (P k).card) (Finset.mem_univ i)).symm
    have hcard_eq : (Finset.univ.biUnion P).card = Fintype.card α := by rw [huniv]; rfl
    rw [hdecomp] at hcard_eq
    omega
  · intro hdisj
    have hbi := Finset.card_biUnion (s := (Finset.univ : Finset (Fin n))) (t := P) (by
      intro i _ j _ hij
      exact hdisj i j hij)
    rw [huniv] at hbi
    exact hbi.symm

lemma sum_le_iff_eq {n : Nat} (f g : Fin n → Nat) (hle : ∀ i, f i ≤ g i) :
    (∑ i : Fin n, f i = ∑ i : Fin n, g i) ↔ ∀ i : Fin n, f i = g i := by
  constructor
  · intro heq i
    by_contra hne
    have hlt : f i < g i := lt_of_le_of_ne (hle i) hne
    have hsum_lt : ∑ k : Fin n, f k < ∑ k : Fin n, g k :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ i, hlt⟩
    omega
  · intro h
    exact Finset.sum_congr rfl (fun i _ => h i)

lemma main_proof :
    ∀ (d l h e : Nat),
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let W := Fin d → F
      ∀ (leaf : Fin l → Submodule F W) (cut : Fin h → Fin e → Fin l → Bool),
        let side := fun (t : Fin h) (j : Fin e) (c : Bool) =>
          Submodule.span F {v : W | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}
        let boundary := fun (t : Fin h) (j : Fin e) => side t j true ⊓ side t j false
        let profile := fun (O : Submodule F W) (t : Fin h) (j : Fin e) =>
          Module.finrank F (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) : Submodule F (W ⧸ O))
        let peak := fun (O : Submodule F W) (t : Fin h) =>
          (Finset.univ : Finset (Fin e)).sup (profile O t)
        (∀ (t : Fin h) (i j : Fin e), ∃ a b : Bool,
          ∀ u : Fin l, cut t i u = a → cut t j u = b) →
        ∀ (w : Nat), IsLeast {z : Nat | ∃ t : Fin h, peak ⊥ t = z} w →
        let piece := fun (O : Submodule F W) (x : W) =>
          {y : W | ∀ v ∈ O, dotProduct v (y-x) = 0}
        (∀ (charge : (Fin e → Nat) → Nat) (budget : Nat),
          ((∃ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
              (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) ∧
              (∑ i : Fin n, charge (profile (masks i) (layout i))) ≤ budget) ↔
            ∃ (O : Submodule F W) (t : Fin h),
              2^(Module.finrank F O) * charge (profile O t) ≤ budget)) ∧
        (∀ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
          (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) →
          let total := ∑ i : Fin n, 2^(peak (masks i) (layout i))
          2^w ≤ total ∧
          (total = 2^w ↔
            (∀ i j : Fin n, i ≠ j → Disjoint (piece (masks i) (rep i)) (piece (masks j) (rep j))) ∧
            ∀ i : Fin n, let O := masks i; let t := layout i; let s := Module.finrank F O
              s ≤ w ∧ peak ⊥ t = w ∧ ∀ j : Fin e, s + Module.finrank F (boundary t j) ≤
                w + Module.finrank F ((O ⊓ boundary t j) : Submodule F W))) := by
  intro d l h e F W leaf cut side boundary profile peak hlam w hw piece
  classical
  have hprof_bot : ∀ (t : Fin h) (j : Fin e), profile ⊥ t j = Module.finrank F (boundary t j) := by
    intro t j
    exact finrank_bot_mkQ_inf (side t j true) (side t j false)
  have hprof_ge : ∀ (O : Submodule F W) (t : Fin h) (j : Fin e),
      Module.finrank F (boundary t j) ≤ profile O t j + Module.finrank F (O ⊓ boundary t j : Submodule F W) := by
    intro O t j
    have hmap : (boundary t j).map O.mkQ ≤ ((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) :=
      le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)
    have hle : Module.finrank F ((boundary t j).map O.mkQ) ≤ profile O t j :=
      Submodule.finrank_mono hmap
    have hrn : Module.finrank F ((boundary t j).map O.mkQ) +
        Module.finrank F (O ⊓ boundary t j : Submodule F W) = Module.finrank F (boundary t j) :=
      finrank_map_mkQ_add_inf O (boundary t j)
    omega
  have hpeak_ge : ∀ (O : Submodule F W) (t : Fin h),
      peak ⊥ t ≤ peak O t + Module.finrank F O := by
    intro O t
    apply Finset.sup_le
    intro j _
    have h1 := hprof_ge O t j
    have h2 : Module.finrank F (O ⊓ boundary t j : Submodule F W) ≤ Module.finrank F O :=
      Submodule.finrank_mono inf_le_left
    have h3 : profile O t j ≤ peak O t := Finset.le_sup (f := profile O t) (Finset.mem_univ j)
    rw [hprof_bot t j]
    omega
  have hw_le : ∀ t : Fin h, w ≤ peak ⊥ t := by
    intro t
    exact hw.2 ⟨t, rfl⟩
  have hpeak_add_ge_w : ∀ (O : Submodule F W) (t : Fin h),
      w ≤ peak O t + Module.finrank F O := by
    intro O t
    exact le_trans (hw_le t) (hpeak_ge O t)
  have hcardW : Fintype.card W = 2 ^ d := by
    simp [W, F, ZMod.card]
  have h2d_pos : 0 < 2 ^ d := Nat.pow_pos (by omega)
  constructor
  · intro charge budget
    constructor
    · rintro ⟨n, masks, rep, layout, hcov, hbud⟩
      rcases hcov 0 with ⟨i_ex, _⟩
      have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i_ex, Finset.mem_univ _⟩
      obtain ⟨i0, _, hi0_min⟩ := Finset.exists_min_image Finset.univ
        (fun i : Fin n => 2 ^ Module.finrank F (masks i) * charge (profile (masks i) (layout i))) hne
      refine ⟨masks i0, layout i0, ?_⟩
      let M := 2 ^ Module.finrank F (masks i0) * charge (profile (masks i0) (layout i0))
      let P : Fin n → Finset W := fun i => Finset.univ.filter fun y => y ∈ piece (masks i) (rep i)
      have hP_card : ∀ i : Fin n, (P i).card = 2 ^ (d - Module.finrank F (masks i)) := by
        intro i
        exact card_piece d (masks i) (rep i)
      have hP_cov : ∀ y : W, ∃ i : Fin n, y ∈ P i := by
        intro y
        rcases hcov y with ⟨i, hi⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have hsum_ge : 2 ^ d ≤ ∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i)) := by
        have h1 := (cover_card_le P hP_cov).1
        rw [hcardW] at h1
        simpa [hP_card] using h1
      have hstep : (∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i))) * M ≤
          2 ^ d * ∑ i : Fin n, charge (profile (masks i) (layout i)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hmi : M ≤ 2 ^ Module.finrank F (masks i) * charge (profile (masks i) (layout i)) :=
          hi0_min i (Finset.mem_univ _)
        have hle_d : Module.finrank F (masks i) ≤ d := finrank_le_d d (masks i)
        calc 2 ^ (d - Module.finrank F (masks i)) * M
            ≤ 2 ^ (d - Module.finrank F (masks i)) *
                (2 ^ Module.finrank F (masks i) * charge (profile (masks i) (layout i))) :=
              Nat.mul_le_mul_left _ hmi
          _ = (2 ^ (d - Module.finrank F (masks i)) * 2 ^ Module.finrank F (masks i)) *
                charge (profile (masks i) (layout i)) := by ring
          _ = 2 ^ d * charge (profile (masks i) (layout i)) := by
              rw [← pow_add, Nat.sub_add_cancel hle_d]
      have htot : 2 ^ d * M ≤ 2 ^ d * budget := by
        calc 2 ^ d * M ≤ (∑ i : Fin n, 2 ^ (d - Module.finrank F (masks i))) * M :=
              Nat.mul_le_mul_right M hsum_ge
          _ ≤ 2 ^ d * ∑ i : Fin n, charge (profile (masks i) (layout i)) := hstep
          _ ≤ 2 ^ d * budget := Nat.mul_le_mul_left _ hbud
      exact Nat.le_of_mul_le_mul_left htot h2d_pos
    · rintro ⟨O, t, hle⟩
      let Q := W ⧸ ortho d O
      have hQ_finrank : Module.finrank F Q = Module.finrank F O := by
        have hrn := Submodule.finrank_quotient_add_finrank (ortho d O)
        have ho : Module.finrank F O + Module.finrank F (ortho d O) = d := finrank_ortho d O
        rw [Module.finrank_fin_fun] at hrn
        change Module.finrank F Q + Module.finrank F (ortho d O) = d at hrn
        omega
      have hQ_card : Fintype.card Q = 2 ^ Module.finrank F O := by
        rw [Module.card_eq_pow_finrank (K := F) (V := Q), ZMod.card, hQ_finrank]
      let n := 2 ^ Module.finrank F O
      let eQ : Fin n ≃ Q := (Fintype.equivFinOfCardEq hQ_card).symm
      refine ⟨n, fun _ => O, fun i => Quotient.out (eQ i), fun _ => t, ?_, ?_⟩
      · intro y
        let i := eQ.symm ((ortho d O).mkQ y)
        refine ⟨i, ?_⟩
        have hq : (ortho d O).mkQ (Quotient.out (eQ i)) = (ortho d O).mkQ y := by
          have h1 : (ortho d O).mkQ (Quotient.out (eQ i)) = eQ i := Submodule.Quotient.mk_out (eQ i)
          rw [h1]
          simp [i]
        have hsub : y - Quotient.out (eQ i) ∈ ortho d O := by
          have : (ortho d O).mkQ (y - Quotient.out (eQ i)) = 0 := by
            rw [map_sub, hq, sub_self]
          exact (Submodule.Quotient.mk_eq_zero (ortho d O)).mp this
        exact (mem_ortho d O _).1 hsub
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        exact hle
  · intro n masks rep layout hcov total
    let P : Fin n → Finset W := fun i => Finset.univ.filter fun y => y ∈ piece (masks i) (rep i)
    have hP_card : ∀ i : Fin n, (P i).card = 2 ^ (d - Module.finrank F (masks i)) := by
      intro i
      exact card_piece d (masks i) (rep i)
    have hP_cov : ∀ y : W, ∃ i : Fin n, y ∈ P i := by
      intro y
      rcases hcov y with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have hcov_res := cover_card_le P hP_cov
    have hsumP_ge : 2 ^ d ≤ ∑ i : Fin n, (P i).card := by
      rw [← hcardW]
      exact hcov_res.1
    have hterm_le : ∀ i : Fin n, (P i).card * 2 ^ w ≤ 2 ^ d * 2 ^ peak (masks i) (layout i) := by
      intro i
      rw [hP_card i]
      have hle_d : Module.finrank F (masks i) ≤ d := finrank_le_d d (masks i)
      have hge_w : w ≤ peak (masks i) (layout i) + Module.finrank F (masks i) :=
        hpeak_add_ge_w (masks i) (layout i)
      calc 2 ^ (d - Module.finrank F (masks i)) * 2 ^ w
          ≤ 2 ^ (d - Module.finrank F (masks i)) * 2 ^ (peak (masks i) (layout i) + Module.finrank F (masks i)) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hge_w)
        _ = 2 ^ (d - Module.finrank F (masks i) + Module.finrank F (masks i) + peak (masks i) (layout i)) := by
            rw [← pow_add]
            congr 1
            omega
        _ = 2 ^ d * 2 ^ peak (masks i) (layout i) := by
            rw [Nat.sub_add_cancel hle_d, pow_add]
    have hsum_le : (∑ i : Fin n, (P i).card) * 2 ^ w ≤ 2 ^ d * total := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hterm_le i)
    have h2w_le_tot : 2 ^ w ≤ total := by
      have hmul : 2 ^ d * 2 ^ w ≤ 2 ^ d * total :=
        le_trans (Nat.mul_le_mul_right (2 ^ w) hsumP_ge) hsum_le
      exact Nat.le_of_mul_le_mul_left hmul h2d_pos
    refine ⟨h2w_le_tot, ?_⟩
    have hdisj_equiv :
        (∀ i j : Fin n, i ≠ j → Disjoint (P i) (P j)) ↔
        (∀ i j : Fin n, i ≠ j → Disjoint (piece (masks i) (rep i)) (piece (masks j) (rep j))) := by
      constructor
      · intro h i j hij
        rw [Set.disjoint_left]
        intro y hyi hyj
        exact (Finset.disjoint_left.mp (h i j hij))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyi⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyj⟩)
      · intro h i j hij
        rw [Finset.disjoint_left]
        intro y hyi hyj
        exact (Set.disjoint_left.mp (h i j hij))
          (Finset.mem_filter.mp hyi).2 (Finset.mem_filter.mp hyj).2
    have hcrit : ∀ (O : Submodule F W) (t : Fin h),
        let s := Module.finrank F O
        (peak O t + s = w) ↔
        (s ≤ w ∧ peak ⊥ t = w ∧ ∀ j : Fin e, s + Module.finrank F (boundary t j) ≤
          w + Module.finrank F ((O ⊓ boundary t j) : Submodule F W)) := by
      intro O t s
      constructor
      · intro heq
        have hsw : s ≤ w := by omega
        have hbot_w : peak ⊥ t = w := by
          have h1 := hw_le t
          have h2 := hpeak_ge O t
          omega
        refine ⟨hsw, hbot_w, fun j => ?_⟩
        have h1 := hprof_ge O t j
        have h2 : profile O t j ≤ peak O t := Finset.le_sup (f := profile O t) (Finset.mem_univ j)
        omega
      · rintro ⟨hsw, hbot_w, hcut⟩
        have hge := hpeak_add_ge_w O t
        suffices hle : peak O t + s ≤ w by omega
        by_cases hs0 : s = 0
        · have hObot : O = ⊥ := Submodule.finrank_eq_zero.mp hs0
          rw [hObot, hs0, add_zero, hbot_w]
        · have hw_pos : 0 < w := by omega
          have he_ne : (Finset.univ : Finset (Fin e)).Nonempty := by
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            have h0 : peak ⊥ t = 0 := by simp [peak, hemp]
            omega
          obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_sup Finset.univ he_ne (profile ⊥ t)
          have hj0_eq : Module.finrank F (boundary t j0) = w := by
            rw [← hprof_bot t j0, ← hj0]
            exact hbot_w
          have hO_le_b0 : O ≤ boundary t j0 := by
            have hc0 := hcut j0
            rw [hj0_eq] at hc0
            have hfin_eq : Module.finrank F (O ⊓ boundary t j0 : Submodule F W) = Module.finrank F O := by
              have hle_O : Module.finrank F (O ⊓ boundary t j0 : Submodule F W) ≤ Module.finrank F O :=
                Submodule.finrank_mono inf_le_left
              omega
            have hinf_eq : O ⊓ boundary t j0 = O :=
              Submodule.eq_of_le_of_finrank_eq inf_le_left hfin_eq
            exact inf_eq_left.mp hinf_eq
          have hprof_le : ∀ j : Fin e, profile O t j + s ≤ w := by
            intro j
            rcases hlam t j0 j with ⟨a, b, hab⟩
            have hside_le : side t j0 a ≤ side t j b := by
              apply Submodule.span_mono
              rintro v ⟨u, hu, hv⟩
              exact ⟨u, hab u hu, hv⟩
            have hO_le_side : O ≤ side t j b := by
              cases a with
              | true => exact le_trans (le_trans hO_le_b0 inf_le_left) hside_le
              | false => exact le_trans (le_trans hO_le_b0 inf_le_right) hside_le
            have hmap_eq : ((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) =
                (boundary t j).map O.mkQ := by
              cases b with
              | true => exact map_mkQ_inf_of_le_left O (side t j true) (side t j false) hO_le_side
              | false => exact map_mkQ_inf_of_le_right O (side t j true) (side t j false) hO_le_side
            have hprof_eq : profile O t j + Module.finrank F (O ⊓ boundary t j : Submodule F W) =
                Module.finrank F (boundary t j) := by
              change Module.finrank F (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) :
                  Submodule F (W ⧸ O)) + _ = _
              rw [hmap_eq]
              exact finrank_map_mkQ_add_inf O (boundary t j)
            have hcj := hcut j
            omega
          have hsup : peak O t ≤ w - s := by
            apply Finset.sup_le
            intro j _
            have := hprof_le j
            omega
          omega
    constructor
    · intro htot_eq
      have hmul_eq : 2 ^ d * 2 ^ w = 2 ^ d * total := by rw [htot_eq]
      have h1_eq : (∑ i : Fin n, (P i).card) * 2 ^ w = 2 ^ d * 2 ^ w := by
        have ha := Nat.mul_le_mul_right (2 ^ w) hsumP_ge
        omega
      have hsumP_eq : ∑ i : Fin n, (P i).card = Fintype.card W := by
        rw [hcardW]
        have h2w_pos : 0 < 2 ^ w := Nat.pow_pos (by omega)
        exact Nat.eq_of_mul_eq_mul_right h2w_pos h1_eq
      have hdisjP : ∀ i j : Fin n, i ≠ j → Disjoint (P i) (P j) :=
        hcov_res.2.mp hsumP_eq
      have h2_eq : ∑ i : Fin n, (P i).card * 2 ^ w =
          ∑ i : Fin n, 2 ^ d * 2 ^ peak (masks i) (layout i) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        exact h1_eq.trans hmul_eq
      have hall_eq := (sum_le_iff_eq (fun i => (P i).card * 2 ^ w)
        (fun i => 2 ^ d * 2 ^ peak (masks i) (layout i)) hterm_le).mp h2_eq
      refine ⟨hdisj_equiv.mp hdisjP, fun i => (hcrit (masks i) (layout i)).mp ?_⟩
      have hi := hall_eq i
      rw [hP_card i] at hi
      have hle_d : Module.finrank F (masks i) ≤ d := finrank_le_d d (masks i)
      have hpow_eq : 2 ^ (d - Module.finrank F (masks i) + w) =
          2 ^ (d + peak (masks i) (layout i)) := by
        rw [pow_add, pow_add]
        exact hi
      have hexp_eq : d - Module.finrank F (masks i) + w = d + peak (masks i) (layout i) :=
        Nat.pow_right_injective (by omega) hpow_eq
      omega
    · rintro ⟨hdisj, hall⟩
      have hsumP_eq : ∑ i : Fin n, (P i).card = 2 ^ d := by
        rw [← hcardW]
        exact hcov_res.2.mpr (hdisj_equiv.mpr hdisj)
      have hterm_eq : ∀ i : Fin n, (P i).card * 2 ^ w = 2 ^ d * 2 ^ peak (masks i) (layout i) := by
        intro i
        have hpeq := (hcrit (masks i) (layout i)).mpr (hall i)
        rw [hP_card i]
        have hle_d : Module.finrank F (masks i) ≤ d := finrank_le_d d (masks i)
        calc 2 ^ (d - Module.finrank F (masks i)) * 2 ^ w
            = 2 ^ (d - Module.finrank F (masks i) + (peak (masks i) (layout i) + Module.finrank F (masks i))) := by
              rw [← pow_add, hpeq]
          _ = 2 ^ (d + peak (masks i) (layout i)) := by congr 1; omega
          _ = 2 ^ d * 2 ^ peak (masks i) (layout i) := pow_add _ _ _
      have hmul_eq : 2 ^ d * total = 2 ^ d * 2 ^ w := by
        calc 2 ^ d * total = ∑ i : Fin n, 2 ^ d * 2 ^ peak (masks i) (layout i) := Finset.mul_sum ..
          _ = ∑ i : Fin n, (P i).card * 2 ^ w := Finset.sum_congr rfl (fun i _ => (hterm_eq i).symm)
          _ = (∑ i : Fin n, (P i).card) * 2 ^ w := (Finset.sum_mul ..).symm
          _ = 2 ^ d * 2 ^ w := by rw [hsumP_eq]
      exact Nat.eq_of_mul_eq_mul_left h2d_pos hmul_eq

end PEqualNP.Outside.L_lib_861_aux

theorem PEqualNP.Outside.L_lib_861 : (∀ (d l h e : Nat),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let W := Fin d → F
  ∀ (leaf : Fin l → Submodule F W) (cut : Fin h → Fin e → Fin l → Bool),
    let side := fun (t : Fin h) (j : Fin e) (c : Bool) =>
      Submodule.span F {v : W | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}
    let boundary := fun (t : Fin h) (j : Fin e) => side t j true ⊓ side t j false
    let profile := fun (O : Submodule F W) (t : Fin h) (j : Fin e) =>
      Module.finrank F (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) : Submodule F (W ⧸ O))
    let peak := fun (O : Submodule F W) (t : Fin h) =>
      (Finset.univ : Finset (Fin e)).sup (profile O t)
    (∀ (t : Fin h) (i j : Fin e), ∃ a b : Bool,
      ∀ u : Fin l, cut t i u = a → cut t j u = b) →
    ∀ (w : Nat), IsLeast {z : Nat | ∃ t : Fin h, peak ⊥ t = z} w →
    let piece := fun (O : Submodule F W) (x : W) =>
      {y : W | ∀ v ∈ O, dotProduct v (y-x) = 0}
    (∀ (charge : (Fin e → Nat) → Nat) (budget : Nat),
      ((∃ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
          (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) ∧
          (∑ i : Fin n, charge (profile (masks i) (layout i))) ≤ budget) ↔
        ∃ (O : Submodule F W) (t : Fin h),
          2^(Module.finrank F O) * charge (profile O t) ≤ budget)) ∧
    (∀ (n : Nat) (masks : Fin n → Submodule F W) (rep : Fin n → W) (layout : Fin n → Fin h),
      (∀ y : W, ∃ i : Fin n, y ∈ piece (masks i) (rep i)) →
      let total := ∑ i : Fin n, 2^(peak (masks i) (layout i))
      2^w ≤ total ∧
      (total = 2^w ↔
        (∀ i j : Fin n, i ≠ j → Disjoint (piece (masks i) (rep i)) (piece (masks j) (rep j))) ∧
        ∀ i : Fin n, let O := masks i; let t := layout i; let s := Module.finrank F O
          s ≤ w ∧ peak ⊥ t = w ∧ ∀ j : Fin e, s + Module.finrank F (boundary t j) ≤
            w + Module.finrank F ((O ⊓ boundary t j) : Submodule F W)))) :=
  PEqualNP.Outside.L_lib_861_aux.main_proof
