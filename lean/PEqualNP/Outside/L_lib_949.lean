import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_949_aux

open Classical

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> rfl

private lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;> rfl

private lemma msingle_apply {d : ℕ} (a b i j : Fin d) :
    Matrix.single a b (1 : ZMod 2) i j = if i = a ∧ j = b then 1 else 0 := by
  simp only [Matrix.single_apply, eq_comm]

private lemma mulVec_single_one {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (j i : Fin d) :
    M.mulVec (Pi.single j 1) i = M i j := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ j) h

private lemma zmod2_quad_alt_zero {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2))
    (hH : H.transpose = H ∧ ∀ i, H i i = 0) (v : Fin d → ZMod 2) :
    (∑ a : Fin d, ∑ b : Fin d, v a * H a b * v b) = 0 := by
  have hsym : ∀ a b : Fin d, H b a = H a b := fun a b => congrFun (congrFun hH.1 a) b
  have hsplit : (∑ a : Fin d, ∑ b : Fin d, v a * H a b * v b) =
      (∑ p : Fin d × Fin d, if p.1 < p.2 then v p.1 * H p.1 p.2 * v p.2 else 0) +
      (∑ p : Fin d × Fin d, if p.2 < p.1 then v p.1 * H p.1 p.2 * v p.2 else 0) := by
    rw [← Fintype.sum_prod_type', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, not_lt.mpr (le_of_lt hlt)]
    · rw [heq]; simp [hH.2]
    · simp [hgt, not_lt.mpr (le_of_lt hgt)]
  have hswap : (∑ p : Fin d × Fin d, if p.2 < p.1 then v p.1 * H p.1 p.2 * v p.2 else 0) =
      (∑ p : Fin d × Fin d, if p.1 < p.2 then v p.1 * H p.1 p.2 * v p.2 else 0) := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin d) (Fin d)) _ _ fun p => ?_
    dsimp only [Equiv.prodComm_apply, Prod.swap]
    by_cases h : p.2 < p.1
    · rw [if_pos h, if_pos h, hsym p.2 p.1]; ring
    · rw [if_neg h, if_neg h]
  rw [hsplit, hswap, zmod2_add_self]

private lemma alt_congr {d : ℕ} (P H : Matrix (Fin d) (Fin d) (ZMod 2))
    (hH : H.transpose = H ∧ ∀ i, H i i = 0) :
    (P * H * P.transpose).transpose = P * H * P.transpose ∧
      ∀ i, (P * H * P.transpose) i i = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1, Matrix.mul_assoc]
  · intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hexp : ∑ x : Fin d, (∑ k : Fin d, P i k * H k x) * P i x =
        ∑ k : Fin d, ∑ x : Fin d, P i k * H k x * P i x := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [hexp]
    exact zmod2_quad_alt_zero H hH (fun k => P i k)

private lemma matrix_rank_mul_le_left {d : ℕ} (A B : Matrix (Fin d) (Fin d) (ZMod 2)) :
    (A * B).rank ≤ A.rank := by
  change Module.finrank (ZMod 2) (LinearMap.range (A * B).mulVecLin) ≤
    Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin)
  rw [Matrix.mulVecLin_mul]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range B.mulVecLin A.mulVecLin)

private lemma matrix_rank_mul_le_right {d : ℕ} (A B : Matrix (Fin d) (Fin d) (ZMod 2)) :
    (A * B).rank ≤ B.rank := by
  change Module.finrank (ZMod 2) (LinearMap.range (A * B).mulVecLin) ≤
    Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le A.mulVecLin (LinearMap.range B.mulVecLin)

private lemma matrix_rank_congr {d : ℕ} (P Pinv X : Matrix (Fin d) (Fin d) (ZMod 2))
    (hPP : P * Pinv = 1) (hPP' : Pinv * P = 1) :
    (P * X * P.transpose).rank = X.rank := by
  have h1 : (P * X * P.transpose).rank ≤ X.rank :=
    le_trans (matrix_rank_mul_le_left (P * X) P.transpose) (matrix_rank_mul_le_right P X)
  have h2 : X.rank ≤ (P * X * P.transpose).rank := by
    have hX : X = Pinv * (P * X * P.transpose) * Pinv.transpose := by
      have ht : P.transpose * Pinv.transpose = 1 := by
        rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
      calc X = 1 * X * 1 := by simp
        _ = (Pinv * P) * X * (P.transpose * Pinv.transpose) := by rw [hPP', ht]
        _ = Pinv * (P * X * P.transpose) * Pinv.transpose := by simp [Matrix.mul_assoc]
    conv_lhs => rw [hX]
    exact le_trans (matrix_rank_mul_le_left _ _) (matrix_rank_mul_le_right _ _)
  exact le_antisymm h1 h2

private def canonN (d r : ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => if i.val < r ∧ j.val = i.val + r then 1 else 0

private def canonU (d r : ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  1 + canonN d r

private lemma finsupp_sum_apply {α β : Type*} [DecidableEq α] {s : Finset α}
    (f : α → β →₀ ZMod 2) (b : β) :
    (∑ a ∈ s, f a) b = ∑ a ∈ s, f a b := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]

private lemma exists_jordan_basis {d : ℕ} (U : Matrix (Fin d) (Fin d) (ZMod 2)) (hU : U * U = 1) :
    let r := (U - 1).rank
    2 * r ≤ d ∧
    ∃ (P Pinv : Matrix (Fin d) (Fin d) (ZMod 2)),
      P * Pinv = 1 ∧ Pinv * P = 1 ∧ P * U * Pinv = canonU d r := by
  let N : Matrix (Fin d) (Fin d) (ZMod 2) := U - 1
  let r := N.rank
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hr0 : r = 0 := by
      have hle : r ≤ 0 := by
        simpa [r, Matrix.rank, Module.finrank_fin_fun] using Submodule.finrank_le (LinearMap.range N.mulVecLin)
      exact Nat.eq_zero_of_le_zero hle
    refine ⟨by show 2 * r ≤ 0; omega, 1, 1, by simp, by simp, ?_⟩
    ext i; exact i.elim0
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hN_eq : N = U + 1 := by
    ext i j; simp only [N, Matrix.sub_apply, Matrix.add_apply]; exact zmod2_sub_eq_add _ _
  have hN2 : N * N = 0 := by
    rw [hN_eq]
    ext i j
    have hcalc : (U + 1) * (U + 1) = U * U + U + U + 1 := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
      abel
    rw [hcalc, hU]
    simp only [Matrix.add_apply, Matrix.zero_apply]
    have h1 := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    have h2 := zmod2_add_self (U i j)
    calc (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + U i j + U i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j
        = (U i j + U i j) + ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) := by ring
      _ = 0 := by rw [h1, h2, add_zero]
  let R := LinearMap.range N.mulVecLin
  let K := LinearMap.ker N.mulVecLin
  have hRK : R ≤ K := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hfrR : Module.finrank (ZMod 2) R = r := rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hR_le_K : r ≤ Module.finrank (ZMod 2) K := Submodule.finrank_mono hRK
  have h2r : 2 * r ≤ d := by change r + Module.finrank (ZMod 2) K = d at hrn; omega
  refine ⟨h2r, ?_⟩
  let bR := (Module.finBasis (ZMod 2) R).reindex (finCongr hfrR)
  let eR : Fin r → (Fin d → ZMod 2) := fun k => (bR k).val
  have heR_mem : ∀ k : Fin r, eR k ∈ R := fun k => (bR k).property
  let f : Fin r → (Fin d → ZMod 2) := fun k => Classical.choose (heR_mem k)
  have hf_spec : ∀ k : Fin r, N.mulVec (f k) = eR k := fun k => Classical.choose_spec (heR_mem k)
  have heR_ker : ∀ k : Fin r, N.mulVec (eR k) = 0 := fun k => hRK (heR_mem k)
  let R_in_K : Submodule (ZMod 2) K := R.comap K.subtype
  rcases Submodule.exists_isCompl R_in_K with ⟨G_in_K, hGK⟩
  let G : Submodule (ZMod 2) (Fin d → ZMod 2) := G_in_K.map K.subtype
  have hRG_bot : R ⊓ G = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvR, hvG⟩
    rcases Submodule.mem_map.mp hvG with ⟨⟨w, hwK⟩, hwG, rfl⟩
    have hmem : (⟨w, hwK⟩ : K) ∈ R_in_K ⊓ G_in_K := ⟨hvR, hwG⟩
    rw [hGK.inf_eq_bot, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hRG_sup : R ⊔ G = K := by
    apply le_antisymm
    · exact sup_le hRK (Submodule.map_subtype_le K G_in_K)
    · intro v hvK
      have htop : (⟨v, hvK⟩ : K) ∈ R_in_K ⊔ G_in_K := by rw [hGK.sup_eq_top]; trivial
      rcases Submodule.mem_sup.mp htop with ⟨⟨a, haK⟩, haR, ⟨b, hbK⟩, hbG, hab⟩
      have hv_eq : a + b = v := congrArg Subtype.val hab
      rw [← hv_eq]
      exact Submodule.add_mem_sup haR (Submodule.mem_map.mpr ⟨⟨b, hbK⟩, hbG, rfl⟩)
  have hfrG : Module.finrank (ZMod 2) G = d - 2 * r := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq R G
    rw [hRG_sup, hRG_bot, finrank_bot, add_zero] at hadd
    change r + Module.finrank (ZMod 2) K = d at hrn
    change Module.finrank (ZMod 2) K = r + Module.finrank (ZMod 2) G at hadd
    omega
  let bG := (Module.finBasis (ZMod 2) G).reindex (finCongr hfrG)
  let g : Fin (d - 2 * r) → (Fin d → ZMod 2) := fun l => (bG l).val
  have hg_ker : ∀ l : Fin (d - 2 * r), N.mulVec (g l) = 0 := fun l =>
    (Submodule.map_subtype_le K G_in_K (bG l).property)
  let v : Fin d → (Fin d → ZMod 2) := fun j =>
    if h1 : j.val < r then eR ⟨j.val, h1⟩
    else if h2 : j.val < 2 * r then f ⟨j.val - r, by omega⟩
    else g ⟨j.val - 2 * r, by omega⟩
  have hv_N : ∀ j : Fin d, N.mulVec (v j) =
      if h : r ≤ j.val ∧ j.val < 2 * r then v ⟨j.val - r, by omega⟩ else 0 := by
    intro j
    dsimp only [v]
    by_cases h1 : j.val < r
    · have hn : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
      rw [dif_pos h1, dif_neg hn]
      exact heR_ker ⟨j.val, h1⟩
    · by_cases h2 : j.val < 2 * r
      · have hmid : r ≤ j.val ∧ j.val < 2 * r := ⟨by omega, h2⟩
        rw [dif_neg h1, dif_pos h2, dif_pos hmid, dif_pos (show j.val - r < r by omega)]
        exact hf_spec ⟨j.val - r, by omega⟩
      · have hn : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
        rw [dif_neg h1, dif_neg h2, dif_neg hn]
        exact hg_ker ⟨j.val - 2 * r, by omega⟩
  have hv_lin : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hNc : ∑ j : Fin d, c j • N.mulVec (v j) = 0 := by
      have h1 : N.mulVecLin (∑ j : Fin d, c j • v j) = 0 := by rw [hc, map_zero]
      rw [map_sum] at h1
      simpa only [map_smul, Matrix.mulVecLin_apply] using h1
    have hmid0 : ∀ k : Fin r, c ⟨k.val + r, by omega⟩ = 0 := by
      have hsumR : ∑ k : Fin r, c ⟨k.val + r, by omega⟩ • bR k = 0 := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
        rw [← hNc]
        have hflt : ∑ j : Fin d, c j • N.mulVec (v j) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r),
              c j • v ⟨j.val - r, by omega⟩ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hv_N j]
          split_ifs with h <;> simp
        rw [hflt]
        refine Finset.sum_bij (fun (k : Fin r) _ => (⟨k.val + r, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
        · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
        · intro k1 _ k2 _ heq; apply Fin.ext; have := congrArg Fin.val heq; dsimp only at this; omega
        · intro j hj
          rcases (Finset.mem_filter.mp hj).2 with ⟨h1, h2⟩
          exact ⟨⟨j.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
        · intro k _
          congr 1
          dsimp only [v]
          rw [dif_pos (show k.val + r - r < r by omega)]
          exact congrArg (fun x => (bR x).val) (Fin.ext (by dsimp only; omega))
      have hliR := Fintype.linearIndependent_iff.mp bR.linearIndependent
      exact hliR _ hsumR
    have hRpart : (∑ k : Fin r, c ⟨k.val, by omega⟩ • eR k) ∈ R :=
      Submodule.sum_mem R fun k _ => Submodule.smul_mem R _ (heR_mem k)
    have hGpart : (∑ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ • g l) ∈ G :=
      Submodule.sum_mem G fun l _ => Submodule.smul_mem G _ (bG l).property
    have hsum_RG : (∑ k : Fin r, c ⟨k.val, by omega⟩ • eR k) +
        (∑ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ • g l) = 0 := by
      rw [← hc]
      have hpart : (Finset.univ : Finset (Fin d)) =
          (Finset.univ.filter (fun j : Fin d => j.val < r)) ∪
          (Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r)) ∪
          (Finset.univ.filter (fun j : Fin d => 2 * r ≤ j.val)) := by
        ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]; omega
      have hd1 : Disjoint (Finset.univ.filter (fun j : Fin d => j.val < r))
          (Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r)) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2; omega
      have hd2 : Disjoint ((Finset.univ.filter (fun j : Fin d => j.val < r)) ∪
          (Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r)))
          (Finset.univ.filter (fun j : Fin d => 2 * r ≤ j.val)) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        have a2 := (Finset.mem_filter.mp h2).2
        rcases Finset.mem_union.mp h1 with h1a | h1b
        · have a1 := (Finset.mem_filter.mp h1a).2; omega
        · have a1 := (Finset.mem_filter.mp h1b).2; omega
      conv_rhs => rw [hpart, Finset.sum_union hd2, Finset.sum_union hd1]
      have hmid_zero : ∑ j ∈ Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r), c j • v j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨h1, h2⟩
        have hjeq : j = ⟨(j.val - r) + r, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [hjeq, hmid0 ⟨j.val - r, by omega⟩, zero_smul]
      rw [hmid_zero, add_zero]
      congr 1
      · refine Finset.sum_bij (fun (k : Fin r) _ => (⟨k.val, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
        · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩
        · intro k1 _ k2 _ heq; exact Fin.ext (congrArg (Fin.val : Fin d → ℕ) heq)
        · intro j hj; exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro k _; dsimp only [v]; rw [dif_pos k.isLt]
      · refine Finset.sum_bij (fun (l : Fin (d - 2 * r)) _ => (⟨l.val + 2 * r, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
        · intro l _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · intro l1 _ l2 _ heq; apply Fin.ext; have := congrArg (Fin.val : Fin d → ℕ) heq; dsimp only at this; omega
        · intro j hj; exact ⟨⟨j.val - 2 * r, by have := (Finset.mem_filter.mp hj).2; omega⟩,
            Finset.mem_univ _, Fin.ext (by dsimp only; have := (Finset.mem_filter.mp hj).2; omega)⟩
        · intro l _
          dsimp only [v]
          rw [dif_neg (by omega), dif_neg (by omega)]
          congr 2; apply Fin.ext; dsimp only; omega
    have hR0 : ∑ k : Fin r, c ⟨k.val, by omega⟩ • eR k = 0 := by
      have hmem : (∑ k : Fin r, c ⟨k.val, by omega⟩ • eR k) ∈ R ⊓ G := by
        refine ⟨hRpart, ?_⟩
        have heq : ∑ k : Fin r, c ⟨k.val, by omega⟩ • eR k =
            -(∑ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ • g l) := eq_neg_of_add_eq_zero_left hsum_RG
        rw [heq]; exact G.neg_mem hGpart
      rwa [hRG_bot, Submodule.mem_bot] at hmem
    have hG0 : ∑ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ • g l = 0 := by
      rw [hR0, zero_add] at hsum_RG; exact hsum_RG
    have htop0 : ∀ k : Fin r, c ⟨k.val, by omega⟩ = 0 := by
      have hsumR : ∑ k : Fin r, c ⟨k.val, by omega⟩ • bR k = 0 := by
        apply Subtype.ext
        simpa only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] using hR0
      exact Fintype.linearIndependent_iff.mp bR.linearIndependent _ hsumR
    have hbot0 : ∀ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ = 0 := by
      have hsumG : ∑ l : Fin (d - 2 * r), c ⟨l.val + 2 * r, by omega⟩ • bG l = 0 := by
        apply Subtype.ext
        simpa only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] using hG0
      exact Fintype.linearIndependent_iff.mp bG.linearIndependent _ hsumG
    intro j
    by_cases h1 : j.val < r
    · exact htop0 ⟨j.val, h1⟩
    · by_cases h2 : j.val < 2 * r
      · have hjeq : j = ⟨(j.val - r) + r, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [hjeq]; exact hmid0 ⟨j.val - r, by omega⟩
      · have hjeq : j = ⟨(j.val - 2 * r) + 2 * r, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [hjeq]; exact hbot0 ⟨j.val - 2 * r, by omega⟩
  let bv : Module.Basis (Fin d) (ZMod 2) (Fin d → ZMod 2) :=
    basisOfLinearIndependentOfCardEqFinrank hv_lin (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  let Pinv : Matrix (Fin d) (Fin d) (ZMod 2) := fun i j => v j i
  let P : Matrix (Fin d) (Fin d) (ZMod 2) := fun i j => bv.repr (Pi.single j 1) i
  have hPinv_mul : ∀ x : Fin d → ZMod 2, Pinv.mulVec x = ∑ j : Fin d, x j • v j := by
    intro x; funext i
    simp only [Matrix.mulVec, dotProduct, Pinv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hP_mul : ∀ w : Fin d → ZMod 2, P.mulVec w = bv.repr w := by
    intro w
    have hw : w = ∑ j : Fin d, w j • Pi.single j (1 : ZMod 2) := by
      funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro h; exact absurd (Finset.mem_univ i) h
    funext i
    conv_rhs => rw [hw, map_sum]
    rw [finsupp_sum_apply]
    simp only [Matrix.mulVec, dotProduct, P, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hbv_apply : ∀ j : Fin d, bv j = v j := fun j =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hv_lin _) j
  have hPPinv : P * Pinv = 1 := by
    ext i j
    have hcol : (P * Pinv).mulVec (Pi.single j 1) = Pi.single j 1 := by
      rw [← Matrix.mulVec_mulVec, hPinv_mul, hP_mul]
      have h1 : ∑ k : Fin d, ((Pi.single j (1 : ZMod 2) : Fin d → ZMod 2) k) • v k = bv j := by
        rw [Finset.sum_eq_single j]
        · simp [hbv_apply]
        · intro k _ hne; simp [Pi.single_eq_of_ne hne]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [h1, bv.repr_self]
      funext k
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    have hi := congrFun hcol i
    rw [mulVec_single_one] at hi
    simpa only [Pi.single_apply, Matrix.one_apply] using hi
  have hPinvP : Pinv * P = 1 := by
    ext i j
    have hcol : (Pinv * P).mulVec (Pi.single j 1) = Pi.single j 1 := by
      rw [← Matrix.mulVec_mulVec, hP_mul, hPinv_mul]
      have h1 : ∑ k : Fin d, (bv.repr (Pi.single j 1) k) • v k = ∑ k : Fin d, (bv.repr (Pi.single j 1) k) • bv k := by
        refine Finset.sum_congr rfl fun k _ => by rw [hbv_apply]
      rw [h1, bv.sum_repr]
    have hi := congrFun hcol i
    rw [mulVec_single_one] at hi
    simpa only [Pi.single_apply, Matrix.one_apply] using hi
  have hPN : P * N * Pinv = canonN d r := by
    ext i j
    have hcol : (P * N * Pinv).mulVec (Pi.single j 1) = (canonN d r).mulVec (Pi.single j 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinv_mul]
      have h1 : ∑ k : Fin d, ((Pi.single j (1 : ZMod 2) : Fin d → ZMod 2) k) • v k = v j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hne; simp [Pi.single_eq_of_ne hne]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [h1, hv_N j, hP_mul]
      funext k
      rw [mulVec_single_one]
      dsimp only [canonN]
      by_cases hmid : r ≤ j.val ∧ j.val < 2 * r
      · rw [dif_pos hmid, ← hbv_apply ⟨j.val - r, by omega⟩, bv.repr_self]
        simp only [Finsupp.single_apply]
        by_cases hkj : k = ⟨j.val - r, by omega⟩
        · subst hkj; rw [if_pos rfl, if_pos ⟨by dsimp only; omega, by dsimp only; omega⟩]
        · have hne : ¬ (k.val < r ∧ j.val = k.val + r) := by
            rintro ⟨hk1, hk2⟩; apply hkj; apply Fin.ext; dsimp only; omega
          rw [if_neg (Ne.symm hkj), if_neg hne]
      · rw [dif_neg hmid, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        have hne : ¬ (k.val < r ∧ j.val = k.val + r) := by rintro ⟨hk1, hk2⟩; omega
        rw [if_neg hne]
    have hi := congrFun hcol i
    rwa [mulVec_single_one, mulVec_single_one] at hi
  refine ⟨P, Pinv, hPPinv, hPinvP, ?_⟩
  have hU_eq : U = 1 + N := by
    ext i j; simp only [N, Matrix.add_apply, Matrix.sub_apply]
    have h := zmod2_add_self ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j)
    rw [zmod2_sub_eq_add]
    calc U i j = ((1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) + U i j := by rw [h, zero_add]
      _ = (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j + (U i j + (1 : Matrix (Fin d) (Fin d) (ZMod 2)) i j) := by ring
  conv_lhs => rw [hU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPPinv, hPN]
  rfl

private def canonWSub (d r : ℕ) (h2r : 2 * r ≤ d) :
    Submodule (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)) :=
  { carrier := { X | (X.transpose = X ∧ ∀ i, X i i = 0) ∧
      (∀ i j : Fin d, r ≤ i.val → r ≤ j.val → X i j = 0) ∧
      (∀ a b : Fin r, X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ = X ⟨b.val, by omega⟩ ⟨a.val + r, by omega⟩) ∧
      (∀ a : Fin r, X ⟨a.val, by omega⟩ ⟨a.val + r, by omega⟩ = 0) },
    zero_mem' := ⟨⟨Matrix.transpose_zero, fun _ => rfl⟩, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩, add_mem' := fun {X Y} hX hY =>
      ⟨⟨by rw [Matrix.transpose_add, hX.1.1, hY.1.1], fun i => by simp [hX.1.2 i, hY.1.2 i]⟩,
       fun i j hi hj => by simp [hX.2.1 i j hi hj, hY.2.1 i j hi hj],
       fun a b => by simp [hX.2.2.1 a b, hY.2.2.1 a b],
       fun a => by simp [hX.2.2.2 a, hY.2.2.2 a]⟩,
    smul_mem' := fun c X hX =>
      ⟨⟨by rw [Matrix.transpose_smul, hX.1.1], fun i => by simp [hX.1.2 i]⟩,
       fun i j hi hj => by simp [hX.2.1 i j hi hj],
       fun a b => by simp [hX.2.2.1 a b],
       fun a => by simp [hX.2.2.2 a]⟩ }

private lemma canonN_mul_apply {d r : ℕ} (h2r : 2 * r ≤ d)
    (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    (canonN d r * H) i j = if hi : i.val < r then H ⟨i.val + r, by omega⟩ j else 0 := by
  simp only [Matrix.mul_apply, canonN]
  by_cases hi : i.val < r
  · rw [dif_pos hi, Finset.sum_eq_single (⟨i.val + r, by omega⟩ : Fin d)]
    · simp [hi]
    · intro k _ hne
      have hcond : ¬ (i.val < r ∧ k.val = i.val + r) := by
        rintro ⟨_, hk⟩; apply hne; exact Fin.ext hk
      simp [hcond]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hi]
    refine Finset.sum_eq_zero fun k _ => by simp [hi]

private lemma mul_canonN_transpose_apply {d r : ℕ} (h2r : 2 * r ≤ d)
    (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    (H * (canonN d r).transpose) i j = if hj : j.val < r then H i ⟨j.val + r, by omega⟩ else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, canonN]
  by_cases hj : j.val < r
  · rw [dif_pos hj, Finset.sum_eq_single (⟨j.val + r, by omega⟩ : Fin d)]
    · simp [hj]
    · intro k _ hne
      have hcond : ¬ (j.val < r ∧ k.val = j.val + r) := by
        rintro ⟨_, hk⟩; apply hne; exact Fin.ext hk
      simp [hcond]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hj]
    refine Finset.sum_eq_zero fun k _ => by simp [hj]

private lemma canonU_action {d r : ℕ} (h2r : 2 * r ≤ d) (H : Matrix (Fin d) (Fin d) (ZMod 2))
    (i j : Fin d) :
    (canonU d r * H * (canonU d r).transpose + H) i j =
      (if hi : i.val < r then H ⟨i.val + r, by omega⟩ j else 0) +
      (if hj : j.val < r then H i ⟨j.val + r, by omega⟩ else 0) +
      (if hi : i.val < r then if hj : j.val < r then H ⟨i.val + r, by omega⟩ ⟨j.val + r, by omega⟩ else 0 else 0) := by
  have h1 : canonU d r * H * (canonU d r).transpose + H =
      canonN d r * H + H * (canonN d r).transpose + canonN d r * H * (canonN d r).transpose := by
    dsimp only [canonU]
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    ext a b
    simp only [Matrix.add_apply]
    have z := zmod2_add_self (H a b)
    calc H a b + (canonN d r * H) a b + ((H * (canonN d r).transpose) a b + (canonN d r * H * (canonN d r).transpose) a b) + H a b
        = (H a b + H a b) + ((canonN d r * H) a b + (H * (canonN d r).transpose) a b + (canonN d r * H * (canonN d r).transpose) a b) := by ring
      _ = (canonN d r * H) a b + (H * (canonN d r).transpose) a b + (canonN d r * H * (canonN d r).transpose) a b := by rw [z, zero_add]
  rw [h1]
  simp only [Matrix.add_apply, canonN_mul_apply h2r, mul_canonN_transpose_apply h2r]
  congr 1
  by_cases hi : i.val < r <;> by_cases hj : j.val < r <;> simp [hi, hj]

private lemma canonW_eq_sub {d r : ℕ} (h2r : 2 * r ≤ d) :
    Submodule.span (ZMod 2)
      {X : Matrix (Fin d) (Fin d) (ZMod 2) |
        ∃ H : Matrix (Fin d) (Fin d) (ZMod 2), (H.transpose = H ∧ ∀ i, H i i = 0) ∧
          X = canonU d r * H * (canonU d r).transpose + H} = canonWSub d r h2r := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro X ⟨H, hH, rfl⟩
    have hHsym : ∀ a b : Fin d, H b a = H a b := fun a b => congrFun (congrFun hH.1 a) b
    have haltX : (canonU d r * H * (canonU d r).transpose + H).transpose =
        canonU d r * H * (canonU d r).transpose + H ∧
        ∀ i, (canonU d r * H * (canonU d r).transpose + H) i i = 0 := by
      have h1 := alt_congr (canonU d r) H hH
      refine ⟨by rw [Matrix.transpose_add, h1.1, hH.1], fun i => by simp [h1.2 i, hH.2 i]⟩
    refine ⟨haltX, ?_, ?_, ?_⟩
    · intro i j hi hj
      rw [canonU_action h2r H i j, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]; simp
    · intro a b
      rw [canonU_action h2r H ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩,
        canonU_action h2r H ⟨b.val, by omega⟩ ⟨a.val + r, by omega⟩]
      rw [dif_pos a.isLt, dif_neg (by dsimp only; omega), dif_pos a.isLt, dif_neg (by dsimp only; omega)]
      rw [dif_pos b.isLt, dif_neg (by dsimp only; omega), dif_pos b.isLt, dif_neg (by dsimp only; omega)]
      simp only [add_zero]
      exact hHsym ⟨b.val + r, by omega⟩ ⟨a.val + r, by omega⟩
    · intro a
      rw [canonU_action h2r H ⟨a.val, by omega⟩ ⟨a.val + r, by omega⟩]
      rw [dif_pos a.isLt, dif_neg (by dsimp only; omega), dif_pos a.isLt, dif_neg (by dsimp only; omega)]
      simp only [add_zero]
      exact hH.2 ⟨a.val + r, by omega⟩
  · intro X hX
    apply Submodule.subset_span
    have hXsym : ∀ a b : Fin d, X b a = X a b := fun a b => congrFun (congrFun hX.1.1 a) b
    let H : Matrix (Fin d) (Fin d) (ZMod 2) := fun a b =>
      if ha1 : r ≤ a.val ∧ a.val < 2 * r then
        if hb1 : r ≤ b.val ∧ b.val < 2 * r then X ⟨a.val - r, by omega⟩ b
        else if hb0 : b.val < r then
          if b.val < a.val - r then X b ⟨a.val - r, by omega⟩ + X b a else 0
        else X ⟨a.val - r, by omega⟩ b
      else if hb1 : r ≤ b.val ∧ b.val < 2 * r then
        if ha0 : a.val < r then
          if a.val < b.val - r then X a ⟨b.val - r, by omega⟩ + X a b else 0
        else X ⟨b.val - r, by omega⟩ a
      else 0
    have hH_alt : H.transpose = H ∧ ∀ a, H a a = 0 := by
      refine ⟨?_, ?_⟩
      · ext a b
        change H b a = H a b
        dsimp only [H]
        by_cases ha1 : r ≤ a.val ∧ a.val < 2 * r
        · by_cases hb1 : r ≤ b.val ∧ b.val < 2 * r
          · rw [dif_pos hb1, dif_pos ha1, dif_pos ha1, dif_pos hb1]
            have h1 := hX.2.2.1 ⟨b.val - r, by omega⟩ ⟨a.val - r, by omega⟩
            have ha_eq : (⟨(a.val - r) + r, by omega⟩ : Fin d) = a := Fin.ext (by dsimp only; omega)
            have hb_eq : (⟨(b.val - r) + r, by omega⟩ : Fin d) = b := Fin.ext (by dsimp only; omega)
            rw [ha_eq, hb_eq] at h1
            exact h1
          · rw [dif_neg hb1, dif_pos ha1, dif_pos ha1, dif_neg hb1]
        · by_cases hb1 : r ≤ b.val ∧ b.val < 2 * r
          · rw [dif_pos hb1, dif_neg ha1, dif_neg ha1, dif_pos hb1]
          · rw [dif_neg hb1, dif_neg ha1, dif_neg ha1, dif_neg hb1]
      · intro a
        dsimp only [H]
        by_cases ha1 : r ≤ a.val ∧ a.val < 2 * r
        · rw [dif_pos ha1, dif_pos ha1]
          have h0 := hX.2.2.2 ⟨a.val - r, by omega⟩
          have ha_eq : (⟨(a.val - r) + r, by omega⟩ : Fin d) = a := Fin.ext (by dsimp only; omega)
          rwa [ha_eq] at h0
        · rw [dif_neg ha1, dif_neg ha1]
    refine ⟨H, hH_alt, ?_⟩
    ext i j
    rw [canonU_action h2r H i j]
    by_cases hi : i.val < r
    · by_cases hj : j.val < r
      · rw [dif_pos hi, dif_pos hj, dif_pos hi, dif_pos hj]
        have hmid_i : r ≤ (⟨i.val + r, by omega⟩ : Fin d).val ∧ (⟨i.val + r, by omega⟩ : Fin d).val < 2 * r := ⟨by dsimp only; omega, by dsimp only; omega⟩
        have hmid_j : r ≤ (⟨j.val + r, by omega⟩ : Fin d).val ∧ (⟨j.val + r, by omega⟩ : Fin d).val < 2 * r := ⟨by dsimp only; omega, by dsimp only; omega⟩
        have hnot_i : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
        have hnot_j : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
        have h1 : H ⟨i.val + r, by omega⟩ j = if j.val < i.val then X j i + X j ⟨i.val + r, by omega⟩ else 0 := by
          dsimp only [H]; rw [dif_pos hmid_i, dif_neg hnot_j, dif_pos hj]
          have : i.val + r - r = i.val := by omega
          simp only [this, Fin.eta]
        have h2 : H i ⟨j.val + r, by omega⟩ = if i.val < j.val then X i j + X i ⟨j.val + r, by omega⟩ else 0 := by
          dsimp only [H]; rw [dif_neg hnot_i, dif_pos hmid_j, dif_pos hi]
          have : j.val + r - r = j.val := by omega
          simp only [this, Fin.eta]
        have h3 : H ⟨i.val + r, by omega⟩ ⟨j.val + r, by omega⟩ = X i ⟨j.val + r, by omega⟩ := by
          dsimp only [H]; rw [dif_pos hmid_i, dif_pos hmid_j]
          congr 1; apply Fin.ext; dsimp only; omega
        rw [h1, h2, h3]
        rcases lt_trichotomy i.val j.val with hlt | heq | hgt
        · rw [if_neg (not_lt.mpr (le_of_lt hlt)), if_pos hlt, zero_add, add_assoc, zmod2_add_self, add_zero]
        · have hij : i = j := Fin.ext heq
          subst hij
          rw [if_neg (lt_irrefl _), add_zero, zero_add, hX.1.2 i]
          exact (hX.2.2.2 ⟨i.val, hi⟩).symm
        · rw [if_pos hgt, if_neg (not_lt.mpr (le_of_lt hgt)), add_zero, hXsym i j]
          have hd_sym := hX.2.2.1 ⟨j.val, hj⟩ ⟨i.val, hi⟩
          dsimp only at hd_sym
          have hj_eq : (⟨j.val, by omega⟩ : Fin d) = j := Fin.ext rfl
          have hi_eq : (⟨i.val, by omega⟩ : Fin d) = i := Fin.ext rfl
          rw [hj_eq, hi_eq] at hd_sym
          rw [hd_sym, add_assoc, zmod2_add_self, add_zero]
      · rw [dif_pos hi, dif_neg hj, dif_pos hi, dif_neg hj, add_zero, add_zero]
        have hmid_i : r ≤ (⟨i.val + r, by omega⟩ : Fin d).val ∧ (⟨i.val + r, by omega⟩ : Fin d).val < 2 * r := ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only [H]
        rw [dif_pos hmid_i]
        by_cases hj1 : r ≤ j.val ∧ j.val < 2 * r
        · rw [dif_pos hj1]; congr 1; apply Fin.ext; dsimp only; omega
        · rw [dif_neg hj1, dif_neg hj]; congr 1; apply Fin.ext; dsimp only; omega
    · by_cases hj : j.val < r
      · rw [dif_neg hi, dif_pos hj, dif_neg hi, zero_add, add_zero]
        have hmid_j : r ≤ (⟨j.val + r, by omega⟩ : Fin d).val ∧ (⟨j.val + r, by omega⟩ : Fin d).val < 2 * r := ⟨by dsimp only; omega, by dsimp only; omega⟩
        dsimp only [H]
        by_cases hi1 : r ≤ i.val ∧ i.val < 2 * r
        · rw [dif_pos hi1, dif_pos hmid_j]
          have h1 := hX.2.2.1 ⟨i.val - r, by omega⟩ ⟨j.val, hj⟩
          have hi_eq : (⟨(i.val - r) + r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp only; omega)
          have hj_eq : (⟨j.val, by omega⟩ : Fin d) = j := Fin.ext rfl
          rw [hi_eq, hj_eq] at h1
          rw [hXsym j i, ← h1]
        · rw [dif_neg hi1, dif_pos hmid_j, dif_neg hi]
          have hj_eq : (⟨j.val + r - r, by omega⟩ : Fin d) = j := Fin.ext (by dsimp only; omega)
          rw [hj_eq, hXsym j i]
      · rw [dif_neg hi, dif_neg hj, dif_neg hi, add_zero, add_zero]
        exact hX.2.1 i j (by omega) (by omega)

private lemma finrank_canonWSub {d r : ℕ} (h2r : 2 * r ≤ d) :
    Module.finrank (ZMod 2) (canonWSub d r h2r) = r * (d - r - 1) := by
  let P2 := {p : Fin r × Fin r // p.1.val < p.2.val}
  let T := (P2 → ZMod 2) × (P2 → ZMod 2) × (Fin r × Fin (d - 2 * r) → ZMod 2)
  let proj : canonWSub d r h2r →ₗ[ZMod 2] T :=
    { toFun := fun X =>
        (fun p => X.val ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val, by omega⟩,
         fun p => X.val ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val + r, by omega⟩,
         fun q => X.val ⟨q.1.val, by omega⟩ ⟨q.2.val + 2 * r, by omega⟩),
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
  have hbij : Function.Bijective proj := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro X hX0
      have h1 : ∀ p : P2, X.val ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val, by omega⟩ = 0 :=
        fun p => congrFun (congrArg Prod.fst hX0) p
      have h2 : ∀ p : P2, X.val ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val + r, by omega⟩ = 0 :=
        fun p => congrFun (congrArg (fun t => t.2.1) hX0) p
      have h3 : ∀ q : Fin r × Fin (d - 2 * r), X.val ⟨q.1.val, by omega⟩ ⟨q.2.val + 2 * r, by omega⟩ = 0 :=
        fun q => congrFun (congrArg (fun t => t.2.2) hX0) q
      have hXsym : ∀ a b : Fin d, X.val b a = X.val a b := fun a b => congrFun (congrFun X.property.1.1 a) b
      apply Subtype.ext; ext i j
      by_cases hi : i.val < r
      · by_cases hj : j.val < r
        · rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact h1 ⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hlt⟩
          · have hij : i = j := Fin.ext heq; subst hij; exact X.property.1.2 i
          · rw [hXsym j i]; exact h1 ⟨(⟨j.val, hj⟩, ⟨i.val, hi⟩), hgt⟩
        · by_cases hj1 : j.val < 2 * r
          · have hjeq : j = ⟨(j.val - r) + r, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hjeq]
            rcases lt_trichotomy i.val (j.val - r) with hlt | heq | hgt
            · exact h2 ⟨(⟨i.val, hi⟩, ⟨j.val - r, by omega⟩), hlt⟩
            · have h0 := X.property.2.2.2 ⟨i.val, hi⟩
              have hxeq : X.val i ⟨(j.val - r) + r, by omega⟩ = X.val ⟨i.val, by omega⟩ ⟨i.val + r, by omega⟩ :=
                congrArg₂ X.val (Fin.ext rfl) (Fin.ext (by dsimp only; omega))
              rw [hxeq]; exact h0
            · rw [X.property.2.2.1 ⟨i.val, hi⟩ ⟨j.val - r, by omega⟩]
              exact h2 ⟨(⟨j.val - r, by omega⟩, ⟨i.val, hi⟩), hgt⟩
          · have hjeq : j = ⟨(j.val - 2 * r) + 2 * r, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hjeq]; exact h3 (⟨i.val, hi⟩, ⟨j.val - 2 * r, by omega⟩)
      · by_cases hj : j.val < r
        · rw [hXsym j i]
          by_cases hi1 : i.val < 2 * r
          · have hieq : i = ⟨(i.val - r) + r, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hieq]
            rcases lt_trichotomy j.val (i.val - r) with hlt | heq | hgt
            · exact h2 ⟨(⟨j.val, hj⟩, ⟨i.val - r, by omega⟩), hlt⟩
            · have h0 := X.property.2.2.2 ⟨j.val, hj⟩
              have hxeq : X.val j ⟨(i.val - r) + r, by omega⟩ = X.val ⟨j.val, by omega⟩ ⟨j.val + r, by omega⟩ :=
                congrArg₂ X.val (Fin.ext rfl) (Fin.ext (by dsimp only; omega))
              rw [hxeq]; exact h0
            · rw [X.property.2.2.1 ⟨j.val, hj⟩ ⟨i.val - r, by omega⟩]
              exact h2 ⟨(⟨i.val - r, by omega⟩, ⟨j.val, hj⟩), hgt⟩
          · have hieq : i = ⟨(i.val - 2 * r) + 2 * r, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hieq]; exact h3 (⟨j.val, hj⟩, ⟨i.val - 2 * r, by omega⟩)
        · exact X.property.2.1 i j (by omega) (by omega)
    · rintro ⟨f1, f2, f3⟩
      let X : Matrix (Fin d) (Fin d) (ZMod 2) := fun i j =>
        if hi : i.val < r then
          if hj : j.val < r then
            if hlt : i.val < j.val then f1 ⟨(⟨i.val, hi⟩, ⟨j.val, hj⟩), hlt⟩
            else if hgt : j.val < i.val then f1 ⟨(⟨j.val, hj⟩, ⟨i.val, hi⟩), hgt⟩
            else 0
          else if hj1 : j.val < 2 * r then
            if hlt : i.val < j.val - r then f2 ⟨(⟨i.val, hi⟩, ⟨j.val - r, by omega⟩), hlt⟩
            else if hgt : j.val - r < i.val then f2 ⟨(⟨j.val - r, by omega⟩, ⟨i.val, hi⟩), hgt⟩
            else 0
          else f3 (⟨i.val, hi⟩, ⟨j.val - 2 * r, by omega⟩)
        else if hj : j.val < r then
          if hi1 : i.val < 2 * r then
            if hlt : j.val < i.val - r then f2 ⟨(⟨j.val, hj⟩, ⟨i.val - r, by omega⟩), hlt⟩
            else if hgt : i.val - r < j.val then f2 ⟨(⟨i.val - r, by omega⟩, ⟨j.val, hj⟩), hgt⟩
            else 0
          else f3 (⟨j.val, hj⟩, ⟨i.val - 2 * r, by omega⟩)
        else 0
      have hXmem : X ∈ canonWSub d r h2r := by
        refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
        · ext i j
          change X j i = X i j
          dsimp only [X]
          by_cases hi : i.val < r
          · by_cases hj : j.val < r
            · rw [dif_pos hj, dif_pos hi, dif_pos hi, dif_pos hj]
              rcases lt_trichotomy i.val j.val with hlt | heq | hgt
              · rw [dif_neg (not_lt.mpr (le_of_lt hlt)), dif_pos hlt, dif_pos hlt]
              · have hij : i = j := Fin.ext heq; subst hij; rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
              · rw [dif_pos hgt, dif_neg (not_lt.mpr (le_of_lt hgt)), dif_pos hgt]
            · rw [dif_neg hj, dif_pos hi, dif_pos hi, dif_neg hj]
          · by_cases hj : j.val < r
            · rw [dif_pos hj, dif_neg hi, dif_neg hi, dif_pos hj]
            · rw [dif_neg hj, dif_neg hi, dif_neg hi, dif_neg hj]
        · intro i; dsimp only [X]
          by_cases hi : i.val < r
          · rw [dif_pos hi, dif_pos hi, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
          · rw [dif_neg hi, dif_neg hi]
        · intro i j hi hj; dsimp only [X]; rw [dif_neg (by omega), dif_neg (by omega)]
        · intro a b; dsimp only [X]
          rw [dif_pos a.isLt, dif_neg (show ¬ (b.val + r < r) by omega), dif_pos (show b.val + r < 2 * r by omega),
            dif_pos b.isLt, dif_neg (show ¬ (a.val + r < r) by omega), dif_pos (show a.val + r < 2 * r by omega)]
          have ha_sub : a.val + r - r = a.val := by omega
          have hb_sub : b.val + r - r = b.val := by omega
          simp only [ha_sub, hb_sub]
          rcases lt_trichotomy a.val b.val with hlt | heq | hgt
          · rw [dif_pos hlt, dif_neg (not_lt.mpr (le_of_lt hlt)), dif_pos hlt]
          · have hab : a = b := Fin.ext heq; subst hab; rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
          · rw [dif_neg (not_lt.mpr (le_of_lt hgt)), dif_pos hgt, dif_pos hgt]
        · intro a; dsimp only [X]
          rw [dif_pos a.isLt, dif_neg (show ¬ (a.val + r < r) by omega), dif_pos (show a.val + r < 2 * r by omega)]
          have ha_sub : a.val + r - r = a.val := by omega
          simp only [ha_sub, lt_irrefl, ↓reduceDIte]
      refine ⟨⟨X, hXmem⟩, ?_⟩
      apply Prod.ext
      · funext p; change X ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val, by omega⟩ = f1 p; dsimp only [X]
        rw [dif_pos p.val.1.isLt, dif_pos p.val.2.isLt, dif_pos p.property]
      · apply Prod.ext
        · funext p; change X ⟨p.val.1.val, by omega⟩ ⟨p.val.2.val + r, by omega⟩ = f2 p; dsimp only [X]
          rw [dif_pos p.val.1.isLt, dif_neg (show ¬ (p.val.2.val + r < r) by omega), dif_pos (show p.val.2.val + r < 2 * r by omega)]
          have hlt : p.val.1.val < p.val.2.val + r - r := by omega
          rw [dif_pos hlt]
          congr 1; apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
        · funext q; change X ⟨q.1.val, by omega⟩ ⟨q.2.val + 2 * r, by omega⟩ = f3 q; dsimp only [X]
          rw [dif_pos q.1.isLt, dif_neg (show ¬ (q.2.val + 2 * r < r) by omega), dif_neg (show ¬ (q.2.val + 2 * r < 2 * r) by omega)]
          congr 1; apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  have heq := (LinearEquiv.ofBijective proj hbij).finrank_eq
  rw [heq]
  have hT : Module.finrank (ZMod 2) T = Fintype.card P2 + Fintype.card P2 + r * (d - 2 * r) := by
    dsimp only [T]
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    omega
  have hP2 : 2 * Fintype.card P2 = r * (r - 1) := by
    have hcard : Fintype.card P2 = (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val < p.2.val)).card := by
      rw [Fintype.card_subtype]
    have hlt_eq_gt : (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val < p.2.val)).card =
        (Finset.univ.filter (fun p : Fin r × Fin r => p.2.val < p.1.val)).card := by
      refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
      · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
      · intro p1 _ p2 _ h; exact Prod.swap_injective h
      · intro p hp; exact ⟨p.swap, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, Prod.swap_swap p⟩
    have hdiag : (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val = p.2.val)).card = r := by
      have : (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val = p.2.val)).card = (Finset.univ : Finset (Fin r)).card := by
        refine (Finset.card_bij (fun (i : Fin r) _ => (i, i)) ?_ ?_ ?_).symm
        · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        · intro i1 _ i2 _ h; exact congrArg Prod.fst h
        · intro p hp; exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl (Fin.ext (Finset.mem_filter.mp hp).2)⟩
      rw [this, Finset.card_univ, Fintype.card_fin]
    have hpart : (Finset.univ : Finset (Fin r × Fin r)) =
        (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val < p.2.val)) ∪
        (Finset.univ.filter (fun p : Fin r × Fin r => p.2.val < p.1.val)) ∪
        (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val = p.2.val)) := by
      ext p; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]; omega
    have hd1 : Disjoint (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val < p.2.val))
        (Finset.univ.filter (fun p : Fin r × Fin r => p.2.val < p.1.val)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2; omega
    have hd2 : Disjoint ((Finset.univ.filter (fun p : Fin r × Fin r => p.1.val < p.2.val)) ∪
        (Finset.univ.filter (fun p : Fin r × Fin r => p.2.val < p.1.val)))
        (Finset.univ.filter (fun p : Fin r × Fin r => p.1.val = p.2.val)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have a2 := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1a | h1b
      · have a1 := (Finset.mem_filter.mp h1a).2; omega
      · have a1 := (Finset.mem_filter.mp h1b).2; omega
    have htot := congrArg Finset.card hpart
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, ← hlt_eq_gt, hdiag, ← hcard] at htot
    rcases r with _ | r'
    · simp at htot ⊢
    · have h1 : (r' + 1) * (r' + 1 - 1) = (r' + 1) * r' := by congr 1
      have h2 : (r' + 1) * r' + (r' + 1) = (r' + 1) * (r' + 1) := by ring
      rw [h1]; omega
  rw [hT]
  rcases r with _ | r'
  · simp at hP2 ⊢
  · have h1 : (r' + 1) * r' + (r' + 1) * (d - 2 * (r' + 1)) = (r' + 1) * (d - (r' + 1) - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h2 : (r' + 1) * (r' + 1 - 1) = (r' + 1) * r' := by congr 1
    omega

private lemma rank_le_two_of_two_rows {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2))
    (i1 i2 : Fin d) (hzero : ∀ i j, i ≠ i1 → i ≠ i2 → M i j = 0) : M.rank ≤ 2 := by
  have hle2 : LinearMap.range M.mulVecLin ≤
      Submodule.span (ZMod 2) (({Pi.single i1 1, Pi.single i2 1} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    by_cases h12 : i1 = i2
    · have hx : M.mulVec x = (M.mulVec x i1) • Pi.single i1 1 := by
        funext i
        by_cases h1 : i = i1
        · subst h1; simp
        · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, h1, ↓reduceIte, mul_zero,
            Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_zero fun j _ => by rw [hzero i j h1 (h12 ▸ h1), zero_mul]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · have hx : M.mulVec x = (M.mulVec x i1) • Pi.single i1 1 + (M.mulVec x i2) • Pi.single i2 1 := by
        funext i
        by_cases h1 : i = i1
        · subst h1; simp [Pi.single_apply, h12]
        · by_cases h2 : i = i2
          · subst h2; simp [Pi.single_apply, h1]
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h1, h2, ↓reduceIte,
              mul_zero, add_zero, Matrix.mulVec, dotProduct]
            exact Finset.sum_eq_zero fun j _ => by rw [hzero i j h1 h2, zero_mul]
      rw [hx]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  calc M.rank ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (({Pi.single i1 1, Pi.single i2 1} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2))) :=
        Submodule.finrank_mono hle2
    _ ≤ ({Pi.single i1 1, Pi.single i2 1} : Finset (Fin d → ZMod 2)).card := finrank_span_finset_le_card _
    _ ≤ 2 := Finset.card_le_two

private lemma rank_le_one_of_single {d : ℕ} (i0 j0 : Fin d) :
    (Matrix.single i0 j0 (1 : ZMod 2)).rank ≤ 1 := by
  have hle : LinearMap.range (Matrix.single i0 j0 (1 : ZMod 2)).mulVecLin ≤
      Submodule.span (ZMod 2) (({Pi.single i0 1} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    have hx : (Matrix.single i0 j0 (1 : ZMod 2)).mulVec x = x j0 • Pi.single i0 1 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, msingle_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hi : i = i0
      · subst hi
        rw [Finset.sum_eq_single j0]
        · simp
        · intro j _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ j0) h
      · rw [if_neg hi, mul_zero]
        refine Finset.sum_eq_zero fun j _ => by simp [hi]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  calc (Matrix.single i0 j0 (1 : ZMod 2)).rank
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({Pi.single i0 1} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ ({Pi.single i0 1} : Finset (Fin d → ZMod 2)).card := finrank_span_finset_le_card _
    _ = 1 := Finset.card_singleton _

private lemma rank_le_one_of_col_vec {d : ℕ} (v : Fin d → ZMod 2) (j0 : Fin d) :
    (Matrix.of fun i j => if j = j0 then v i else 0).rank ≤ 1 := by
  have hle : LinearMap.range (Matrix.of fun i j => if j = j0 then v i else 0).mulVecLin ≤
      Submodule.span (ZMod 2) (({v} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    have hx : (Matrix.of fun i j => if j = j0 then v i else 0).mulVec x = x j0 • v := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j0]
      · simp [mul_comm]
      · intro j _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ j0) h
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  calc (Matrix.of fun i j => if j = j0 then v i else 0).rank
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({v} : Finset (Fin d → ZMod 2)) : Set (Fin d → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ ({v} : Finset (Fin d → ZMod 2)).card := finrank_span_finset_le_card _
    _ = 1 := Finset.card_singleton _

private lemma canon_fits_upper {d r : ℕ} (h2r : 2 * r ≤ d) :
    let W := canonWSub d r h2r
    let free := fun E : Submodule (ZMod 2) (Fin d → ZMod 2) =>
      Submodule.span (ZMod 2) {X : Matrix (Fin d) (Fin d) (ZMod 2) | ∀ j, (fun i => X i j) ∈ E}
    ∃ E : Submodule (ZMod 2) (Fin d → ZMod 2),
      Module.finrank (ZMod 2) E ≤ (if r ≤ 1 then 0 else r) ∧
      W ⊔ free E = Submodule.span (ZMod 2) {X | X ∈ W ⊔ free E ∧ X.rank ≤ 2} := by
  intro W free
  by_cases hr1 : r ≤ 1
  · refine ⟨⊥, by simp [hr1], ?_⟩
    apply le_antisymm
    · have hfree_bot : free ⊥ = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro X hX
        refine Submodule.span_induction (fun Y hY => ?_) rfl (fun _ _ _ _ ha hb => by simp [ha, hb])
          (fun c _ _ ha => by simp [ha]) hX
        ext i j; exact congrFun (hY j) i
      rw [hfree_bot, sup_bot_eq]
      intro X hX
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with rfl | rfl
      · have hX0 : X = 0 := by ext i j; exact hX.2.1 i j (Nat.zero_le _) (Nat.zero_le _)
        rw [hX0]; exact Submodule.zero_mem _
      · have h0 : 0 < d := by omega
        have hdecomp : X = ∑ k ∈ Finset.univ.filter (fun k : Fin d => 2 ≤ k.val),
            X ⟨0, h0⟩ k • (Matrix.single ⟨0, h0⟩ k (1 : ZMod 2) + Matrix.single k ⟨0, h0⟩ (1 : ZMod 2)) := by
          ext i j
          simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, msingle_apply, smul_eq_mul]
          by_cases hi0 : i.val = 0
          · have hi : i = ⟨0, h0⟩ := Fin.ext hi0; subst hi
            by_cases hj2 : 2 ≤ j.val
            · rw [Finset.sum_eq_single j]
              · have hne : j ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                simp [hne, hne.symm]
              · intro k hk hkj
                have hk2 : 2 ≤ k.val := (Finset.mem_filter.mp hk).2
                have hne1 : k ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                have hne2 : j ≠ k := hkj.symm
                simp [hne1, hne1.symm, hne2]
              · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩) h
            · have hzero : X ⟨0, h0⟩ j = 0 := by
                by_cases hj0 : j.val = 0
                · have hj : j = ⟨0, h0⟩ := Fin.ext hj0; subst hj; exact hX.1.2 _
                · have hj1 : j = ⟨0 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
                  rw [hj1]; exact hX.2.2.2 ⟨0, by omega⟩
              rw [hzero]
              refine (Finset.sum_eq_zero fun k hk => ?_).symm
              have hk2 : 2 ≤ k.val := (Finset.mem_filter.mp hk).2
              have hne1 : k ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have hne2 : j ≠ k := fun h => by subst h; omega
              simp [hne1, hne1.symm, hne2]
          · by_cases hj0 : j.val = 0
            · have hj : j = ⟨0, h0⟩ := Fin.ext hj0; subst hj
              have hsym : X i ⟨0, h0⟩ = X ⟨0, h0⟩ i := (congrFun (congrFun hX.1.1 i) ⟨0, h0⟩).symm
              rw [hsym]
              by_cases hi2 : 2 ≤ i.val
              · rw [Finset.sum_eq_single i]
                · have hne : i ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp [hne, hne.symm]
                · intro k hk hki
                  have hne1 : i ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have hne2 : i ≠ k := hki.symm
                  simp [hne1, hne1.symm, hne2]
                · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi2⟩) h
              · have hi1 : i = ⟨0 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
                rw [hi1, hX.2.2.2 ⟨0, by omega⟩]
                refine (Finset.sum_eq_zero fun k hk => ?_).symm
                have hk2 : 2 ≤ k.val := (Finset.mem_filter.mp hk).2
                have hne1 : (⟨0 + 1, by omega⟩ : Fin d) ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                have hne2 : (⟨0 + 1, by omega⟩ : Fin d) ≠ k := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                simp [hne1, hne1.symm, hne2]
            · rw [hX.2.1 i j (by omega) (by omega)]
              refine (Finset.sum_eq_zero fun k _ => ?_).symm
              have hne1 : i ≠ ⟨0, h0⟩ := fun h => hi0 (congrArg Fin.val h)
              have hne2 : j ≠ ⟨0, h0⟩ := fun h => hj0 (congrArg Fin.val h)
              simp [hne1, hne2]
        rw [hdecomp]
        refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        have hk2 : 2 ≤ k.val := (Finset.mem_filter.mp hk).2
        let M := Matrix.single ⟨0, h0⟩ k (1 : ZMod 2) + Matrix.single k ⟨0, h0⟩ (1 : ZMod 2)
        have hM_W : M ∈ W := by
          refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
          · ext a b; simp only [M, Matrix.transpose_apply, Matrix.add_apply, msingle_apply]
            have ha1 : (b = (⟨0, h0⟩ : Fin d) ∧ a = k) ↔ (a = k ∧ b = ⟨0, h0⟩) := and_comm
            have ha2 : (b = k ∧ a = (⟨0, h0⟩ : Fin d)) ↔ (a = ⟨0, h0⟩ ∧ b = k) := and_comm
            simp only [ha1, ha2, add_comm]
          · intro a; simp only [M, Matrix.add_apply, msingle_apply]
            have hne : k ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            by_cases ha : a = ⟨0, h0⟩
            · subst ha; simp [hne.symm]
            · by_cases hak : a = k
              · subst hak; simp [hne]
              · simp [ha, hak]
          · intro a b ha hb; simp only [M, Matrix.add_apply, msingle_apply]
            have ha0 : a ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            have hb0 : b ≠ ⟨0, h0⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            simp [ha0, hb0]
          · intro a b
            have ha0 : a.val = 0 := by omega
            have hb0 : b.val = 0 := by omega
            simp [ha0, hb0]
          · intro a
            have ha0 : a.val = 0 := by omega
            simp only [M, Matrix.add_apply, msingle_apply, ha0]
            have hne : (⟨0 + 1, by omega⟩ : Fin d) ≠ k := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            have hne0 : (⟨0, h0⟩ : Fin d) ≠ ⟨0 + 1, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            have hne0k : (⟨0, h0⟩ : Fin d) ≠ k := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            simp [hne, hne0, hne0k]
        have hM_rk : M.rank ≤ 2 := by
          refine rank_le_two_of_two_rows M ⟨0, h0⟩ k fun a b ha0 hak => ?_
          simp [M, msingle_apply, ha0, hak]
        exact ⟨hM_W, hM_rk⟩
    · rw [Submodule.span_le]; rintro X ⟨hX, _⟩; exact hX
  · have hr2 : 2 ≤ r := by omega
    let E : Submodule (ZMod 2) (Fin d → ZMod 2) :=
      { carrier := { v | ∀ i : Fin d, r ≤ i.val → v i = 0 },
        zero_mem' := fun _ _ => rfl, add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi],
        smul_mem' := fun c u hu i hi => by simp [hu i hi] }
    have hfrE : Module.finrank (ZMod 2) E = r := by
      let eE : E ≃ₗ[ZMod 2] (Fin r → ZMod 2) :=
        { toFun := fun v k => v.val ⟨k.val, by omega⟩,
          invFun := fun w => ⟨fun i => if hi : i.val < r then w ⟨i.val, hi⟩ else 0,
            fun i hi => dif_neg (by omega)⟩,
          map_add' := fun _ _ => rfl,
          map_smul' := fun _ _ => rfl,
          left_inv := fun v => Subtype.ext (funext fun i => by
            dsimp only
            by_cases hi : i.val < r
            · rw [dif_pos hi]
            · rw [dif_neg hi, (v.property i (by omega)).symm]),
          right_inv := fun w => funext fun k => by dsimp only; rw [dif_pos k.isLt] }
      rw [eE.finrank_eq, Module.finrank_fin_fun]
    refine ⟨E, by rw [if_neg hr1, hfrE], ?_⟩
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro X hX
        let Xtop : Matrix (Fin d) (Fin d) (ZMod 2) := fun i j => if i.val < r then X i j else 0
        have hXtop_free : Xtop ∈ free E := by
          apply Submodule.subset_span
          intro j i hi; dsimp only [Xtop]; rw [if_neg (by omega)]
        have hXtop_rk2 : Xtop ∈ Submodule.span (ZMod 2) {Y | Y ∈ W ⊔ free E ∧ Y.rank ≤ 2} := by
          have hexp : Xtop = ∑ p : Fin d × Fin d, Xtop p.1 p.2 • Matrix.single p.1 p.2 (1 : ZMod 2) := by
            ext i j
            simp only [Matrix.sum_apply, Matrix.smul_apply, msingle_apply, smul_eq_mul]
            rw [Finset.sum_eq_single (i, j)]
            · simp
            · intro p _ hne
              have : ¬ (i = p.1 ∧ j = p.2) := by rintro ⟨rfl, rfl⟩; exact hne rfl
              simp [this]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hexp]
          refine Submodule.sum_mem _ fun p _ => ?_
          by_cases hp : p.1.val < r
          · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, le_trans (rank_le_one_of_single p.1 p.2) (by omega)⟩)
            apply Submodule.mem_sup_right
            apply Submodule.subset_span
            intro j i hi; simp only [msingle_apply]
            have hne : i ≠ p.1 := fun h => by subst h; omega
            simp [hne]
          · have h0 : Xtop p.1 p.2 = 0 := if_neg hp
            rw [h0, zero_smul]; exact Submodule.zero_mem _
        let Xrem : Matrix (Fin d) (Fin d) (ZMod 2) := X + Xtop
        have hX_eq : X = Xrem + Xtop := by
          ext i j; simp only [Xrem, Matrix.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
        rw [hX_eq]
        refine Submodule.add_mem _ ?_ hXtop_rk2
        have hXrem_eq : Xrem =
            (∑ a : Fin r, ∑ b : Fin r, if a.val < b.val then
              X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ •
                (Matrix.single ⟨a.val + r, by omega⟩ ⟨b.val, by omega⟩ (1 : ZMod 2) +
                 Matrix.single ⟨b.val + r, by omega⟩ ⟨a.val, by omega⟩ (1 : ZMod 2)) else 0) +
            (∑ a : Fin r, ∑ l : Fin (d - 2 * r),
              X ⟨a.val, by omega⟩ ⟨l.val + 2 * r, by omega⟩ •
                Matrix.single ⟨l.val + 2 * r, by omega⟩ ⟨a.val, by omega⟩ (1 : ZMod 2)) := by
          have hXsym : ∀ u w : Fin d, X w u = X u w := fun u w => congrFun (congrFun hX.1.1 u) w
          ext i j
          dsimp only [Xrem]
          rw [Matrix.add_apply]
          dsimp only [Xtop]
          simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, msingle_apply, smul_eq_mul]
          by_cases hi : i.val < r
          · rw [if_pos hi, zmod2_add_self]
            have hS1 : (∑ a : Fin r, ∑ b : Fin r, (if a.val < b.val then
                X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ •
                  (Matrix.single (⟨a.val + r, by omega⟩ : Fin d) (⟨b.val, by omega⟩ : Fin d) (1 : ZMod 2) +
                   Matrix.single (⟨b.val + r, by omega⟩ : Fin d) (⟨a.val, by omega⟩ : Fin d) (1 : ZMod 2)) else 0) i j) = 0 := by
              refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
              split_ifs with hlt
              · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                have hne1 : i ≠ ⟨a.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                have hne2 : i ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                simp [hne1, hne2]
              · rfl
            have hS2 : (∑ a : Fin r, ∑ l : Fin (d - 2 * r),
                X ⟨a.val, by omega⟩ ⟨l.val + 2 * r, by omega⟩ *
                  if i = ⟨l.val + 2 * r, by omega⟩ ∧ j = ⟨a.val, by omega⟩ then 1 else 0) = 0 := by
              refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun l _ => ?_
              have hne : i ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              simp [hne]
            rw [hS1, hS2, add_zero]
          · rw [if_neg hi, add_zero]
            by_cases hj : j.val < r
            · by_cases hi1 : i.val < 2 * r
              · have hS2 : (∑ a : Fin r, ∑ l : Fin (d - 2 * r),
                    X ⟨a.val, by omega⟩ ⟨l.val + 2 * r, by omega⟩ *
                      if i = ⟨l.val + 2 * r, by omega⟩ ∧ j = ⟨a.val, by omega⟩ then 1 else 0) = 0 := by
                  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun l _ => ?_
                  have hne : i ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp [hne]
                rw [hS2, add_zero]
                let ia : Fin r := ⟨i.val - r, by omega⟩
                let jb : Fin r := ⟨j.val, hj⟩
                have hi_eq : (⟨ia.val + r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp only [ia]; omega)
                have hj_eq : (⟨jb.val, by omega⟩ : Fin d) = j := Fin.ext rfl
                rcases lt_trichotomy ia.val jb.val with hlt | heq | hgt
                · rw [Finset.sum_eq_single ia]
                  · rw [Finset.sum_eq_single jb]
                    · rw [if_pos hlt]
                      simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply, hi_eq, hj_eq, smul_eq_mul]
                      have hne : i ≠ ⟨jb.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only [ia, jb] at this hlt; omega
                      simp only [hne, false_and, ↓reduceIte, and_self, add_zero, mul_one]
                      have hsym := hX.2.2.1 ia jb
                      rw [hi_eq, hj_eq] at hsym
                      rw [hXsym j i, ← hsym]
                    · intro b _ hne
                      split_ifs with h1
                      · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                        have hn1 : j ≠ ⟨b.val, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [jb] at *; omega))
                        have hn2 : i ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only [ia] at this h1; omega
                        simp [hn1, hn2]
                      · rfl
                    · intro h; exact absurd (Finset.mem_univ jb) h
                  · intro a _ hne
                    refine Finset.sum_eq_zero fun b _ => ?_
                    split_ifs with h1
                    · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                      have hn1 : i ≠ ⟨a.val + r, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [ia] at *; omega))
                      have hn2 : ¬ (i = ⟨b.val + r, by omega⟩ ∧ j = ⟨a.val, by omega⟩) := by
                        rintro ⟨h1a, h1b⟩
                        have v1 := congrArg Fin.val h1a; have v2 := congrArg Fin.val h1b
                        dsimp only [ia, jb] at hlt h1 v1 v2; omega
                      simp [hn1, hn2]
                    · rfl
                  · intro h; exact absurd (Finset.mem_univ ia) h
                · have hzero : X i j = 0 := by
                    rw [hXsym j i]
                    have h1 : X j i = X ⟨jb.val, by omega⟩ ⟨jb.val + r, by omega⟩ :=
                      congrArg₂ X (Fin.ext rfl) (Fin.ext (by dsimp only [ia, jb] at heq ⊢; omega))
                    rw [h1]; exact hX.2.2.2 jb
                  rw [hzero]
                  refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_).symm
                  split_ifs with h1
                  · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                    have hn1 : ¬ (i = ⟨a.val + r, by omega⟩ ∧ j = ⟨b.val, by omega⟩) := by
                      rintro ⟨h1a, h1b⟩
                      have v1 := congrArg Fin.val h1a; have v2 := congrArg Fin.val h1b
                      dsimp only [ia, jb] at heq v1 v2; omega
                    have hn2 : ¬ (i = ⟨b.val + r, by omega⟩ ∧ j = ⟨a.val, by omega⟩) := by
                      rintro ⟨h1a, h1b⟩
                      have v1 := congrArg Fin.val h1a; have v2 := congrArg Fin.val h1b
                      dsimp only [ia, jb] at heq v1 v2; omega
                    simp [hn1, hn2]
                  · rfl
                · rw [Finset.sum_eq_single jb]
                  · rw [Finset.sum_eq_single ia]
                    · rw [if_pos hgt]
                      simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply, hi_eq, hj_eq, smul_eq_mul]
                      have hne : i ≠ ⟨jb.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only [ia, jb] at this hgt; omega
                      simp only [hne, false_and, ↓reduceIte, and_self, zero_add, mul_one]
                      exact hXsym j i
                    · intro b _ hne
                      split_ifs with h1
                      · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                        have hn1 : i ≠ ⟨jb.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only [ia, jb] at this hgt; omega
                        have hn2 : i ≠ ⟨b.val + r, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [ia] at *; omega))
                        simp [hn1, hn2]
                      · rfl
                    · intro h; exact absurd (Finset.mem_univ ia) h
                  · intro a _ hne
                    refine Finset.sum_eq_zero fun b _ => ?_
                    split_ifs with h1
                    · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                      have hn1 : ¬ (i = ⟨a.val + r, by omega⟩ ∧ j = ⟨b.val, by omega⟩) := by
                        rintro ⟨h1a, h1b⟩
                        have v1 := congrArg Fin.val h1a; have v2 := congrArg Fin.val h1b
                        dsimp only [ia, jb] at hgt v1 v2; omega
                      have hn2 : j ≠ ⟨a.val, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [jb] at *; omega))
                      simp [hn1, hn2]
                    · rfl
                  · intro h; exact absurd (Finset.mem_univ jb) h
              · have hS1 : (∑ a : Fin r, ∑ b : Fin r, (if a.val < b.val then
                    X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ •
                      (Matrix.single (⟨a.val + r, by omega⟩ : Fin d) (⟨b.val, by omega⟩ : Fin d) (1 : ZMod 2) +
                       Matrix.single (⟨b.val + r, by omega⟩ : Fin d) (⟨a.val, by omega⟩ : Fin d) (1 : ZMod 2)) else 0) i j) = 0 := by
                  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
                  split_ifs with hlt
                  · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                    have hne1 : i ≠ ⟨a.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                    have hne2 : i ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                    simp [hne1, hne2]
                  · rfl
                rw [hS1, zero_add]
                let jb : Fin r := ⟨j.val, hj⟩
                let il : Fin (d - 2 * r) := ⟨i.val - 2 * r, by omega⟩
                have hi_eq : (⟨il.val + 2 * r, by omega⟩ : Fin d) = i := Fin.ext (by dsimp only [il]; omega)
                have hj_eq : (⟨jb.val, by omega⟩ : Fin d) = j := Fin.ext rfl
                rw [Finset.sum_eq_single jb]
                · rw [Finset.sum_eq_single il]
                  · rw [hi_eq, hj_eq]; simp [hXsym j i]
                  · intro l _ hne
                    have : i ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [il] at *; omega))
                    simp [this]
                  · intro h; exact absurd (Finset.mem_univ il) h
                · intro a _ hne
                  refine Finset.sum_eq_zero fun l _ => ?_
                  have : j ≠ ⟨a.val, by omega⟩ := fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp only [jb] at *; omega))
                  simp [this]
                · intro h; exact absurd (Finset.mem_univ jb) h
            · rw [hX.2.1 i j (by omega) (by omega)]
              have hS1 : (∑ a : Fin r, ∑ b : Fin r, (if a.val < b.val then
                  X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ •
                    (Matrix.single (⟨a.val + r, by omega⟩ : Fin d) (⟨b.val, by omega⟩ : Fin d) (1 : ZMod 2) +
                     Matrix.single (⟨b.val + r, by omega⟩ : Fin d) (⟨a.val, by omega⟩ : Fin d) (1 : ZMod 2)) else 0) i j) = 0 := by
                refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
                split_ifs with hlt
                · simp only [Matrix.smul_apply, Matrix.add_apply, msingle_apply]
                  have hne1 : j ≠ ⟨b.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have hne2 : j ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp [hne1, hne2]
                · rfl
              have hS2 : (∑ a : Fin r, ∑ l : Fin (d - 2 * r),
                  X ⟨a.val, by omega⟩ ⟨l.val + 2 * r, by omega⟩ *
                    if i = ⟨l.val + 2 * r, by omega⟩ ∧ j = ⟨a.val, by omega⟩ then 1 else 0) = 0 := by
                refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun l _ => ?_
                have hne : j ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                simp [hne]
              rw [hS1, hS2, add_zero]
        rw [hXrem_eq]
        refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_)
          (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun l _ => ?_)
        · split_ifs with hlt
          · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, ?_⟩)
            · let M : Matrix (Fin d) (Fin d) (ZMod 2) :=
                  Matrix.single ⟨a.val + r, by omega⟩ ⟨b.val, by omega⟩ (1 : ZMod 2) +
                  Matrix.single ⟨b.val + r, by omega⟩ ⟨a.val, by omega⟩ (1 : ZMod 2)
              let Mtop : Matrix (Fin d) (Fin d) (ZMod 2) :=
                  Matrix.single ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ (1 : ZMod 2) +
                  Matrix.single ⟨b.val, by omega⟩ ⟨a.val + r, by omega⟩ (1 : ZMod 2)
              have hM_eq : M = (M + Mtop) + Mtop := by
                ext u w; simp only [Matrix.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
              change M ∈ W ⊔ free E
              rw [hM_eq]
              have hMW : M + Mtop ∈ W := by
                refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
                · ext u w; simp only [M, Mtop, Matrix.transpose_apply, Matrix.add_apply, msingle_apply]
                  have ha1 : (w = (⟨a.val + r, by omega⟩ : Fin d) ∧ u = ⟨b.val, by omega⟩) ↔ (u = ⟨b.val, by omega⟩ ∧ w = ⟨a.val + r, by omega⟩) := and_comm
                  have ha2 : (w = (⟨b.val + r, by omega⟩ : Fin d) ∧ u = ⟨a.val, by omega⟩) ↔ (u = ⟨a.val, by omega⟩ ∧ w = ⟨b.val + r, by omega⟩) := and_comm
                  have ha3 : (w = (⟨a.val, by omega⟩ : Fin d) ∧ u = ⟨b.val + r, by omega⟩) ↔ (u = ⟨b.val + r, by omega⟩ ∧ w = ⟨a.val, by omega⟩) := and_comm
                  have ha4 : (w = (⟨b.val, by omega⟩ : Fin d) ∧ u = ⟨a.val + r, by omega⟩) ↔ (u = ⟨a.val + r, by omega⟩ ∧ w = ⟨b.val, by omega⟩) := and_comm
                  simp only [ha1, ha2, ha3, ha4]; ring
                · intro u; simp only [M, Mtop, Matrix.add_apply, msingle_apply]
                  have h1 : ¬ (u = ⟨a.val + r, by omega⟩ ∧ u = ⟨b.val, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
                  have h2 : ¬ (u = ⟨b.val + r, by omega⟩ ∧ u = ⟨a.val, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
                  have h3 : ¬ (u = ⟨a.val, by omega⟩ ∧ u = ⟨b.val + r, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
                  have h4 : ¬ (u = ⟨b.val, by omega⟩ ∧ u = ⟨a.val + r, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
                  simp [h1, h2, h3, h4]
                · intro u w hu hw; simp only [M, Mtop, Matrix.add_apply, msingle_apply]
                  have h1 : w ≠ ⟨b.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h2 : w ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h3 : u ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h4 : u ≠ ⟨b.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp [h1, h2, h3, h4]
                · intro u w; simp only [M, Mtop, Matrix.add_apply, msingle_apply]
                  have h1 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨a.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h2 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h3 : (⟨w.val, by omega⟩ : Fin d) ≠ ⟨a.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h4 : (⟨w.val, by omega⟩ : Fin d) ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp only [h1, h2, h3, h4, false_and, ↓reduceIte, zero_add]
                  have eq1 : ((⟨u.val, by omega⟩ : Fin d) = ⟨a.val, by omega⟩ ∧ (⟨w.val + r, by omega⟩ : Fin d) = ⟨b.val + r, by omega⟩) ↔
                      ((⟨w.val, by omega⟩ : Fin d) = ⟨b.val, by omega⟩ ∧ (⟨u.val + r, by omega⟩ : Fin d) = ⟨a.val + r, by omega⟩) := by
                    constructor <;> (rintro ⟨ha, hb⟩; have va := congrArg Fin.val ha; have vb := congrArg Fin.val hb; dsimp only at va vb; exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by dsimp only; omega)⟩)
                  have eq2 : ((⟨u.val, by omega⟩ : Fin d) = ⟨b.val, by omega⟩ ∧ (⟨w.val + r, by omega⟩ : Fin d) = ⟨a.val + r, by omega⟩) ↔
                      ((⟨w.val, by omega⟩ : Fin d) = ⟨a.val, by omega⟩ ∧ (⟨u.val + r, by omega⟩ : Fin d) = ⟨b.val + r, by omega⟩) := by
                    constructor <;> (rintro ⟨ha, hb⟩; have va := congrArg Fin.val ha; have vb := congrArg Fin.val hb; dsimp only at va vb; exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by dsimp only; omega)⟩)
                  simp only [eq1, eq2]; rw [add_comm]
                · intro u; simp only [M, Mtop, Matrix.add_apply, msingle_apply]
                  have h1 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨a.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h2 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨b.val + r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  have h3 : ¬ ((⟨u.val, by omega⟩ : Fin d) = ⟨a.val, by omega⟩ ∧ (⟨u.val + r, by omega⟩ : Fin d) = ⟨b.val + r, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have va := congrArg Fin.val ha; have vb := congrArg Fin.val hb; dsimp only at va vb; omega
                  have h4 : ¬ ((⟨u.val, by omega⟩ : Fin d) = ⟨b.val, by omega⟩ ∧ (⟨u.val + r, by omega⟩ : Fin d) = ⟨a.val + r, by omega⟩) := by
                    rintro ⟨ha, hb⟩; have va := congrArg Fin.val ha; have vb := congrArg Fin.val hb; dsimp only at va vb; omega
                  simp only [h1, h2, h3, h4, false_and, ↓reduceIte, add_zero]
              have hMtop_free : Mtop ∈ free E := by
                apply Submodule.subset_span
                intro j i hi; simp only [Mtop, Matrix.add_apply, msingle_apply]
                have h1 : i ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                have h2 : i ≠ ⟨b.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                simp [h1, h2]
              exact Submodule.add_mem_sup hMW hMtop_free
            · refine rank_le_two_of_two_rows _ ⟨a.val + r, by omega⟩ ⟨b.val + r, by omega⟩ fun i j h1 h2 => ?_
              simp [msingle_apply, h1, h2]
          · exact Submodule.zero_mem _
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, le_trans (rank_le_one_of_single _ _) (by omega)⟩)
          let N1 : Matrix (Fin d) (Fin d) (ZMod 2) := Matrix.single ⟨l.val + 2 * r, by omega⟩ ⟨a.val, by omega⟩ (1 : ZMod 2)
          let Ntop : Matrix (Fin d) (Fin d) (ZMod 2) := Matrix.single ⟨a.val, by omega⟩ ⟨l.val + 2 * r, by omega⟩ (1 : ZMod 2)
          have hN_eq : N1 = (N1 + Ntop) + Ntop := by
            ext u w; simp only [Matrix.add_apply]; rw [add_assoc, zmod2_add_self, add_zero]
          change N1 ∈ W ⊔ free E
          rw [hN_eq]
          have hNW : N1 + Ntop ∈ W := by
            refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
            · ext u w; simp only [N1, Ntop, Matrix.transpose_apply, Matrix.add_apply, msingle_apply]
              have ha1 : (w = (⟨l.val + 2 * r, by omega⟩ : Fin d) ∧ u = ⟨a.val, by omega⟩) ↔ (u = ⟨a.val, by omega⟩ ∧ w = ⟨l.val + 2 * r, by omega⟩) := and_comm
              have ha2 : (w = (⟨a.val, by omega⟩ : Fin d) ∧ u = ⟨l.val + 2 * r, by omega⟩) ↔ (u = ⟨l.val + 2 * r, by omega⟩ ∧ w = ⟨a.val, by omega⟩) := and_comm
              simp only [ha1, ha2, add_comm]
            · intro u; simp only [N1, Ntop, Matrix.add_apply, msingle_apply]
              have h1 : ¬ (u = ⟨l.val + 2 * r, by omega⟩ ∧ u = ⟨a.val, by omega⟩) := by
                rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
              have h2 : ¬ (u = ⟨a.val, by omega⟩ ∧ u = ⟨l.val + 2 * r, by omega⟩) := by
                rintro ⟨ha, hb⟩; have := congrArg Fin.val (ha.symm.trans hb); dsimp only at this; omega
              simp [h1, h2]
            · intro u w hu hw; simp only [N1, Ntop, Matrix.add_apply, msingle_apply]
              have h1 : w ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have h2 : u ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              simp [h1, h2]
            · intro u w; simp only [N1, Ntop, Matrix.add_apply, msingle_apply]
              have h1 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have h2 : (⟨w.val + r, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have h3 : (⟨w.val, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have h4 : (⟨u.val + r, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              simp [h1, h2, h3, h4]
            · intro u; simp only [N1, Ntop, Matrix.add_apply, msingle_apply]
              have h1 : (⟨u.val, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              have h2 : (⟨u.val + r, by omega⟩ : Fin d) ≠ ⟨l.val + 2 * r, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
              simp [h1, h2]
          have hNtop_free : Ntop ∈ free E := by
            apply Submodule.subset_span
            intro j i hi; simp only [Ntop, msingle_apply]
            have h1 : i ≠ ⟨a.val, by omega⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
            simp [h1]
          exact Submodule.add_mem_sup hNW hNtop_free
      · rw [Submodule.span_le]
        intro Z hZ
        have hexp : Z = ∑ j0 : Fin d, Matrix.of (fun i j => if j = j0 then Z i j0 else 0) := by
          ext i j; simp only [Matrix.sum_apply, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
          · intro j0 _ hne; simp [hne.symm]
          · intro h; exact absurd (Finset.mem_univ j) h
        rw [hexp]
        refine Submodule.sum_mem _ fun j0 _ => Submodule.subset_span ⟨?_, le_trans (rank_le_one_of_col_vec (fun i => Z i j0) j0) (by omega)⟩
        apply Submodule.mem_sup_right
        apply Submodule.subset_span
        intro j
        by_cases hj : j = j0
        · subst hj; simpa only [Matrix.of_apply, ↓reduceIte] using hZ j
        · simp only [Matrix.of_apply, if_neg hj]; exact E.zero_mem
    · rw [Submodule.span_le]; rintro X ⟨hX, _⟩; exact hX

private lemma ann_finrank_ge {r : ℕ} (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    let Ann : Submodule (ZMod 2) (Fin r → ZMod 2) :=
      { carrier := { v | ∀ u ∈ U, dotProduct v u = 0 },
        zero_mem' := fun _ _ => by simp, add_mem' := fun {a b} ha hb u hu => by
          change dotProduct (a + b) u = 0; rw [add_dotProduct, ha u hu, hb u hu, add_zero],
        smul_mem' := fun c a ha u hu => by
          change dotProduct (c • a) u = 0; rw [smul_dotProduct, ha u hu, smul_zero] }
    Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) Ann = r := by
  intro Ann
  let ev : (Fin r → ZMod 2) →ₗ[ZMod 2] (U →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun v =>
        { toFun := fun u => dotProduct v u.val,
          map_add' := fun u1 u2 => dotProduct_add v u1.val u2.val,
          map_smul' := fun c u => by simp [dotProduct_smul] },
      map_add' := fun v1 v2 => LinearMap.ext fun u => add_dotProduct v1 v2 u.val,
      map_smul' := fun c v => LinearMap.ext fun u => by simp [smul_dotProduct] }
  have hker : LinearMap.ker ev = Ann := by
    ext v; simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply, Subtype.forall]
    rfl
  have hsurj : Function.Surjective ev := by
    intro φ
    rcases Submodule.exists_isCompl U with ⟨C, hC⟩
    have hsplit : ∀ x : Fin r → ZMod 2, ∃ u ∈ U, ∃ c ∈ C, u + c = x := by
      intro x
      have htop : x ∈ U ⊔ C := by rw [hC.sup_eq_top]; trivial
      exact Submodule.mem_sup.mp htop
    have huniq : ∀ u ∈ U, ∀ c ∈ C, u + c = 0 → u = 0 := by
      intro u hu c hc h0
      have hmem : u ∈ U ⊓ C := ⟨hu, by rw [eq_neg_of_add_eq_zero_left h0]; exact C.neg_mem hc⟩
      rwa [hC.inf_eq_bot, Submodule.mem_bot] at hmem
    let getU : (Fin r → ZMod 2) → U := fun x => ⟨Classical.choose (hsplit x), (Classical.choose_spec (hsplit x)).1⟩
    have hgetU_eq : ∀ x u (hu : u ∈ U) c, c ∈ C → u + c = x → getU x = ⟨u, hu⟩ := by
      intro x u hu c hc hx
      have h1 := Classical.choose_spec (hsplit x)
      let u1 := Classical.choose (hsplit x)
      let c1 := Classical.choose h1.2
      have hc1 := Classical.choose_spec h1.2
      apply Subtype.ext; change u1 = u
      have h0 : (u1 - u) + (c1 - c) = 0 := by
        have heq := hc1.2.trans hx.symm
        funext i; have hi := congrFun heq i; simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢; linear_combination hi
      exact sub_eq_zero.mp (huniq (u1 - u) (U.sub_mem h1.1 hu) (c1 - c) (C.sub_mem hc1.1 hc) h0)
    let ψ : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => φ (getU x),
        map_add' := fun x1 x2 => by
          have h1 := Classical.choose_spec (hsplit x1)
          let u1 := Classical.choose (hsplit x1); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
          have h2 := Classical.choose_spec (hsplit x2)
          let u2 := Classical.choose (hsplit x2); let c2 := Classical.choose h2.2; have hc2 := Classical.choose_spec h2.2
          have hsum : (u1 + u2) + (c1 + c2) = x1 + x2 := by
            calc (u1 + u2) + (c1 + c2) = (u1 + c1) + (u2 + c2) := by abel
              _ = x1 + x2 := by rw [hc1.2, hc2.2]
          have hgu := hgetU_eq (x1 + x2) (u1 + u2) (U.add_mem h1.1 h2.1) (c1 + c2) (C.add_mem hc1.1 hc2.1) hsum
          rw [hgu]; exact map_add φ (getU x1) (getU x2)
        map_smul' := fun s x => by
          have h1 := Classical.choose_spec (hsplit x)
          let u1 := Classical.choose (hsplit x); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
          have hsm : s • u1 + s • c1 = s • x := by rw [← smul_add, hc1.2]
          have hgu := hgetU_eq (s • x) (s • u1) (U.smul_mem s h1.1) (s • c1) (C.smul_mem s hc1.1) hsm
          rw [hgu]; exact map_smul φ s (getU x) }
    refine ⟨fun j => ψ (Pi.single j 1), LinearMap.ext fun u => ?_⟩
    have hu_eq : u.val = ∑ j : Fin r, u.val j • Pi.single j (1 : ZMod 2) := by
      funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hdot : dotProduct (fun j => ψ (Pi.single j 1)) u.val = ψ u.val := by
      conv_rhs => rw [hu_eq, map_sum]
      simp only [dotProduct, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    change dotProduct (fun j => ψ (Pi.single j 1)) u.val = φ u
    rw [hdot]
    change φ (getU u.val) = φ u
    rw [hgetU_eq u.val u.val u.property 0 C.zero_mem (by simp)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Module.finrank_fin_fun] at hrn
  have hdual : Module.finrank (ZMod 2) (U →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) U :=
    Subspace.dual_finrank_eq
  omega

private lemma alt_rank_mod_bound {r : ℕ} (A B : Submodule (ZMod 2) (Fin r → ZMod 2))
    (D : Matrix (Fin r) (Fin r) (ZMod 2)) (hD : D.transpose = D ∧ ∀ i, D i i = 0)
    (lam mu : Fin r → ZMod 2)
    (hlam : ∀ u ∈ A ⊔ B, dotProduct lam u = 0)
    (hmu : ∀ u ∈ A ⊓ B, dotProduct mu u = 0)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin)) +
      Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp D.mulVecLin)) ≤ 2) :
    dotProduct lam (D.mulVec mu) = 0 := by
  let V := LinearMap.range D.mulVecLin
  have hmod : ∀ S : Submodule (ZMod 2) (Fin r → ZMod 2),
      Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ S).comp D.mulVecLin)) +
      Module.finrank (ZMod 2) ↥(V ⊓ S) = Module.finrank (ZMod 2) V := by
    intro S
    let fS : V →ₗ[ZMod 2] ((Fin r → ZMod 2) ⧸ S) := (Submodule.mkQ S).comp V.subtype
    have hrg : LinearMap.range fS = LinearMap.range ((Submodule.mkQ S).comp D.mulVecLin) := by
      ext q; simp only [fS, LinearMap.mem_range, LinearMap.comp_apply, Submodule.coe_subtype, Subtype.exists]
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨D.mulVec x, ⟨x, rfl⟩, rfl⟩
    have hker : (LinearMap.ker fS).map V.subtype = V ⊓ S := by
      ext w; simp only [Submodule.mem_map, LinearMap.mem_ker, fS, LinearMap.comp_apply,
        Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_inf]
      constructor
      · rintro ⟨⟨y, hyV⟩, hyS, rfl⟩; exact ⟨hyV, hyS⟩
      · rintro ⟨hwV, hwS⟩; exact ⟨⟨w, hwV⟩, hwS, rfl⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker fS
    rw [hrg, ← Submodule.finrank_map_subtype_eq V (LinearMap.ker fS), hker] at hrn
    exact hrn
  by_cases hVA : V ≤ A ⊔ B
  · exact hlam (D.mulVec mu) (hVA ⟨mu, rfl⟩)
  · have hA0 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin)) ≠ 0 := by
      intro hz
      have h1 := hmod A; rw [hz, zero_add] at h1
      have hVA_eq : V ⊓ A = V := Submodule.eq_of_le_of_finrank_eq inf_le_left h1
      apply hVA
      intro w hw; rw [← hVA_eq] at hw; exact Submodule.mem_sup_left hw.2
    have hB0 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp D.mulVecLin)) ≠ 0 := by
      intro hz
      have h1 := hmod B; rw [hz, zero_add] at h1
      have hVB_eq : V ⊓ B = V := Submodule.eq_of_le_of_finrank_eq inf_le_left h1
      apply hVA
      intro w hw; rw [← hVB_eq] at hw; exact Submodule.mem_sup_right hw.2
    have hA1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin)) = 1 := by omega
    have hB1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp D.mulVecLin)) = 1 := by omega
    have hfrA := hmod A; rw [hA1] at hfrA
    have hfrB := hmod B; rw [hB1] at hfrB
    have hVA_eq_VB : V ⊓ A = V ⊓ B := by
      by_contra hne
      have hsup_le : (V ⊓ A) ⊔ (V ⊓ B) ≤ V := sup_le inf_le_left inf_le_left
      have hlt : V ⊓ A < (V ⊓ A) ⊔ (V ⊓ B) := by
        refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
        have hle_BA : V ⊓ B ≤ V ⊓ A := le_sup_right.trans (le_of_eq heq.symm)
        exact (Submodule.eq_of_le_of_finrank_eq hle_BA (by omega)).symm
      have hfr_gt := Submodule.finrank_lt_finrank_of_lt hlt
      have hfr_le := Submodule.finrank_mono hsup_le
      have hsup_eq : (V ⊓ A) ⊔ (V ⊓ B) = V := Submodule.eq_of_le_of_finrank_eq hsup_le (by omega)
      apply hVA
      intro w hw
      rw [← hsup_eq] at hw
      rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
      exact Submodule.add_mem_sup hu.2 hv.2
    have hVAB : V ⊓ (A ⊓ B) = V ⊓ A := by
      apply le_antisymm
      · exact inf_le_inf_left V inf_le_left
      · intro w hw; exact ⟨hw.1, hw.2, (hVA_eq_VB ▸ hw).2⟩
    have hfrAB := hmod (A ⊓ B)
    rw [hVAB] at hfrAB
    have hQ1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp D.mulVecLin)) = 1 := by omega
    have hne_bot : LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp D.mulVecLin) ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hQ1; omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hne_bot with ⟨q0, hq0_mem, hq0_ne⟩
    rcases hq0_mem with ⟨x0, rfl⟩
    let v0 := D.mulVec x0
    have hspan_q0 : LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp D.mulVecLin) =
        Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} := by
      have hle : Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} ≤
          LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp D.mulVecLin) := by
        rw [Submodule.span_singleton_le_iff_mem]; exact ⟨x0, rfl⟩
      have hfr1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0}) = 1 :=
        finrank_span_singleton hq0_ne
      exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
    have hdecomp : ∀ x : Fin r → ZMod 2, ∃ c : ZMod 2, D.mulVec x - c • v0 ∈ A ⊓ B := by
      intro x
      have hmem : Submodule.mkQ (A ⊓ B) (D.mulVec x) ∈ Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} := by
        rw [← hspan_q0]; exact ⟨x, rfl⟩
      rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hc, sub_self]
    have hlam_AB : ∀ u ∈ A ⊓ B, dotProduct lam u = 0 := fun u hu => hlam u (Submodule.mem_sup_left hu.1)
    have hdot_formula : ∀ x : Fin r → ZMod 2, ∃ c : ZMod 2,
        dotProduct lam (D.mulVec x) = c * dotProduct lam v0 ∧
        dotProduct mu (D.mulVec x) = c * dotProduct mu v0 := by
      intro x
      rcases hdecomp x with ⟨c, hcab⟩
      have h1 := hlam_AB _ hcab
      have h2 := hmu _ hcab
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h1 h2
      exact ⟨c, h1, h2⟩
    rcases zmod2_cases (dotProduct lam v0) with hlv0 | hlv1
    · rcases hdot_formula mu with ⟨c, h1, _⟩
      rw [h1, hlv0, mul_zero]
    · have hquad : dotProduct lam (D.mulVec lam) = 0 := by
        simp only [dotProduct, Matrix.mulVec]
        have hexp : ∑ a : Fin r, lam a * ∑ b : Fin r, D a b * lam b =
            ∑ a : Fin r, ∑ b : Fin r, lam a * D a b * lam b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => (mul_assoc _ _ _).symm
        rw [hexp]; exact zmod2_quad_alt_zero D hD lam
      rcases hdot_formula lam with ⟨c, h1, h2⟩
      rw [hlv1, mul_one, hquad] at h1
      have hc0 : c = 0 := h1.symm
      rw [hc0, zero_mul] at h2
      have hsym_dot : dotProduct lam (D.mulVec mu) = dotProduct mu (D.mulVec lam) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hDab : D b a = D a b := congrFun (congrFun hD.1 a) b
        rw [hDab]; ring
      rw [hsym_dot, h2]

private lemma canon_fits_lower {d r : ℕ} (h2r : 2 * r ≤ d) (hr2 : 2 ≤ r)
    (E : Submodule (ZMod 2) (Fin d → ZMod 2)) (hE_lt : Module.finrank (ZMod 2) E < r) :
    let W := canonWSub d r h2r
    let free := Submodule.span (ZMod 2) {X : Matrix (Fin d) (Fin d) (ZMod 2) | ∀ j, (fun i => X i j) ∈ E}
    let L := W ⊔ free
    L ≠ Submodule.span (ZMod 2) {X | X ∈ L ∧ X.rank ≤ 2} := by
  intro W free L hL_eq
  let projTop : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := fun v i => v ⟨i.val, by omega⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let projMid : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := fun v i => v ⟨i.val + r, by omega⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let projPair : (Fin d → ZMod 2) →ₗ[ZMod 2] ((Fin r → ZMod 2) × (Fin r → ZMod 2)) :=
    projTop.prod projMid
  let E' := E.map projPair
  have hfrE' : Module.finrank (ZMod 2) E' < r :=
    lt_of_le_of_lt (Submodule.finrank_map_le projPair E) hE_lt
  let A : Submodule (ZMod 2) (Fin r → ZMod 2) :=
    { carrier := { u | (u, 0) ∈ E' },
      zero_mem' := E'.zero_mem, add_mem' := fun {u1 u2} h1 h2 => by
        change (u1 + u2, 0) ∈ E'
        have h := E'.add_mem h1 h2; simpa only [Prod.mk_add_mk, add_zero] using h,
      smul_mem' := fun c u hu => by
        change (c • u, 0) ∈ E'
        have h := E'.smul_mem c hu; simpa only [Prod.smul_mk, smul_zero] using h }
  let B : Submodule (ZMod 2) (Fin r → ZMod 2) := E'.map (LinearMap.snd (ZMod 2) _ _)
  have hfrAB_sum : Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) E' := by
    let f := (LinearMap.snd (ZMod 2) (Fin r → ZMod 2) (Fin r → ZMod 2)).comp E'.subtype
    have hrg : LinearMap.range f = B := by
      ext v; simp [f, B, Submodule.mem_map]
    let eA : A ≃ₗ[ZMod 2] LinearMap.ker f :=
      { toFun := fun u => ⟨⟨(u.val, 0), u.property⟩, rfl⟩,
        invFun := fun k => ⟨k.val.val.1, by
          change (k.val.val.1, (0 : Fin r → ZMod 2)) ∈ E'
          have hk2 : k.val.val.2 = 0 := k.property
          have hpair : (k.val.val.1, (0 : Fin r → ZMod 2)) = k.val.val := Prod.ext rfl hk2.symm
          rw [hpair]; exact k.val.property⟩,
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl,
        left_inv := fun _ => rfl,
        right_inv := fun k => Subtype.ext (Subtype.ext (Prod.ext rfl k.property.symm)) }
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrg, ← eA.finrank_eq] at hrn
    omega
  -- Build shear S : (Fin r → ZMod 2) →ₗ (Fin r → ZMod 2) with ∀ v ∈ B, (S v, v) ∈ E'
  rcases Submodule.exists_isCompl B with ⟨BC, hBC⟩
  let bB := Module.finBasis (ZMod 2) B
  let liftB : Fin (Module.finrank (ZMod 2) B) → (Fin r → ZMod 2) := fun k =>
    (Classical.choose (Submodule.mem_map.mp (bB k).property)).1
  have hliftB_mem : ∀ k, (liftB k, (bB k).val) ∈ E' := by
    intro k
    have hspec := Classical.choose_spec (Submodule.mem_map.mp (bB k).property)
    have hpair : (liftB k, (bB k).val) = Classical.choose (Submodule.mem_map.mp (bB k).property) :=
      Prod.ext rfl hspec.2.symm
    rw [hpair]; exact hspec.1
  let S_on_B : B →ₗ[ZMod 2] (Fin r → ZMod 2) := bB.constr (ZMod 2) liftB
  have hS_on_B_mem : ∀ v : B, (S_on_B v, v.val) ∈ E' := by
    intro v
    have hv := bB.sum_repr v
    rw [← hv, map_sum]
    simp only [Submodule.coe_sum, map_smul, SetLike.val_smul]
    have hpair : (∑ k, bB.repr v k • S_on_B (bB k), ∑ k, bB.repr v k • (bB k).val) =
        ∑ k, bB.repr v k • (S_on_B (bB k), (bB k).val) := by
      apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd]
    rw [hpair]
    refine Submodule.sum_mem E' fun k _ => Submodule.smul_mem E' _ ?_
    have hk : S_on_B (bB k) = liftB k := bB.constr_basis (ZMod 2) liftB k
    rw [hk]; exact hliftB_mem k
  have hsplitB : ∀ x : Fin r → ZMod 2, ∃ b ∈ B, ∃ c ∈ BC, b + c = x := by
    intro x; exact Submodule.mem_sup.mp (by rw [hBC.sup_eq_top]; trivial)
  have huniqB : ∀ b ∈ B, ∀ c ∈ BC, b + c = 0 → b = 0 := by
    intro b hb c hc h0
    have hmem : b ∈ B ⊓ BC := ⟨hb, by rw [eq_neg_of_add_eq_zero_left h0]; exact BC.neg_mem hc⟩
    rwa [hBC.inf_eq_bot, Submodule.mem_bot] at hmem
  let getB : (Fin r → ZMod 2) → B := fun x => ⟨Classical.choose (hsplitB x), (Classical.choose_spec (hsplitB x)).1⟩
  have hgetB_eq : ∀ x b (hb : b ∈ B) c, c ∈ BC → b + c = x → getB x = ⟨b, hb⟩ := by
    intro x b hb c hc hx
    have h1 := Classical.choose_spec (hsplitB x)
    let b1 := Classical.choose (hsplitB x); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
    apply Subtype.ext; change b1 = b
    have h0 : (b1 - b) + (c1 - c) = 0 := by
      have heq := hc1.2.trans hx.symm
      funext i; have hi := congrFun heq i; simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢; linear_combination hi
    exact sub_eq_zero.mp (huniqB _ (B.sub_mem h1.1 hb) _ (BC.sub_mem hc1.1 hc) h0)
  let S : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := fun x => S_on_B (getB x),
      map_add' := fun x1 x2 => by
        have h1 := Classical.choose_spec (hsplitB x1)
        let b1 := Classical.choose (hsplitB x1); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
        have h2 := Classical.choose_spec (hsplitB x2)
        let b2 := Classical.choose (hsplitB x2); let c2 := Classical.choose h2.2; have hc2 := Classical.choose_spec h2.2
        have hsum : (b1 + b2) + (c1 + c2) = x1 + x2 := by
          calc (b1 + b2) + (c1 + c2) = (b1 + c1) + (b2 + c2) := by abel
            _ = x1 + x2 := by rw [hc1.2, hc2.2]
        rw [hgetB_eq (x1 + x2) (b1 + b2) (B.add_mem h1.1 h2.1) (c1 + c2) (BC.add_mem hc1.1 hc2.1) hsum]
        exact map_add S_on_B (getB x1) (getB x2)
      map_smul' := fun s x => by
        have h1 := Classical.choose_spec (hsplitB x)
        let b1 := Classical.choose (hsplitB x); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
        have hsm : s • b1 + s • c1 = s • x := by rw [← smul_add, hc1.2]
        rw [hgetB_eq (s • x) (s • b1) (B.smul_mem s h1.1) (s • c1) (BC.smul_mem s hc1.1) hsm]
        exact map_smul S_on_B s (getB x) }
  have hS_kills_E : ∀ w ∈ E, projTop w + S (projMid w) ∈ A ∧ projMid w ∈ B := by
    intro w hwE
    have hwE' : (projTop w, projMid w) ∈ E' := Submodule.mem_map.mpr ⟨w, hwE, rfl⟩
    have hwB : projMid w ∈ B := Submodule.mem_map.mpr ⟨(projTop w, projMid w), hwE', rfl⟩
    have hSw : (S (projMid w), projMid w) ∈ E' := by
      change (S_on_B (getB (projMid w)), projMid w) ∈ E'
      rw [hgetB_eq (projMid w) (projMid w) hwB 0 BC.zero_mem (by simp)]
      exact hS_on_B_mem ⟨projMid w, hwB⟩
    refine ⟨?_, hwB⟩
    change (projTop w + S (projMid w), 0) ∈ E'
    have hadd := E'.add_mem hwE' hSw
    have hzero : projMid w + projMid w = 0 := funext fun i => zmod2_add_self _
    simpa only [Prod.mk_add_mk, hzero] using hadd
  -- Pick linearly independent lam ∈ Ann(A ⊔ B) and mu ∈ Ann(A ⊓ B)
  let AnnSup : Submodule (ZMod 2) (Fin r → ZMod 2) :=
    { carrier := { v | ∀ u ∈ A ⊔ B, dotProduct v u = 0 },
      zero_mem' := fun _ _ => by simp, add_mem' := fun {a b} ha hb u hu => by
        change dotProduct (a + b) u = 0; rw [add_dotProduct, ha u hu, hb u hu, add_zero],
      smul_mem' := fun c a ha u hu => by
        change dotProduct (c • a) u = 0; rw [smul_dotProduct, ha u hu, smul_zero] }
  let AnnInf : Submodule (ZMod 2) (Fin r → ZMod 2) :=
    { carrier := { v | ∀ u ∈ A ⊓ B, dotProduct v u = 0 },
      zero_mem' := fun _ _ => by simp, add_mem' := fun {a b} ha hb u hu => by
        change dotProduct (a + b) u = 0; rw [add_dotProduct, ha u hu, hb u hu, add_zero],
      smul_mem' := fun c a ha u hu => by
        change dotProduct (c • a) u = 0; rw [smul_dotProduct, ha u hu, smul_zero] }
  have hfr_sup_inf := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hfr_AnnSup := ann_finrank_ge (A ⊔ B)
  have hfr_AnnInf := ann_finrank_ge (A ⊓ B)
  have hAnnSup_pos : 1 ≤ Module.finrank (ZMod 2) AnnSup := by
    change Module.finrank (ZMod 2) ↥(A ⊔ B) + Module.finrank (ZMod 2) AnnSup = r at hfr_AnnSup; omega
  have hAnnInf_ge2 : 2 ≤ Module.finrank (ZMod 2) AnnInf := by
    have hinf_leA : Module.finrank (ZMod 2) ↥(A ⊓ B) ≤ Module.finrank (ZMod 2) A := Submodule.finrank_mono inf_le_left
    have hinf_leB : Module.finrank (ZMod 2) ↥(A ⊓ B) ≤ Module.finrank (ZMod 2) B := Submodule.finrank_mono inf_le_right
    change Module.finrank (ZMod 2) ↥(A ⊓ B) + Module.finrank (ZMod 2) AnnInf = r at hfr_AnnInf
    omega
  have hAnnSup_ne : AnnSup ≠ ⊥ := by intro hb; rw [hb, finrank_bot] at hAnnSup_pos; omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hAnnSup_ne with ⟨lam, hlam_mem, hlam_ne⟩
  have hex_mu : ∃ mu ∈ AnnInf, mu ≠ 0 ∧ mu ≠ lam := by
    by_contra hall; push Not at hall
    have hle : AnnInf ≤ Submodule.span (ZMod 2) {lam} := by
      intro v hv
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · rw [hall v hv hv0]; exact Submodule.subset_span (Set.mem_singleton lam)
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {lam}) = 1 := finrank_span_singleton hlam_ne
    omega
  rcases hex_mu with ⟨mu, hmu_mem, hmu_ne, hmu_ne_lam⟩
  -- Define linear functional f_bad(Y) = dotProduct (liftMid lam) (Y.mulVec (liftTop mu))
  let liftMid : (Fin r → ZMod 2) → (Fin d → ZMod 2) := fun v i =>
    if h : r ≤ i.val ∧ i.val < 2 * r then v ⟨i.val - r, by omega⟩ else 0
  let liftTop : (Fin r → ZMod 2) → (Fin d → ZMod 2) := fun v i =>
    if h : i.val < r then v ⟨i.val, h⟩ else 0
  let f_bad : Matrix (Fin d) (Fin d) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun Y => dotProduct (liftMid lam) (Y.mulVec (liftTop mu)),
      map_add' := fun Y1 Y2 => by rw [Matrix.add_mulVec, dotProduct_add],
      map_smul' := fun c Y => by simp [Matrix.smul_mulVec, dotProduct_smul] }
  have hf_bad_free : ∀ Z ∈ free, f_bad Z = 0 := by
    intro Z hZ
    refine Submodule.span_induction (fun Y hY => ?_) (map_zero f_bad)
      (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c _ _ ha => by rw [map_smul, ha, smul_zero]) hZ
    dsimp only [f_bad, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hcolB : projMid (fun i => Y i j) ∈ B := (hS_kills_E (fun i => Y i j) (hY j)).2
    have hlam0 : dotProduct lam (projMid (fun i => Y i j)) = 0 := hlam_mem _ (Submodule.mem_sup_right hcolB)
    have hsum_j : ∑ i : Fin d, liftMid lam i * (Y i j * liftTop mu j) =
        dotProduct lam (projMid (fun i => Y i j)) * liftTop mu j := by
      rw [dotProduct, Finset.sum_mul]
      have hflt : ∑ i : Fin d, liftMid lam i * (Y i j * liftTop mu j) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => r ≤ i.val ∧ i.val < 2 * r),
            liftMid lam i * (Y i j * liftTop mu j) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [liftMid]
        split_ifs with h <;> simp
      rw [hflt]
      refine (Finset.sum_bij (fun (a : Fin r) _ => (⟨a.val + r, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_).symm
      · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
      · intro a1 _ a2 _ h; apply Fin.ext; have := congrArg Fin.val h; dsimp only at this; omega
      · intro i hi; rcases (Finset.mem_filter.mp hi).2 with ⟨h1, h2⟩
        exact ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      · intro a _
        dsimp only [liftMid, projMid, LinearMap.coe_mk, AddHom.coe_mk]
        rw [dif_pos ⟨by omega, by omega⟩]
        have ha : (⟨a.val + r - r, by omega⟩ : Fin r) = a := Fin.ext (by dsimp only; omega)
        rw [ha]; ring
    rw [hsum_j, hlam0, zero_mul]
  have hf_bad_W : ∀ X ∈ W, f_bad X = dotProduct lam ((Matrix.of fun a b : Fin r => X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩).mulVec mu) := by
    intro X hX
    dsimp only [f_bad, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    have hflt_i : ∑ i : Fin d, liftMid lam i * ∑ j : Fin d, X i j * liftTop mu j =
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => r ≤ i.val ∧ i.val < 2 * r),
          liftMid lam i * ∑ j : Fin d, X i j * liftTop mu j := by
      rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i _ => by dsimp only [liftMid]; split_ifs <;> simp
    rw [hflt_i]
    refine (Finset.sum_bij (fun (a : Fin r) _ => (⟨a.val + r, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_).symm
    · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
    · intro a1 _ a2 _ h; apply Fin.ext; have := congrArg Fin.val h; dsimp only at this; omega
    · intro i hi; rcases (Finset.mem_filter.mp hi).2 with ⟨h1, h2⟩
      exact ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
    · intro a _
      dsimp only [liftMid]
      rw [dif_pos ⟨by omega, by omega⟩]
      have ha : (⟨a.val + r - r, by omega⟩ : Fin r) = a := Fin.ext (by dsimp only; omega)
      rw [ha]; congr 1
      have hflt_j : ∑ j : Fin d, X ⟨a.val + r, by omega⟩ j * liftTop mu j =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < r), X ⟨a.val + r, by omega⟩ j * liftTop mu j := by
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ => by dsimp only [liftTop]; split_ifs <;> simp
      rw [hflt_j]
      refine Finset.sum_bij (fun (b : Fin r) _ => (⟨b.val, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
      · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩
      · intro b1 _ b2 _ h; exact Fin.ext (congrArg (Fin.val : Fin d → ℕ) h)
      · intro j hj; exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro b _
        dsimp only [liftTop]; rw [dif_pos b.isLt]
        congr 1
        have hsym1 : X ⟨a.val + r, by omega⟩ ⟨b.val, by omega⟩ = X ⟨b.val, by omega⟩ ⟨a.val + r, by omega⟩ :=
          (congrFun (congrFun hX.1.1 (⟨a.val + r, by omega⟩ : Fin d)) (⟨b.val, by omega⟩ : Fin d)).symm
        rw [hsym1, hX.2.2.1 b a]
  have hf_bad_rk2 : ∀ Y ∈ L, Y.rank ≤ 2 → f_bad Y = 0 := by
    intro Y hYL hYrk
    rcases Submodule.mem_sup.mp hYL with ⟨X, hXW, Z, hZfree, rfl⟩
    let D : Matrix (Fin r) (Fin r) (ZMod 2) := fun a b => X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩
    have hD_alt : D.transpose = D ∧ ∀ a, D a a = 0 := by
      refine ⟨?_, hXW.2.2.2⟩
      ext a b; exact hXW.2.2.1 b a
    -- Define Ψ : (Fin d → ZMod 2) →ₗ ((Fin r → ZMod 2) ⧸ A) × ((Fin r → ZMod 2) ⧸ B)
    let Ψ : (Fin d → ZMod 2) →ₗ[ZMod 2] (((Fin r → ZMod 2) ⧸ A) × ((Fin r → ZMod 2) ⧸ B)) :=
      ((Submodule.mkQ A).comp (projTop + S.comp projMid)).prod ((Submodule.mkQ B).comp projMid)
    have hΨ_Z : ∀ w : Fin d → ZMod 2, Ψ (Z.mulVec w) = 0 := by
      have hZ_E : ∀ Z' ∈ free, ∀ w : Fin d → ZMod 2, Ψ (Z'.mulVec w) = 0 := by
        intro Z' hZ'
        refine Submodule.span_induction (fun M hM w => ?_) (fun w => by simp)
          (fun M1 M2 _ _ h1 h2 w => by rw [Matrix.add_mulVec, map_add, h1 w, h2 w, add_zero])
          (fun c M _ h1 w => by rw [Matrix.smul_mulVec, map_smul, h1 w, smul_zero]) hZ'
        have hcol_sum : M.mulVec w = ∑ j : Fin d, w j • (fun i => M i j) := by
          funext i; simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hcol_sum, map_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [map_smul]
        have hkill := hS_kills_E (fun i => M i j) (hM j)
        have h0 : Ψ (fun i => M i j) = 0 := by
          apply Prod.ext
          · change Submodule.mkQ A (projTop (fun i => M i j) + S (projMid (fun i => M i j))) = 0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact hkill.1
          · change Submodule.mkQ B (projMid (fun i => M i j)) = 0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact hkill.2
        rw [h0, smul_zero]
      exact hZ_E Z hZfree
    let Q := LinearMap.range (Ψ.comp (X + Z).mulVecLin)
    have hQ_le2 : Module.finrank (ZMod 2) Q ≤ 2 := by
      have h1 : Module.finrank (ZMod 2) Q ≤ (X + Z).rank := by
        have hQeq : Q = (LinearMap.range (X + Z).mulVecLin).map Ψ := LinearMap.range_comp _ _
        exact hQeq ▸ Submodule.finrank_map_le Ψ (LinearMap.range (X + Z).mulVecLin)
      omega
    have hΨ_eq : ∀ w, Ψ ((X + Z).mulVec w) = Ψ (X.mulVec w) := fun w => by
      rw [Matrix.add_mulVec, map_add, hΨ_Z w, add_zero]
    let p2 : Q →ₗ[ZMod 2] ((Fin r → ZMod 2) ⧸ B) := (LinearMap.snd (ZMod 2) _ _).comp Q.subtype
    have hrg_B : LinearMap.range ((Submodule.mkQ B).comp D.mulVecLin) ≤ LinearMap.range p2 := by
      rintro _ ⟨x, rfl⟩
      have hmid_x : projMid (X.mulVec (liftTop x)) = D.mulVec x := by
        funext a
        simp only [projMid, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        have hflt : ∑ j : Fin d, X ⟨a.val + r, by omega⟩ j * liftTop x j =
            ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < r), X ⟨a.val + r, by omega⟩ j * liftTop x j := by
          rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ => by dsimp only [liftTop]; split_ifs <;> simp
        rw [hflt]
        refine (Finset.sum_bij (fun (b : Fin r) _ => (⟨b.val, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_).symm
        · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩
        · intro b1 _ b2 _ h; exact Fin.ext (congrArg (Fin.val : Fin d → ℕ) h)
        · intro j hj; exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro b _
          dsimp only [liftTop]; rw [dif_pos b.isLt]; congr 1
          have hsym1 : X ⟨a.val + r, by omega⟩ ⟨b.val, by omega⟩ = X ⟨b.val, by omega⟩ ⟨a.val + r, by omega⟩ :=
            (congrFun (congrFun hXW.1.1 (⟨a.val + r, by omega⟩ : Fin d)) (⟨b.val, by omega⟩ : Fin d)).symm
          rw [hsym1, hXW.2.2.1 b a]
      refine ⟨⟨Ψ ((X + Z).mulVec (liftTop x)), ⟨liftTop x, rfl⟩⟩, ?_⟩
      change (Ψ ((X + Z).mulVec (liftTop x))).2 = Submodule.mkQ B (D.mulVec x)
      rw [hΨ_eq, ← hmid_x]; rfl
    have hker_A : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin)) ≤
        Module.finrank (ZMod 2) (LinearMap.ker p2) := by
      let emb : LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin) →ₗ[ZMod 2] LinearMap.ker p2 :=
        { toFun := fun q => ⟨⟨(q.val, 0), by
            rcases q.property with ⟨y, hy⟩
            refine ⟨liftMid y, ?_⟩
            change Ψ ((X + Z).mulVec (liftMid y)) = (q.val, 0)
            rw [hΨ_eq]
            have hmid0 : projMid (X.mulVec (liftMid y)) = 0 := by
              funext a
              simp only [projMid, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct, Pi.zero_apply]
              refine Finset.sum_eq_zero fun j _ => ?_
              dsimp only [liftMid]
              split_ifs with hj
              · rw [hXW.2.1 ⟨a.val + r, by omega⟩ j (by dsimp only; omega) hj.1, zero_mul]
              · simp
            have htop_y : projTop (X.mulVec (liftMid y)) = D.mulVec y := by
              funext a
              simp only [projTop, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
              have hflt : ∑ j : Fin d, X ⟨a.val, by omega⟩ j * liftMid y j =
                  ∑ j ∈ Finset.univ.filter (fun j : Fin d => r ≤ j.val ∧ j.val < 2 * r),
                    X ⟨a.val, by omega⟩ j * liftMid y j := by
                rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ => by dsimp only [liftMid]; split_ifs <;> simp
              rw [hflt]
              refine (Finset.sum_bij (fun (b : Fin r) _ => (⟨b.val + r, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_).symm
              · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩
              · intro b1 _ b2 _ h; apply Fin.ext; have := congrArg Fin.val h; dsimp only at this; omega
              · intro j hj; rcases (Finset.mem_filter.mp hj).2 with ⟨h1, h2⟩
                exact ⟨⟨j.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
              · intro b _
                dsimp only [liftMid]; rw [dif_pos ⟨by omega, by omega⟩]
                exact congrArg (fun x => X ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩ * y x) (Fin.ext (by dsimp only; omega))
            apply Prod.ext
            · change Submodule.mkQ A (projTop (X.mulVec (liftMid y)) + S (projMid (X.mulVec (liftMid y)))) = q.val
              rw [hmid0, map_zero, add_zero, htop_y]
              exact hy
            · change Submodule.mkQ B (projMid (X.mulVec (liftMid y))) = 0
              rw [hmid0, map_zero]⟩, rfl⟩,
          map_add' := fun _ _ => rfl,
          map_smul' := fun _ _ => rfl }
      have hemb_inj : Function.Injective emb := by
        intro q1 q2 h; exact Subtype.ext (congrArg Prod.fst (congrArg Subtype.val (congrArg Subtype.val h)))
      have hrg_emb := LinearMap.finrank_range_of_inj hemb_inj
      rw [← hrg_emb]; exact Submodule.finrank_le _
    have hrn := LinearMap.finrank_range_add_finrank_ker p2
    have hrg_le := Submodule.finrank_mono hrg_B
    have hrk_sum : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp D.mulVecLin)) +
        Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp D.mulVecLin)) ≤ 2 := by omega
    rw [map_add, hf_bad_free Z hZfree, add_zero, hf_bad_W X hXW]
    exact alt_rank_mod_bound A B D hD_alt lam mu hlam_mem hmu_mem hrk_sum
  have hf_bad_L : ∀ Y ∈ L, f_bad Y = 0 := by
    intro Y hYL
    rw [hL_eq] at hYL
    refine Submodule.span_induction (fun M hM => hf_bad_rk2 M hM.1 hM.2) (map_zero f_bad)
      (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c _ _ ha => by rw [map_smul, ha, smul_zero]) hYL
  -- Construct x, y ∈ Fin r → ZMod 2 with lam ⬝ᵥ x = 1, lam ⬝ᵥ y = 0, mu ⬝ᵥ x = 0, mu ⬝ᵥ y = 1
  let evalLM : (Fin r → ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    { toFun := fun v => (dotProduct lam v, dotProduct mu v),
      map_add' := fun v1 v2 => Prod.ext (dotProduct_add lam v1 v2) (dotProduct_add mu v1 v2),
      map_smul' := fun c v => Prod.ext (by simp [dotProduct_smul]) (by simp [dotProduct_smul]) }
  have heval_surj : Function.Surjective evalLM := by
    let P2 := Submodule.span (ZMod 2) ({lam, mu} : Set (Fin r → ZMod 2))
    have hfrP2 : Module.finrank (ZMod 2) P2 = 2 := by
      have hli : LinearIndependent (ZMod 2) (fun b : Fin 2 => if b = 0 then lam else mu) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hc' : c 0 • lam + c 1 • mu = 0 := by
          simpa only [Fin.sum_univ_two, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff] using hc
        rcases zmod2_cases (c 0) with h0 | h0 <;> rcases zmod2_cases (c 1) with h1 | h1
        · intro i; fin_cases i <;> assumption
        · rw [h0, h1, zero_smul, one_smul, zero_add] at hc'; exact absurd hc' hmu_ne
        · rw [h0, h1, one_smul, zero_smul, add_zero] at hc'; exact absurd hc' hlam_ne
        · rw [h0, h1, one_smul, one_smul] at hc'
          have heq : mu = lam := by
            funext i; have hi := congrFun hc' i
            simp only [Pi.add_apply, Pi.zero_apply] at hi
            rcases zmod2_cases (lam i) with hl | hl <;> rcases zmod2_cases (mu i) with hm | hm <;>
              simp [hl, hm, zmod2_add_self] at hi ⊢
          exact absurd heq hmu_ne_lam
      have hspan_eq : Submodule.span (ZMod 2) (Set.range (fun b : Fin 2 => if b = 0 then lam else mu)) = P2 := by
        congr 1; ext v; simp [Fin.exists_fin_two, eq_comm]
      rw [← hspan_eq, finrank_span_eq_card hli, Fintype.card_fin]
    have hker_eq : LinearMap.ker evalLM =
        { carrier := { v | ∀ u ∈ P2, dotProduct v u = 0 },
          zero_mem' := fun _ _ => by simp, add_mem' := fun {a b} ha hb u hu => by
            change dotProduct (a + b) u = 0; rw [add_dotProduct, ha u hu, hb u hu, add_zero],
          smul_mem' := fun c a ha u hu => by
            change dotProduct (c • a) u = 0; rw [smul_dotProduct, ha u hu, smul_zero] } := by
      ext v
      simp only [LinearMap.mem_ker, evalLM, LinearMap.coe_mk, AddHom.coe_mk, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      constructor
      · rintro ⟨h1, h2⟩ u hu
        refine Submodule.span_induction (fun w hw => ?_) (by simp)
          (fun _ _ _ _ ha hb => by rw [dotProduct_add, ha, hb, add_zero])
          (fun c _ _ ha => by rw [dotProduct_smul, ha, smul_zero]) hu
        rcases hw with rfl | rfl
        · rwa [dotProduct_comm]
        · rwa [dotProduct_comm]
      · intro h
        exact ⟨by rw [dotProduct_comm]; exact h lam (Submodule.subset_span (Set.mem_insert _ _)),
               by rw [dotProduct_comm]; exact h mu (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    have hfr_ker := ann_finrank_ge P2
    rw [← hker_eq, hfrP2] at hfr_ker
    have hrn := LinearMap.finrank_range_add_finrank_ker evalLM
    rw [Module.finrank_fin_fun] at hrn
    have hfr_rg : Module.finrank (ZMod 2) (LinearMap.range evalLM) = 2 := by omega
    have htop : LinearMap.range evalLM = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfr_rg, Module.finrank_prod, Module.finrank_self])
    exact LinearMap.range_eq_top.mp htop
  rcases heval_surj (1, 0) with ⟨x, hx⟩
  rcases heval_surj (0, 1) with ⟨y, hy⟩
  have hlx : dotProduct lam x = 1 := congrArg Prod.fst hx
  have hmx : dotProduct mu x = 0 := congrArg Prod.snd hx
  have hly : dotProduct lam y = 0 := congrArg Prod.fst hy
  have hmy : dotProduct mu y = 1 := congrArg Prod.snd hy
  let D0 : Matrix (Fin r) (Fin r) (ZMod 2) := fun a b => x a * y b + y a * x b
  let X0 : Matrix (Fin d) (Fin d) (ZMod 2) := fun i j =>
    if hi : i.val < r then
      if hj : r ≤ j.val ∧ j.val < 2 * r then D0 ⟨i.val, hi⟩ ⟨j.val - r, by omega⟩ else 0
    else if hi1 : r ≤ i.val ∧ i.val < 2 * r then
      if hj : j.val < r then D0 ⟨j.val, hj⟩ ⟨i.val - r, by omega⟩ else 0
    else 0
  have hX0_W : X0 ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · ext i j; change X0 j i = X0 i j; dsimp only [X0]
      by_cases hi : i.val < r
      · by_cases hj : r ≤ j.val ∧ j.val < 2 * r
        · rw [dif_neg (by omega), dif_pos hj, dif_pos hi, dif_pos hi, dif_pos hj]
        · by_cases hj0 : j.val < r
          · rw [dif_pos hj0, dif_neg (by omega), dif_pos hi, dif_neg hj]
          · rw [dif_neg hj0, dif_neg hj, dif_pos hi, dif_neg hj]
      · by_cases hi1 : r ≤ i.val ∧ i.val < 2 * r
        · by_cases hj : j.val < r
          · rw [dif_pos hj, dif_pos hi1, dif_neg hi, dif_pos hi1, dif_pos hj]
          · by_cases hj1 : r ≤ j.val ∧ j.val < 2 * r
            · rw [dif_neg hj, dif_pos hj1, dif_neg hi, dif_neg hi, dif_pos hi1, dif_neg hj]
            · rw [dif_neg hj, dif_neg hj1, dif_neg hi, dif_pos hi1, dif_neg hj]
        · by_cases hj : j.val < r
          · rw [dif_pos hj, dif_neg hi1, dif_neg hi, dif_neg hi1]
          · by_cases hj1 : r ≤ j.val ∧ j.val < 2 * r
            · rw [dif_neg hj, dif_pos hj1, dif_neg hi, dif_neg hi, dif_neg hi1]
            · rw [dif_neg hj, dif_neg hj1, dif_neg hi, dif_neg hi1]
    · intro i; dsimp only [X0]
      by_cases hi : i.val < r
      · rw [dif_pos hi, dif_neg (by omega)]
      · by_cases hi1 : r ≤ i.val ∧ i.val < 2 * r
        · rw [dif_neg hi, dif_pos hi1, dif_neg hi]
        · rw [dif_neg hi, dif_neg hi1]
    · intro i j hi hj; dsimp only [X0]
      rw [dif_neg (by omega)]
      by_cases hi1 : r ≤ i.val ∧ i.val < 2 * r
      · rw [dif_pos hi1, dif_neg (by omega)]
      · rw [dif_neg hi1]
    · intro a b; dsimp only [X0, D0]
      rw [dif_pos a.isLt, dif_pos ⟨by omega, by omega⟩,
        dif_pos b.isLt, dif_pos ⟨by omega, by omega⟩]
      have ha : (⟨a.val + r - r, by omega⟩ : Fin r) = a := Fin.ext (by dsimp only; omega)
      have hb : (⟨b.val + r - r, by omega⟩ : Fin r) = b := Fin.ext (by dsimp only; omega)
      rw [ha, hb]; ring
    · intro a; dsimp only [X0, D0]
      rw [dif_pos a.isLt, dif_pos ⟨by omega, by omega⟩]
      have ha : (⟨a.val + r - r, by omega⟩ : Fin r) = a := Fin.ext (by dsimp only; omega)
      rw [ha]; rw [mul_comm (y a) (x a)]; exact zmod2_add_self _
  have hf0 := hf_bad_L X0 (Submodule.mem_sup_left hX0_W)
  rw [hf_bad_W X0 hX0_W] at hf0
  have hD0_eq : (Matrix.of fun a b : Fin r => X0 ⟨a.val, by omega⟩ ⟨b.val + r, by omega⟩) = D0 := by
    ext a b; dsimp only [Matrix.of_apply, X0]
    rw [dif_pos a.isLt, dif_pos ⟨by omega, by omega⟩]
    congr 1; apply Fin.ext; dsimp only; omega
  rw [hD0_eq] at hf0
  have hval : dotProduct lam (D0.mulVec mu) = 1 := by
    have hcalc : dotProduct lam (D0.mulVec mu) =
        dotProduct lam x * dotProduct mu y + dotProduct lam y * dotProduct mu x := by
      simp only [dotProduct, Matrix.mulVec, D0]
      simp_rw [Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib]
      congr 1 <;> (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
    rw [hcalc, hlx, hmy, hly, hmx]; simp
  rw [hval] at hf0
  exact one_ne_zero hf0

private lemma canon_main {d r : ℕ} (h2r : 2 * r ≤ d) :
    let F := ZMod 2
    let Mat := Matrix (Fin d) (Fin d) F
    let W := canonWSub d r h2r
    let fits := fun (e : ℕ) =>
      ∃ E : Submodule F (Fin d → F), Module.finrank F E ≤ e ∧
        let free := Submodule.span F {X : Mat | ∀ j, (fun i => X i j) ∈ E}
        let L := W ⊔ free
        L = Submodule.span F {X : Mat | X ∈ L ∧ X.rank ≤ 2}
    let D := r * (d - r - 1)
    (∀ e : ℕ, fits e ↔ (if r ≤ 1 then 0 else r) ≤ e) ∧
      ∀ (t : ℕ) (R : Fin t → Mat), (∀ i, (R i).rank ≤ 2) →
        W ≤ Submodule.span F (Set.range R) →
        D ≤ t ∧ (2 ≤ r → r ≤ 2 * (t - D)) := by
  intro F Mat W fits D
  have hfits : ∀ e : ℕ, fits e ↔ (if r ≤ 1 then 0 else r) ≤ e := by
    intro e
    constructor
    · rintro ⟨E, hEe, hEq⟩
      by_cases hr1 : r ≤ 1
      · rw [if_pos hr1]; exact Nat.zero_le e
      · rw [if_neg hr1]
        by_contra hlt
        exact canon_fits_lower h2r (by omega) E (lt_of_le_of_lt hEe (by omega)) hEq
    · intro hle
      rcases canon_fits_upper h2r with ⟨E, hEr, hEq⟩
      exact ⟨E, le_trans hEr hle, hEq⟩
  refine ⟨hfits, ?_⟩
  intro t R hR_rk hW_le
  let VR := Submodule.span (ZMod 2) (Set.range R)
  have hfrW : Module.finrank (ZMod 2) W = D := finrank_canonWSub h2r
  have hfrVR_le : Module.finrank (ZMod 2) VR ≤ t := by
    have h1 : VR = Submodule.span (ZMod 2) (↑(Finset.univ.image R) : Set Mat) := by
      dsimp only [VR]; congr 1; ext M; simp
    rw [h1]
    calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑(Finset.univ.image R) : Set Mat))
        ≤ (Finset.univ.image R).card := finrank_span_finset_le_card _
      _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := by simp
  have hD_le_VR : D ≤ Module.finrank (ZMod 2) VR := by
    rw [← hfrW]; exact Submodule.finrank_mono hW_le
  refine ⟨le_trans hD_le_VR hfrVR_le, fun hr2 => ?_⟩
  -- Pick s = finrank (VR ⧸ W) ≤ t - D generators among R spanning VR mod W
  let qW : Mat →ₗ[ZMod 2] (Mat ⧸ W) := Submodule.mkQ W
  let Q := VR.map qW
  have hfrQ : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) VR - D := by
    let f := qW.comp VR.subtype
    have hrg : LinearMap.range f = Q := by ext x; simp [f, Q, Submodule.mem_map]
    have hker : (LinearMap.ker f).map VR.subtype = W := by
      ext x; simp only [Submodule.mem_map, LinearMap.mem_ker, f, LinearMap.comp_apply,
        Submodule.coe_subtype, qW, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨fun ⟨y, hyW, hyx⟩ => hyx ▸ hyW, fun hxW => ⟨⟨x, hW_le hxW⟩, hxW, rfl⟩⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrg, ← Submodule.finrank_map_subtype_eq VR (LinearMap.ker f), hker, hfrW] at hrn
    omega
  have hQ_span : Q = Submodule.span (ZMod 2) (Set.range (fun i : Fin t => qW (R i))) := by
    dsimp only [Q, VR]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  let s := Module.finrank (ZMod 2) Q
  -- Find a subset J ⊆ Finset.univ of size s whose qW ∘ R images form a basis of Q
  have hex_J : ∃ J : Finset (Fin t), J.card ≤ s ∧ Q ≤ Submodule.span (ZMod 2) (↑(J.image (fun i => qW (R i))) : Set (Mat ⧸ W)) := by
    have hspan_top : Submodule.span (ZMod 2) (Set.range (fun i : Fin t => (⟨qW (R i), by rw [hQ_span]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Q))) = ⊤ := by
      rw [eq_top_iff]; rintro ⟨x, hxQ⟩ _
      have haux : ∀ y, y ∈ Submodule.span (ZMod 2) (Set.range (fun i : Fin t => qW (R i))) →
          ∀ hy : y ∈ Q, (⟨y, hy⟩ : Q) ∈ Submodule.span (ZMod 2) (Set.range (fun i : Fin t => (⟨qW (R i), by rw [hQ_span]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Q))) := by
        intro y hy
        refine Submodule.span_induction (fun z hz _ => ?_) (fun _ => Submodule.zero_mem _)
          (fun a b ha hb iha ihb _ => Submodule.add_mem _ (iha (hQ_span ▸ ha)) (ihb (hQ_span ▸ hb)))
          (fun c a ha iha _ => Submodule.smul_mem _ c (iha (hQ_span ▸ ha))) hy
        rcases hz with ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, rfl⟩
      exact haux x (hQ_span ▸ hxQ) hxQ
    rcases exists_linearIndependent (ZMod 2) (Set.range (fun i : Fin t => (⟨qW (R i), by rw [hQ_span]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Q))) with
      ⟨Bset, hBsub, hBspan, hBli⟩
    have hB_fin : Bset.Finite := Set.toFinite Bset
    let Bfin := hB_fin.toFinset
    have hBcard : Bfin.card ≤ s := by
      have h1 : Bfin.card = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) Bset) := by
        rw [← Subtype.range_coe (s := Bset), finrank_span_eq_card hBli]
        have e : ↥Bfin ≃ ↥Bset := Equiv.subtypeEquivRight (fun x => hB_fin.mem_toFinset)
        rw [← Fintype.card_congr e, Fintype.card_coe]
      rw [h1]; exact Submodule.finrank_le _
    let pickIdx : ↥Bfin → Fin t := fun b => Classical.choose (hBsub (hB_fin.mem_toFinset.mp b.property))
    have hpick : ∀ b : ↥Bfin, qW (R (pickIdx b)) = b.val.val := fun b =>
      congrArg Subtype.val (Classical.choose_spec (hBsub (hB_fin.mem_toFinset.mp b.property)))
    let J : Finset (Fin t) := Finset.univ.image pickIdx
    refine ⟨J, le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_coe]; exact hBcard), ?_⟩
    intro x hxQ
    have hmem_B : (⟨x, hxQ⟩ : Q) ∈ Submodule.span (ZMod 2) Bset := by
      rw [hBspan, hspan_top]; trivial
    have hle_map : (Submodule.span (ZMod 2) Bset).map Q.subtype ≤
        Submodule.span (ZMod 2) (↑(J.image (fun i => qW (R i))) : Set (Mat ⧸ W)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨b, hbB, rfl⟩
      apply Submodule.subset_span
      have hb_fin : b ∈ Bfin := hB_fin.mem_toFinset.mpr hbB
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨pickIdx ⟨b, hb_fin⟩,
        Finset.mem_image.mpr ⟨⟨b, hb_fin⟩, Finset.mem_univ _, rfl⟩, hpick ⟨b, hb_fin⟩⟩)
    exact hle_map (Submodule.mem_map.mpr ⟨⟨x, hxQ⟩, hmem_B, rfl⟩)
  rcases hex_J with ⟨J, hJcard, hJspan⟩
  let E : Submodule (ZMod 2) (Fin d → ZMod 2) := ⨆ i ∈ J, LinearMap.range (R i).mulVecLin
  have hfrE : Module.finrank (ZMod 2) E ≤ 2 * (t - D) := by
    have hbi : ∀ S : Finset (Fin t),
        Module.finrank (ZMod 2) ↥(⨆ i ∈ S, LinearMap.range (R i).mulVecLin) ≤ ∑ i ∈ S, (R i).rank := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [finrank_bot]
      | insert a S ha ih =>
        rw [Finset.iSup_insert, Finset.sum_insert ha]
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq
          (LinearMap.range (R a).mulVecLin) (⨆ i ∈ S, LinearMap.range (R i).mulVecLin)
        have h1 : Module.finrank (ZMod 2) ↥(LinearMap.range (R a).mulVecLin ⊔ ⨆ i ∈ S, LinearMap.range (R i).mulVecLin) ≤
            (R a).rank + Module.finrank (ZMod 2) ↥(⨆ i ∈ S, LinearMap.range (R i).mulVecLin) := by
          change Module.finrank (ZMod 2) ↥(LinearMap.range (R a).mulVecLin ⊔ ⨆ i ∈ S, LinearMap.range (R i).mulVecLin) + _ =
            (R a).rank + Module.finrank (ZMod 2) ↥(⨆ i ∈ S, LinearMap.range (R i).mulVecLin) at hsup
          omega
        omega
    calc Module.finrank (ZMod 2) E ≤ ∑ i ∈ J, (R i).rank := hbi J
      _ ≤ ∑ _i ∈ J, 2 := Finset.sum_le_sum fun i _ => hR_rk i
      _ = J.card * 2 := by simp
      _ ≤ s * 2 := Nat.mul_le_mul_right 2 hJcard
      _ ≤ 2 * (t - D) := by omega
  let free := Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}
  have hR_in_free : ∀ i ∈ J, R i ∈ free := by
    intro i hiJ
    apply Submodule.subset_span
    intro j
    have hcol : (fun a => R i a j) = (R i).mulVec (Pi.single j 1) := by
      funext a; exact (mulVec_single_one (R i) j a).symm
    rw [hcol]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hiJ ⟨Pi.single j 1, rfl⟩)
  have hVR_le : VR ≤ W ⊔ free := by
    intro X hXVR
    have hqX : qW X ∈ Submodule.span (ZMod 2) (↑(J.image (fun i => qW (R i))) : Set (Mat ⧸ W)) :=
      hJspan (Submodule.mem_map.mpr ⟨X, hXVR, rfl⟩)
    have hq_map : Submodule.span (ZMod 2) (↑(J.image (fun i => qW (R i))) : Set (Mat ⧸ W)) =
        (Submodule.span (ZMod 2) (↑(J.image R) : Set Mat)).map qW := by
      rw [Submodule.map_span]
      congr 1; ext y; simp [Finset.mem_image]
    rw [hq_map] at hqX
    rcases Submodule.mem_map.mp hqX with ⟨Y, hYJ, hqY⟩
    have hXY_W : X - Y ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      change qW (X - Y) = 0
      rw [map_sub, hqY, sub_self]
    have hY_free : Y ∈ free := by
      have hle : Submodule.span (ZMod 2) (↑(J.image R) : Set Mat) ≤ free := by
        rw [Submodule.span_le]; rintro _ hmem
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hmem) with ⟨i, hiJ, rfl⟩
        exact hR_in_free i hiJ
      exact hle hYJ
    have hX_eq : X = (X - Y) + Y := (sub_add_cancel X Y).symm
    rw [hX_eq]
    exact Submodule.add_mem_sup hXY_W hY_free
  have hL_rk2 : W ⊔ free = Submodule.span (ZMod 2) {X : Mat | X ∈ W ⊔ free ∧ X.rank ≤ 2} := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · refine hW_le.trans ?_
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨hVR_le (Submodule.subset_span ⟨i, rfl⟩), hR_rk i⟩
      · rw [Submodule.span_le]
        intro Z hZ
        have hexp : Z = ∑ j0 : Fin d, Matrix.of (fun i j => if j = j0 then Z i j0 else 0) := by
          ext i j; simp only [Matrix.sum_apply, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
          · intro j0 _ hne; simp [hne.symm]
          · intro h; exact absurd (Finset.mem_univ j) h
        rw [hexp]
        refine Submodule.sum_mem _ fun j0 _ => Submodule.subset_span ⟨?_, le_trans (rank_le_one_of_col_vec (fun i => Z i j0) j0) (by omega)⟩
        apply Submodule.mem_sup_right
        apply Submodule.subset_span
        intro j
        by_cases hj : j = j0
        · subst hj; simpa only [Matrix.of_apply, ↓reduceIte] using hZ j
        · simp only [Matrix.of_apply, if_neg hj]; exact E.zero_mem
    · rw [Submodule.span_le]; rintro X ⟨hX, _⟩; exact hX
  have hfits_val : fits (2 * (t - D)) := ⟨E, hfrE, hL_rk2⟩
  have hbound := (hfits (2 * (t - D))).mp hfits_val
  rw [if_neg (by omega)] at hbound
  exact hbound

private lemma main_proof :
let F := ZMod 2
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let S : Set Mat := {X | ∃ H : Mat, alt H ∧ X = U*H*U.transpose + H}
  let W := Submodule.span F S
  let fits := fun (e : ℕ) =>
    ∃ E : Submodule F (Fin d → F), Module.finrank F E ≤ e ∧
      let free := Submodule.span F {X : Mat | ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span F {X : Mat | X ∈ L ∧ X.rank ≤ 2}
  let D := r*(d-r-1)
  (∀ e : ℕ, fits e ↔ (if r ≤ 1 then 0 else r) ≤ e) ∧
    ∀ (t : ℕ) (R : Fin t → Mat), (∀ i, (R i).rank ≤ 2) →
      W ≤ Submodule.span F (Set.range R) →
      D ≤ t ∧ (2 ≤ r → r ≤ 2*(t-D)) := by
  intro F d U hU Mat alt r S W fits D
  rcases exists_jordan_basis U hU with ⟨h2r, P, Pinv, hPP, hPP', hPU⟩
  let Φ : Mat ≃ₗ[ZMod 2] Mat :=
    { toFun := fun X => P * X * P.transpose,
      invFun := fun Y => Pinv * Y * Pinv.transpose,
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul],
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul],
      left_inv := fun X => by
        have ht : P.transpose * Pinv.transpose = 1 := by rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
        calc Pinv * (P * X * P.transpose) * Pinv.transpose
            = (Pinv * P) * (X * (P.transpose * Pinv.transpose)) := by simp only [mul_assoc]
          _ = X := by rw [hPP', ht, mul_one, one_mul]
      right_inv := fun Y => by
        have ht : Pinv.transpose * P.transpose = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
        calc P * (Pinv * Y * Pinv.transpose) * P.transpose
            = (P * Pinv) * (Y * (Pinv.transpose * P.transpose)) := by simp only [mul_assoc]
          _ = Y := by rw [hPP, ht, mul_one, one_mul] }
  have hΦ_rank : ∀ X : Mat, (Φ X).rank = X.rank := fun X => matrix_rank_congr P Pinv X hPP hPP'
  have hΦ_W : W.map Φ.toLinearMap = canonWSub d r h2r := by
    rw [← canonW_eq_sub h2r]
    dsimp only [W]
    rw [Submodule.map_span]
    congr 1; ext Y
    simp only [Set.mem_image, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨X, ⟨H, hH, rfl⟩, rfl⟩
      refine ⟨Φ H, alt_congr P H hH, ?_⟩
      change P * (U * H * U.transpose + H) * P.transpose =
        canonU d r * (P * H * P.transpose) * (canonU d r).transpose + (P * H * P.transpose)
      have ht' : P.transpose * Pinv.transpose = 1 := by rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
      have h1 : canonU d r * (P * H * P.transpose) * (canonU d r).transpose = P * (U * H * U.transpose) * P.transpose := by
        rw [← hPU, Matrix.transpose_mul, Matrix.transpose_mul]
        calc P * U * Pinv * (P * H * P.transpose) * (Pinv.transpose * (U.transpose * P.transpose))
            = P * (U * ((Pinv * P) * (H * ((P.transpose * Pinv.transpose) * (U.transpose * P.transpose))))) := by simp only [mul_assoc]
          _ = P * (U * H * U.transpose) * P.transpose := by rw [hPP', ht']; simp only [one_mul, mul_assoc]
      rw [h1, Matrix.mul_add, Matrix.add_mul]
    · rintro ⟨H', hH', rfl⟩
      refine ⟨U * Φ.symm H' * U.transpose + Φ.symm H', ⟨Φ.symm H', alt_congr Pinv H' hH', rfl⟩, ?_⟩
      have h1 : Φ (U * Φ.symm H' * U.transpose) = canonU d r * H' * (canonU d r).transpose := by
        change P * (U * (Pinv * H' * Pinv.transpose) * U.transpose) * P.transpose =
          canonU d r * H' * (canonU d r).transpose
        rw [← hPU, Matrix.transpose_mul, Matrix.transpose_mul]
        simp only [mul_assoc]
      rw [map_add, h1, Φ.apply_symm_apply]
  let P_equiv : (Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := P.mulVec, invFun := Pinv.mulVec,
      map_add' := Matrix.mulVec_add P, map_smul' := fun c v => Matrix.mulVec_smul P c v,
      left_inv := fun v => by rw [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec],
      right_inv := fun v => by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec] }
  have hΦ_free : ∀ E : Submodule (ZMod 2) (Fin d → ZMod 2),
      (Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
        Submodule.span (ZMod 2) {Y : Mat | ∀ j, (fun i => Y i j) ∈ E.map P_equiv.toLinearMap} := by
    intro E
    rw [Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨X, hXE, rfl⟩
      apply Submodule.subset_span
      intro j
      have hcol : (fun i => (P * X * P.transpose) i j) =
          ∑ k : Fin d, P j k • P_equiv (fun i => X i k) := by
        funext i
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, P_equiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun k _ => mul_comm _ _
      change (fun i => (P * X * P.transpose) i j) ∈ E.map P_equiv.toLinearMap
      rw [hcol]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.mem_map.mpr ⟨fun i => X i k, hXE k, rfl⟩)
    · rw [Submodule.span_le]
      intro Y hYE
      apply Submodule.subset_span
      refine ⟨Φ.symm Y, ?_, Φ.apply_symm_apply Y⟩
      intro j
      have hcol : (fun i => (Pinv * Y * Pinv.transpose) i j) =
          ∑ k : Fin d, Pinv j k • P_equiv.symm (fun i => Y i k) := by
        funext i
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, P_equiv, LinearEquiv.coe_symm_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun k _ => mul_comm _ _
      change (fun i => (Pinv * Y * Pinv.transpose) i j) ∈ E
      rw [hcol]
      refine Submodule.sum_mem E fun k _ => Submodule.smul_mem E _ ?_
      rcases Submodule.mem_map.mp (hYE k) with ⟨u, huE, hu_eq⟩
      have : P_equiv.symm (fun i => Y i k) = u := by rw [← hu_eq]; exact P_equiv.symm_apply_apply u
      rwa [this]
  have hmain := canon_main h2r
  have hfits_iff : ∀ e : ℕ, fits e ↔
      ∃ E' : Submodule (ZMod 2) (Fin d → ZMod 2), Module.finrank (ZMod 2) E' ≤ e ∧
        let free' := Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E'}
        let L' := canonWSub d r h2r ⊔ free'
        L' = Submodule.span (ZMod 2) {X : Mat | X ∈ L' ∧ X.rank ≤ 2} := by
    intro e
    constructor
    · rintro ⟨E, hEe, hLeq⟩
      refine ⟨E.map P_equiv.toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact hEe, ?_⟩
      have hmap := congrArg (Submodule.map Φ.toLinearMap) hLeq
      rw [Submodule.map_sup, hΦ_W, hΦ_free E, Submodule.map_span] at hmap
      convert hmap using 2
      ext Y; simp only [Set.mem_image, Set.mem_setOf_eq, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨hYL', hYrk⟩
        refine ⟨Φ.symm Y, ⟨?_, by rw [← hΦ_rank, Φ.apply_symm_apply]; exact hYrk⟩, Φ.apply_symm_apply Y⟩
        have hsup_eq : (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
            canonWSub d r h2r ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E.map P_equiv.toLinearMap} := by
          rw [Submodule.map_sup, hΦ_W, hΦ_free E]
        rw [← hsup_eq] at hYL'
        rcases Submodule.mem_map.mp hYL' with ⟨X, hXL, rfl⟩
        change Φ.symm (Φ X) ∈ _
        rwa [Φ.symm_apply_apply]
      · rintro ⟨X, ⟨hXL, hXrk⟩, rfl⟩
        refine ⟨?_, by rw [hΦ_rank]; exact hXrk⟩
        have hsup_eq : (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
            canonWSub d r h2r ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E.map P_equiv.toLinearMap} := by
          rw [Submodule.map_sup, hΦ_W, hΦ_free E]
        rw [← hsup_eq]; exact Submodule.mem_map.mpr ⟨X, hXL, rfl⟩
    · rintro ⟨E', hEe, hLeq⟩
      let E := E'.map P_equiv.symm.toLinearMap
      have hE_map : E.map P_equiv.toLinearMap = E' := by
        dsimp only [E]; rw [← Submodule.map_comp]
        have : P_equiv.toLinearMap.comp P_equiv.symm.toLinearMap = LinearMap.id := by
          apply LinearMap.ext; intro x; exact P_equiv.apply_symm_apply x
        rw [this, Submodule.map_id]
      refine ⟨E, by dsimp only [E]; rw [LinearEquiv.finrank_map_eq]; exact hEe, ?_⟩
      have hmap_eq : (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
          (Submodule.span (ZMod 2) {X : Mat | X ∈ W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E} ∧ X.rank ≤ 2}).map Φ.toLinearMap := by
        rw [Submodule.map_sup, hΦ_W, hΦ_free E, hE_map, Submodule.map_span]
        convert hLeq using 2
        ext Y; simp only [Set.mem_image, Set.mem_setOf_eq, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨X, ⟨hXL, hXrk⟩, rfl⟩
          refine ⟨?_, by rw [hΦ_rank]; exact hXrk⟩
          have hsup_eq : (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
              canonWSub d r h2r ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E'} := by
            rw [Submodule.map_sup, hΦ_W, hΦ_free E, hE_map]
          rw [← hsup_eq]; exact Submodule.mem_map.mpr ⟨X, hXL, rfl⟩
        · rintro ⟨hYL', hYrk⟩
          refine ⟨Φ.symm Y, ⟨?_, by rw [← hΦ_rank, Φ.apply_symm_apply]; exact hYrk⟩, Φ.apply_symm_apply Y⟩
          have hsup_eq : (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap =
              canonWSub d r h2r ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E'} := by
            rw [Submodule.map_sup, hΦ_W, hΦ_free E, hE_map]
          rw [← hsup_eq] at hYL'
          rcases Submodule.mem_map.mp hYL' with ⟨X, hXL, rfl⟩
          change Φ.symm (Φ X) ∈ _
          rwa [Φ.symm_apply_apply]
      ext X
      constructor
      · intro hX
        have hY : Φ X ∈ (Submodule.span (ZMod 2) {X : Mat | X ∈ W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E} ∧ X.rank ≤ 2}).map Φ.toLinearMap := by
          rw [← hmap_eq]; exact Submodule.mem_map.mpr ⟨X, hX, rfl⟩
        rcases Submodule.mem_map.mp hY with ⟨X', hX', hEq⟩
        rwa [← Φ.injective hEq]
      · intro hX
        have hY : Φ X ∈ (W ⊔ Submodule.span (ZMod 2) {X : Mat | ∀ j, (fun i => X i j) ∈ E}).map Φ.toLinearMap := by
          rw [hmap_eq]; exact Submodule.mem_map.mpr ⟨X, hX, rfl⟩
        rcases Submodule.mem_map.mp hY with ⟨X', hX', hEq⟩
        rwa [← Φ.injective hEq]
  refine ⟨fun e => (hfits_iff e).trans (hmain.1 e), ?_⟩
  intro t R hR_rk hW_le
  refine hmain.2 t (fun i => Φ (R i)) (fun i => by rw [hΦ_rank]; exact hR_rk i) ?_
  have h1 : canonWSub d r h2r ≤ (Submodule.span F (Set.range R)).map Φ.toLinearMap := by
    rw [← hΦ_W]; exact Submodule.map_mono hW_le
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact h1

end PEqualNP.Outside.L_lib_949_aux

open PEqualNP.Outside.L_lib_949_aux in
theorem PEqualNP.Outside.L_lib_949 :
let F := ZMod 2
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let S : Set Mat := {X | ∃ H : Mat, alt H ∧ X = U*H*U.transpose + H}
  let W := Submodule.span F S
  let fits := fun (e : ℕ) =>
    ∃ E : Submodule F (Fin d → F), Module.finrank F E ≤ e ∧
      let free := Submodule.span F {X : Mat | ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span F {X : Mat | X ∈ L ∧ X.rank ≤ 2}
  let D := r*(d-r-1)
  (∀ e : ℕ, fits e ↔ (if r ≤ 1 then 0 else r) ≤ e) ∧
    ∀ (t : ℕ) (R : Fin t → Mat), (∀ i, (R i).rank ≤ 2) →
      W ≤ Submodule.span F (Set.range R) →
      D ≤ t ∧ (2 ≤ r → r ≤ 2*(t-D)) :=
  main_proof
