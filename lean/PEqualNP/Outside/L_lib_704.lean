import Mathlib

open scoped BigOperators Kronecker

namespace PEqualNP.Outside.L_lib_704

private theorem sylvesterExact (h : ℕ) :
    ∃ H : Matrix (Fin (2 ^ h)) (Fin (2 ^ h)) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 1) ∧
        H.det ^ 2 = ((2 ^ h : ℕ) : ℝ) ^ (2 ^ h : ℕ) := by
  induction h with
  | zero =>
      let H : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
      refine ⟨H, fun _ _ => Or.inr rfl, ?_⟩
      have hdet : H.det = 1 := Matrix.det_fin_one H
      norm_num [hdet]
  | succ h ih =>
      obtain ⟨H, hsign, hdet⟩ := ih
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]
      have hAs (i j : Fin 2) : A i j = -1 ∨ A i j = 1 := by
        fin_cases i <;> fin_cases j <;> simp [A]
      have hA : A.det ^ 2 = (2 : ℝ) ^ 2 := by
        norm_num [A, Matrix.det_fin_two_of]
      let e : Fin (2 ^ h) × Fin 2 ≃ Fin (2 ^ (h + 1)) :=
        finProdFinEquiv.trans (finCongr (pow_succ (2 : ℕ) h).symm)
      refine ⟨Matrix.reindex e e (H ⊗ₖ A), ?_, ?_⟩
      · intro i j
        have hentry (p q : Fin (2 ^ h) × Fin 2) :
            (H ⊗ₖ A) p q = -1 ∨ (H ⊗ₖ A) p q = 1 := by
          rcases p with ⟨p, r⟩
          rcases q with ⟨q, s⟩
          simp only [Matrix.kronecker_apply]
          rcases hsign p q with hp | hp <;> rcases hAs r s with hr | hr <;> norm_num [hp, hr]
        exact hentry (e.symm i) (e.symm j)
      · have hApow : (A.det ^ (2 ^ h : ℕ)) ^ 2 = (2 : ℝ) ^ (2 ^ h * 2 : ℕ) := by
          calc
            (A.det ^ (2 ^ h : ℕ)) ^ 2 = (A.det ^ 2) ^ (2 ^ h : ℕ) := by
              simp only [← pow_mul, Nat.mul_comm (2 ^ h) 2]
            _ = (2 : ℝ) ^ (2 ^ h * 2 : ℕ) := by
              rw [hA, ← pow_mul, Nat.mul_comm 2 (2 ^ h)]
        rw [Matrix.det_reindex_self, Matrix.det_kronecker, Fintype.card_fin 2,
          Fintype.card_fin (2 ^ h), mul_pow, hdet, hApow, ← pow_mul]
        simp only [pow_succ (2 : ℕ) h, Nat.cast_mul, Nat.cast_ofNat, mul_pow]

-- The sequence x^j / j! increases up to j = x and decreases thereafter.
private theorem pow_div_factorial_le_diagonal (x k : ℕ) :
    (x : ℝ) ^ k / (k.factorial : ℝ) ≤ (x : ℝ) ^ x / (x.factorial : ℝ) := by
  let f (j : ℕ) : ℝ := (x : ℝ) ^ j / (j.factorial : ℝ)
  change f k ≤ f x
  have hf (j : ℕ) : 0 ≤ f j := by
    dsimp only [f]
    positivity
  have hs (j : ℕ) : f (j + 1) = ((x : ℝ) / ((j + 1 : ℕ) : ℝ)) * f j := by
    dsimp only [f]
    rw [pow_succ', Nat.factorial_succ, Nat.cast_mul, div_mul_div_comm]
  rcases le_total k x with hkx | hxk
  · refine Nat.decreasingInduction (motive := fun j _ => f j ≤ f x) ?_ le_rfl hkx
    intro j hj ih
    refine le_trans ?_ ih
    rw [hs]
    -- Compare the multiplier x / (j + 1) with one.
    have hratio : 1 ≤ (x : ℝ) / ((j + 1 : ℕ) : ℝ) :=
      (one_le_div₀ (by positivity)).2 (Nat.cast_le.mpr (Nat.succ_le_of_lt hj))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (hf j)
  · refine Nat.le_induction (motive := fun j _ => f j ≤ f x) le_rfl ?_ k hxk
    intro j hj ih
    refine le_trans ?_ ih
    rw [hs]
    have hratio : (x : ℝ) / ((j + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one₀ (by positivity)).2 (Nat.cast_le.mpr (Nat.le_succ_of_le hj))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (hf j)

private theorem add_pow_div_factorial_le (a b : ℕ) :
    ((a + b : ℕ) : ℝ) ^ (a + b) / ((a + b).factorial : ℝ) ≤
      ((a + b + 1 : ℕ) : ℝ) * ((a : ℝ) ^ a / (a.factorial : ℝ)) *
        ((b : ℝ) ^ b / (b.factorial : ℝ)) := by
  let n := a + b
  change (n : ℝ) ^ n / (n.factorial : ℝ) ≤
    ((n + 1 : ℕ) : ℝ) * ((a : ℝ) ^ a / (a.factorial : ℝ)) *
      ((b : ℝ) ^ b / (b.factorial : ℝ))
  rw [show (n : ℝ) = (a : ℝ) + (b : ℝ) from Nat.cast_add a b, add_pow, Finset.sum_div]
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1),
        ((a : ℝ) ^ a / (a.factorial : ℝ)) * ((b : ℝ) ^ b / (b.factorial : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hchoose : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
          (n.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
      have hden : (n.factorial : ℝ) =
          (k.factorial : ℝ) * ((n - k).factorial : ℝ) * (n.choose k : ℝ) := by
        rw [← hchoose]
        ac_rfl
      have hc : (n.choose k : ℝ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero hkn
      calc
        _ = ((a : ℝ) ^ k / (k.factorial : ℝ)) *
              ((b : ℝ) ^ (n - k) / ((n - k).factorial : ℝ)) := by
          rw [hden, mul_div_mul_right _ _ hc, div_mul_div_comm]
        _ ≤ _ := mul_le_mul (pow_div_factorial_le_diagonal a k)
          (pow_div_factorial_le_diagonal b (n - k)) (by positivity) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

private def squarePerm {n : Type*} [DecidableEq n] [Fintype n] (H : Matrix n n ℝ) : ℝ :=
  Matrix.permanent (fun i j => (H i j)^2)

private lemma permanent_submatrix_equiv {i j : Type*} [Fintype i] [Fintype j]
    [DecidableEq i] [DecidableEq j] (e : i ≃ j) (A : Matrix j j ℝ) :
    (A.submatrix e e).permanent = A.permanent := by
  simp only [Matrix.permanent]
  apply Fintype.sum_equiv e.permCongr
  intro σ
  apply Fintype.prod_equiv e
  intro x
  simp

private lemma permanent_blocks {i j : Type*} [DecidableEq i] [DecidableEq j]
    [Fintype i] [Fintype j] (A : Matrix i i ℝ) (B : Matrix j j ℝ) :
    (Matrix.fromBlocks A 0 0 B).permanent = A.permanent * B.permanent := by
  classical
  let S := ((Equiv.Perm.sumCongrHom i j).range : Set (Equiv.Perm (i ⊕ j))).toFinset
  let f (σ : Equiv.Perm (i ⊕ j)) := ∏ x, (Matrix.fromBlocks A 0 0 B) (σ x) x
  change ∑ σ, f σ = _
  calc
    ∑ σ, f σ = ∑ σ ∈ S, f σ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro σ _ hσ
      have hn : ¬∀ x : i, ∃ y : i, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσ
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσ
      push Not at hn
      obtain ⟨x, hx⟩ := hn
      cases h : σ (Sum.inl x) with
      | inl y => exact (hx y h.symm).elim
      | inr y =>
        unfold f
        exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl x)) (by simp [h])
    _ = A.permanent * B.permanent := by
      symm
      simp only [Matrix.permanent, Finset.sum_mul_sum, ← Finset.sum_product',
        Finset.univ_product_univ]
      refine Finset.sum_nbij (fun σ : Equiv.Perm i × Equiv.Perm j => σ.1.sumCongr σ.2)
        ?_ ?_ ?_ ?_
      · intro σ _
        exact Set.mem_toFinset.mpr ⟨σ, rfl⟩
      · intro σ _ τ _ h
        exact Equiv.Perm.sumCongrHom_injective h
      · intro σ hσ
        obtain ⟨τ, rfl⟩ := Set.mem_toFinset.mp hσ
        exact ⟨τ, Finset.mem_univ _, rfl⟩
      · rintro ⟨σ, τ⟩ _
        simp [f, Fintype.prod_sum_type, Equiv.sumCongr_apply]

private lemma block_witness {a b n : ℕ} (h : a + b = n)
    (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin b) (Fin b) ℝ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hB : ∀ i j, B i j = -1 ∨ B i j = 0 ∨ B i j = 1) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧
      squarePerm H = squarePerm A * squarePerm B ∧ H.det^2 = A.det^2 * B.det^2 := by
  let C := Matrix.fromBlocks A 0 0 B
  let e : Fin n ≃ Fin a ⊕ Fin b := (finCongr h.symm).trans finSumFinEquiv.symm
  refine ⟨C.submatrix e e, ?_, ?_, ?_⟩
  · intro i j
    change C (e i) (e j) = -1 ∨ C (e i) (e j) = 0 ∨ C (e i) (e j) = 1
    rcases e i with i' | i' <;> rcases e j with j' | j' <;>
      simp only [C, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    · exact hA _ _
    · exact Or.inr (Or.inl trivial)
    · exact Or.inr (Or.inl trivial)
    · exact hB _ _
  · let A₂ : Matrix (Fin a) (Fin a) ℝ := fun i j => A i j ^ 2
    let B₂ : Matrix (Fin b) (Fin b) ℝ := fun i j => B i j ^ 2
    let C₂ : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ := fun i j => C i j ^ 2
    have hs : C₂ = Matrix.fromBlocks A₂ 0 0 B₂ := by
      ext (i | i) (j | j) <;> simp [A₂, B₂, C₂, C, Matrix.fromBlocks]
    change (C₂.submatrix e e).permanent = A₂.permanent * B₂.permanent
    calc
      _ = C₂.permanent := permanent_submatrix_equiv e C₂
      _ = _ := by rw [hs, permanent_blocks]
  · rw [Matrix.det_submatrix_equiv_self]
    simp only [C, Matrix.det_fromBlocks_zero₂₁, mul_pow]

private lemma squarePerm_of_signs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, H i j = -1 ∨ H i j = 1) : squarePerm H = (n.factorial : ℝ) := by
  have hs (i j : Fin n) : (H i j)^2 = 1 := by
    rcases hH i j with h | h <;> rw [h] <;> norm_num
  simp [squarePerm, Matrix.permanent, hs, Fintype.card_perm]

private noncomputable def q (n : ℕ) : ℝ := (n : ℝ)^n / (n.factorial : ℝ)

private lemma largest_power_bounds {n : ℕ} (hn : 0 < n) :
    let d := 2^(Nat.log2 n)
    d ≤ n ∧ n - d < d := by
  dsimp only
  have hl := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hu := (Nat.log_lt_iff_lt_pow (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt hn)).mp
    (Nat.lt_succ_self (Nat.log 2 n))
  rw [pow_succ] at hu
  rw [Nat.log2_eq_log_two]
  refine ⟨hl, ?_⟩
  omega

private lemma assemble
    (hsyl : ∀ h : ℕ, ∃ H : Matrix (Fin (2^h)) (Fin (2^h)) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 1) ∧ H.det^2 = ((2^h : ℕ) : ℝ)^(2^h))
    (hbin : ∀ a b : ℕ, 0 < a → 0 < b →
      q (a+b) ≤ ((a+b+1 : ℕ) : ℝ) * q a * q b) :
    ∀ n : ℕ, 0 < n → ∃ H : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧ 0 < squarePerm H ∧
      q n ≤ (((n+1 : ℕ) : ℝ)^(Nat.log2 n+1)) * (H.det^2 / squarePerm H) ∧
      (∀ h : ℕ, n = 2^h → q n = H.det^2 / squarePerm H) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases he : ∃ h : ℕ, n = 2^h
    · obtain ⟨h, rfl⟩ := he
      obtain ⟨H, hH, hd⟩ := hsyl h
      have hp := squarePerm_of_signs H hH
      have hrate : H.det^2 / squarePerm H = q (2^h) := by rw [hd, hp, q]
      refine ⟨H, fun i j => (hH i j).imp_right Or.inr, ?_, ?_, fun _ _ => hrate.symm⟩
      · rw [hp]
        positivity
      · rw [hrate]
        exact le_mul_of_one_le_left (by unfold q; positivity)
          (one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2^h))))
    · let d := 2 ^ Nat.log2 n
      let m := n - d
      obtain ⟨hd, hm⟩ : d ≤ n ∧ m < d := largest_power_bounds hn
      have hdpos : 0 < d := by unfold d; positivity
      have hne : d ≠ n := fun h => he ⟨Nat.log2 n, h.symm⟩
      have hmpos : 0 < m := by unfold m; omega
      have hmn : m < n := lt_of_lt_of_le hm hd
      have hn' : d + m = n := Nat.add_sub_of_le hd
      have hlog : Nat.log2 m < Nat.log2 n := by
        rw [Nat.log2_eq_log_two (n := m)]
        exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hmpos) hm
      obtain ⟨A, hA, hAd⟩ := hsyl (Nat.log2 n)
      obtain ⟨B, hB, hBp, hBq, _⟩ := ih m hmn hmpos
      have hAp := squarePerm_of_signs A hA
      have hAr : A.det^2 / squarePerm A = q d := by rw [hAd, hAp, q]
      obtain ⟨H, hH, hp, hdet⟩ := block_witness hn' A B (fun i j => (hA i j).imp_right Or.inr) hB
      have hrate : H.det^2 / squarePerm H = q d * (B.det^2 / squarePerm B) := by
        rw [hp, hdet, mul_div_mul_comm, hAr]
      have hq : 0 ≤ q d := by unfold q; positivity
      have hrB : 0 ≤ B.det^2 / squarePerm B := by positivity
      have hbase : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      have hpow : ((m+1 : ℕ) : ℝ)^(Nat.log2 m+1) ≤ ((n+1 : ℕ) : ℝ)^(Nat.log2 n) :=
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.succ_le_succ hmn.le)) _).trans
          (pow_le_pow_right₀ hbase (by omega))
      refine ⟨H, hH, ?_, ?_, fun h hh => (he ⟨h, hh⟩).elim⟩
      · rw [hp, hAp]
        positivity
      · rw [hrate]
        calc
          q n ≤ ((n+1 : ℕ) : ℝ) * q d * q m := by simpa only [hn'] using hbin d m hdpos hmpos
          _ ≤ ((n+1 : ℕ) : ℝ) * q d * (((m+1 : ℕ) : ℝ)^(Nat.log2 m+1) * (B.det^2 / squarePerm B)) :=
            mul_le_mul_of_nonneg_left hBq (mul_nonneg (by positivity) hq)
          _ ≤ ((n+1 : ℕ) : ℝ) * q d * (((n+1 : ℕ) : ℝ)^(Nat.log2 n) * (B.det^2 / squarePerm B)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hrB) (mul_nonneg (by positivity) hq)
          _ = ((n+1 : ℕ) : ℝ)^(Nat.log2 n+1) * (q d * (B.det^2 / squarePerm B)) := by
            rw [pow_succ ((n+1 : ℕ) : ℝ) (Nat.log2 n)]
            ring

end PEqualNP.Outside.L_lib_704

theorem PEqualNP.Outside.L_lib_704 :
    ∀ n : ℕ, 0 < n →
      let I := Fin n
      let P := fun H : Matrix I I ℝ => Matrix.permanent (fun i j => (H i j)^2)
      let penalty := (n+1)^(Nat.log2 n+1)
      ∃ H : Matrix I I ℝ,
        (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧ 0 < P H ∧
        (n : ℝ)^n * P H ≤ (penalty : ℝ) * (n.factorial : ℝ) * H.det^2 ∧
        (∀ h : ℕ, n = 2^h → (n : ℝ)^n * P H = (n.factorial : ℝ) * H.det^2) := by
  intro n hn
  obtain ⟨H, hH, hp, hle, he⟩ := PEqualNP.Outside.L_lib_704.assemble
    PEqualNP.Outside.L_lib_704.sylvesterExact (fun a b _ _ =>
      PEqualNP.Outside.L_lib_704.add_pow_div_factorial_le a b) n hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  refine ⟨H, hH, hp, ?_, ?_⟩
  · change (n : ℝ)^n * PEqualNP.Outside.L_lib_704.squarePerm H ≤
      (((n+1)^(Nat.log2 n+1) : ℕ) : ℝ) * (n.factorial : ℝ) * H.det^2
    have hle' : (n : ℝ)^n / (n.factorial : ℝ) ≤
        ((n+1 : ℕ) : ℝ)^(Nat.log2 n+1) * H.det^2 / PEqualNP.Outside.L_lib_704.squarePerm H := by
      simpa only [PEqualNP.Outside.L_lib_704.q, mul_div_assoc] using hle
    rw [Nat.cast_pow]
    exact ((div_le_div_iff₀ hf hp).mp hle').trans_eq (mul_right_comm _ _ _)
  · intro h hh
    change (n : ℝ)^n * PEqualNP.Outside.L_lib_704.squarePerm H = (n.factorial : ℝ) * H.det^2
    rw [mul_comm (n.factorial : ℝ)]
    exact (div_eq_div_iff hf.ne' hp.ne').mp (he h hh)
