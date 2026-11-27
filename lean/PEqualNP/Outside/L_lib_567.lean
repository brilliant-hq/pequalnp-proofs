import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_567 : (∀ (n k : ℕ) (m : Fin k → ℕ) (v : (j : Fin k) → Fin (m j) → Fin n → ℝ) (w : Fin k → ℝ),
  (∀ j, 0 < m j) →
  let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
  (∀ j, 0 ≤ w j) →
  (∀ j a b, dot (v j a) (v j b) = if a = b then 1 else 0) →
  (∀ x, (∑ j, w j * (∑ a, (dot x (v j a))^2)) = dot x x) →
  (∀ j, w j ≤ 1) ∧
    ∀ i j, i ≠ j → w i = 1 → 0 < w j → ∀ a b, dot (v i a) (v j b) = 0) := by
  intro n k m v w hm dot hw horth hparse
  have hnonneg : ∀ (x : Fin n → ℝ) (r : Fin k), 0 ≤ w r * (∑ c, (dot x (v r c)) ^ 2) := by
    intro x r
    exact mul_nonneg (hw r) (Finset.sum_nonneg (fun c _ => sq_nonneg _))
  have hinner : ∀ (r : Fin k) (a : Fin (m r)), (∑ c, (dot (v r a) (v r c)) ^ 2) = 1 := by
    intro r a
    rw [Finset.sum_eq_single a]
    · simp [horth r a a]
    · intro c _ hc
      simp [horth r a c, Ne.symm hc]
    · intro h; exact False.elim (h (Finset.mem_univ a))
  constructor
  · intro j
    let a0 : Fin (m j) := ⟨0, hm j⟩
    have hle := Finset.single_le_sum (fun r _ => hnonneg (v j a0) r) (Finset.mem_univ j)
    rw [hparse (v j a0), hinner j a0, horth j a0 a0] at hle
    simpa using hle
  · intro i j hij hwi hwj a b
    let f : Fin k → ℝ := fun r => w r * (∑ c, (dot (v i a) (v r c)) ^ 2)
    have hle2 : f i + f j ≤ ∑ r : Fin k, f r := by
      calc f i + f j = ∑ r ∈ ({i, j} : Finset (Fin k)), f r := (Finset.sum_pair hij).symm
        _ ≤ ∑ r ∈ Finset.univ, f r :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun r _ _ => hnonneg (v i a) r)
    have hsum : (∑ r : Fin k, f r) = 1 := by
      have hp := hparse (v i a)
      rw [horth i a a] at hp
      simpa [f] using hp
    have hfi : f i = 1 := by
      dsimp only [f]
      rw [hwi, hinner i a, mul_one]
    have hfj_le : f j ≤ 0 := by linarith
    have hsq_le : (dot (v i a) (v j b)) ^ 2 ≤ ∑ c, (dot (v i a) (v j c)) ^ 2 :=
      Finset.single_le_sum (fun c _ => sq_nonneg (dot (v i a) (v j c))) (Finset.mem_univ b)
    have hmul_le : w j * (dot (v i a) (v j b)) ^ 2 ≤ 0 := by
      have h1 : w j * (dot (v i a) (v j b)) ^ 2 ≤ f j :=
        mul_le_mul_of_nonneg_left hsq_le (le_of_lt hwj)
      linarith
    have hsq0 : (dot (v i a) (v j b)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (dot (v i a) (v j b))]
    exact sq_eq_zero_iff.mp hsq0
