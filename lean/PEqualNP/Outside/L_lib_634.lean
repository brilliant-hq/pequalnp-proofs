import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_634_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

lemma z2_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases z2_zero_or_one a with rfl | rfl <;> decide

lemma z2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rcases z2_zero_or_one a with rfl | rfl <;> rcases z2_zero_or_one b with rfl | rfl <;> simp_all

lemma card_filter_add_card_filter_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun a => ¬ p a)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun a => ¬ p a)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : s.filter p ∪ s.filter (fun a => ¬ p a) = s := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hp : p a <;> simp [hp]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

lemma sum_z2 {α : Type*} [AddCommMonoid α] (f : ZMod 2 → α) :
    ∑ x : ZMod 2, f x = f 0 + f 1 := by
  change ∑ x : Fin 2, f x = f (0 : Fin 2) + f (1 : Fin 2)
  exact Fin.sum_univ_two f

lemma xor_eq_xor_imp {a b c d : Bool} (h : xor a b = xor c d) :
    a = xor (xor c b) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma decide_ne_xor (a1 a2 q1 q2 r d : Bool) :
    decide (xor a1 a2 ≠ xor q1 q2) =
      xor (decide (a1 ≠ xor (xor q1 r) d)) (decide (a2 ≠ xor (xor q2 r) d)) := by
  cases a1 <;> cases a2 <;> cases q1 <;> cases q2 <;> cases r <;> cases d <;> decide

lemma decide_ne_xor_col (a1 a2 q r1 r2 d : Bool) :
    decide (xor a1 a2 ≠ xor r1 r2) =
      xor (decide (a1 ≠ xor (xor q r1) d)) (decide (a2 ≠ xor (xor q r2) d)) := by
  cases a1 <;> cases a2 <;> cases q <;> cases r1 <;> cases r2 <;> cases d <;> decide

lemma xor_flip_cancel (q1 q2 r d : Bool) :
    xor (xor q1 r) d = xor (xor q1 q2) (xor (xor q2 r) d) := by
  cases q1 <;> cases q2 <;> cases r <;> cases d <;> decide

def b2z (b : Bool) : ZMod 2 :=
  if b = true then 1 else 0

def z2b (a : ZMod 2) : Bool :=
  decide (a = 1)

lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

lemma b2z_z2b (a : ZMod 2) : b2z (z2b a) = a := by
  rcases z2_zero_or_one a with rfl | rfl <;> decide

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma z2b_add (a b : ZMod 2) : z2b (a + b) = xor (z2b a) (z2b b) := by
  rcases z2_zero_or_one a with rfl | rfl <;> rcases z2_zero_or_one b with rfl | rfl <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp_all [b2z]

def pm (b : Bool) : ℝ :=
  if b = true then -1 else 1

def pmZ2 (a : ZMod 2) : ℝ :=
  if a = 1 then -1 else 1

lemma pm_eq_pmZ2 (b : Bool) : pm b = pmZ2 (b2z b) := by
  cases b <;> simp [pm, pmZ2, b2z]

lemma pmZ2_eq_pm (a : ZMod 2) : pmZ2 a = pm (z2b a) := by
  rcases z2_zero_or_one a with rfl | rfl <;> simp [pm, pmZ2, z2b]

lemma pm_sq (b : Bool) : pm b ^ 2 = 1 := by
  cases b <;> norm_num [pm]

lemma pmZ2_sq (a : ZMod 2) : pmZ2 a ^ 2 = 1 := by
  rcases z2_zero_or_one a with rfl | rfl <;> norm_num [pmZ2]

lemma pm_mul_self (b : Bool) : pm b * pm b = 1 := by
  cases b <;> norm_num [pm]

lemma pmZ2_add (a b : ZMod 2) : pmZ2 (a + b) = pmZ2 a * pmZ2 b := by
  rcases z2_zero_or_one a with rfl | rfl <;> rcases z2_zero_or_one b with rfl | rfl <;>
    simp [pmZ2, (by decide : (1 : ZMod 2) + 1 = 0)]

lemma pm_xor (a b : Bool) : pm (xor a b) = pm a * pm b := by
  rw [pm_eq_pmZ2, pm_eq_pmZ2, pm_eq_pmZ2, b2z_xor, pmZ2_add]

lemma pm_eq_pm_iff {a b : Bool} : pm a = pm b ↔ a = b := by
  cases a <;> cases b <;> norm_num [pm]

def chi {m : ℕ} (u w : Fin m → ZMod 2) : ℝ :=
  pmZ2 (∑ i : Fin m, u i * w i)

lemma chi_comm {m : ℕ} (u w : Fin m → ZMod 2) : chi u w = chi w u := by
  simp only [chi]
  congr 1
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma chi_add_left {m : ℕ} (u1 u2 w : Fin m → ZMod 2) :
    chi (u1 + u2) w = chi u1 w * chi u2 w := by
  simp only [chi, Pi.add_apply, add_mul, Finset.sum_add_distrib, pmZ2_add]

lemma chi_add_right {m : ℕ} (u w1 w2 : Fin m → ZMod 2) :
    chi u (w1 + w2) = chi u w1 * chi u w2 := by
  rw [chi_comm, chi_add_left, chi_comm w1 u, chi_comm w2 u]

lemma chi_zero_left {m : ℕ} (w : Fin m → ZMod 2) : chi 0 w = 1 := by
  simp [chi, pmZ2]

lemma chi_zero_right {m : ℕ} (u : Fin m → ZMod 2) : chi u 0 = 1 := by
  simp [chi, pmZ2]

lemma sum_chi {m : ℕ} (u : Fin m → ZMod 2) :
    ∑ w : Fin m → ZMod 2, chi u w = if u = 0 then (2 ^ m : ℝ) else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp only [↓reduceIte, chi_zero_left, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hu, ↓reduceIte]
    have hex : ∃ i0 : Fin m, u i0 = 1 := by
      by_contra hall
      apply hu
      ext i
      rcases z2_zero_or_one (u i) with h0 | h1
      · exact h0
      · exact False.elim (hall ⟨i, h1⟩)
    obtain ⟨i0, hi0⟩ := hex
    let F0 := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun w => w i0 = 0)
    let F1 := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun w => w i0 = 1)
    have hunion : (Finset.univ : Finset (Fin m → ZMod 2)) = F0 ∪ F1 := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, F0, F1]
      exact z2_zero_or_one (w i0)
    have hdisj : Disjoint F0 F1 := by
      rw [Finset.disjoint_left]
      intro w h0 h1
      have ha : w i0 = 0 := (Finset.mem_filter.mp h0).2
      have hb : w i0 = 1 := (Finset.mem_filter.mp h1).2
      rw [ha] at hb
      exact zero_ne_one hb
    have hneg : ∑ w ∈ F1, chi u w = -(∑ w ∈ F0, chi u w) := by
      rw [← Finset.sum_neg_distrib]
      symm
      refine Finset.sum_bij (fun w _ => Function.update w i0 1) ?_ ?_ ?_ ?_
      · intro w _
        simp [F1]
      · intro w1 hw1 w2 hw2 heq
        ext i
        by_cases hi : i = i0
        · subst hi
          have h1 : w1 i = 0 := (Finset.mem_filter.mp hw1).2
          have h2 : w2 i = 0 := (Finset.mem_filter.mp hw2).2
          exact h1.trans h2.symm
        · have := congrFun heq i
          simpa [Function.update_of_ne hi] using this
      · intro w hw
        refine ⟨Function.update w i0 0, by simp [F0], ?_⟩
        ext i
        by_cases hi : i = i0
        · subst hi
          have h1 : w i = 1 := (Finset.mem_filter.mp hw).2
          simp [h1]
        · simp [Function.update_of_ne hi]
      · intro w hw
        have hw0 : w i0 = 0 := (Finset.mem_filter.mp hw).2
        have hupd : Function.update w i0 1 = w + Pi.single i0 1 := by
          ext i
          by_cases hi : i = i0
          · subst hi; simp [hw0]
          · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
        rw [hupd, chi_add_right]
        have hsingle : chi u (Pi.single i0 1) = -1 := by
          simp only [chi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, hi0, pmZ2]
        rw [hsingle, mul_neg_one]
    rw [hunion, Finset.sum_union hdisj, hneg, add_neg_cancel]

lemma fourier_inv {m : ℕ} (f : (Fin m → ZMod 2) → ℝ) (d : Fin m → ZMod 2) :
    ∑ ω : Fin m → ZMod 2, (∑ x : Fin m → ZMod 2, f x * chi ω x) * chi ω d =
      (2 ^ m : ℝ) * f d := by
  trans ∑ ω : Fin m → ZMod 2, ∑ x : Fin m → ZMod 2, f x * (chi ω x * chi ω d)
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
  · rw [Finset.sum_comm]
    have hinner : ∀ x : Fin m → ZMod 2,
        ∑ ω : Fin m → ZMod 2, f x * (chi ω x * chi ω d) =
          if x = d then (2 ^ m : ℝ) * f d else 0 := by
      intro x
      rw [← Finset.mul_sum]
      have hchi : ∀ ω : Fin m → ZMod 2, chi ω x * chi ω d = chi (x + d) ω := by
        intro ω
        rw [← chi_add_right, chi_comm]
      simp_rw [hchi, sum_chi]
      have hiff : x + d = 0 ↔ x = d := by
        constructor
        · intro h
          ext i
          exact z2_eq_of_add_eq_zero (congrFun h i)
        · rintro rfl
          ext i
          exact z2_add_self _
      by_cases hxd : x = d
      · subst hxd
        simp [hiff, mul_comm]
      · simp [hxd, hiff]
    simp [hinner]

lemma fourier_parseval {m : ℕ} (f : (Fin m → ZMod 2) → ℝ) :
    ∑ ω : Fin m → ZMod 2, (∑ x : Fin m → ZMod 2, f x * chi ω x) ^ 2 =
      (2 ^ m : ℝ) * ∑ x : Fin m → ZMod 2, f x ^ 2 := by
  have hexp : ∀ ω : Fin m → ZMod 2,
      (∑ x : Fin m → ZMod 2, f x * chi ω x) ^ 2 =
        ∑ x : Fin m → ZMod 2, f x * ((∑ y : Fin m → ZMod 2, f y * chi ω y) * chi ω x) := by
    intro ω
    rw [sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, fourier_inv]
  ring

lemma hadamard_orth_rows {N : ℕ} {H : Fin N → Fin N → Bool}
    (hH : ∀ a b : Fin N, a ≠ b →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N)
    (a b : Fin N) :
    ∑ v : Fin N, pm (H a v) * pm (H b v) = if a = b then (N : ℝ) else 0 := by
  by_cases hab : a = b
  · subst hab
    simp [pm_mul_self]
  · simp only [hab, ↓reduceIte]
    let diff := (Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)
    let same := (Finset.univ : Finset (Fin N)).filter (fun v => H a v = H b v)
    have hsplit : ∑ v : Fin N, pm (H a v) * pm (H b v) =
        ∑ v ∈ same, pm (H a v) * pm (H b v) + ∑ v ∈ diff, pm (H a v) * pm (H b v) := by
      have hunion : (Finset.univ : Finset (Fin N)) = same ∪ diff := by
        ext v
        simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, same, diff]
        exact eq_or_ne _ _
      have hdisj : Disjoint same diff := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      conv_lhs => rw [hunion]
      exact Finset.sum_union hdisj
    have hsame : ∑ v ∈ same, pm (H a v) * pm (H b v) = (same.card : ℝ) := by
      trans ∑ v ∈ same, (1 : ℝ)
      · refine Finset.sum_congr rfl fun v hv => ?_
        rw [(Finset.mem_filter.mp hv).2, pm_mul_self]
      · simp
    have hdiff : ∑ v ∈ diff, pm (H a v) * pm (H b v) = -(diff.card : ℝ) := by
      trans ∑ v ∈ diff, (-1 : ℝ)
      · refine Finset.sum_congr rfl fun v hv => ?_
        have hne : H a v ≠ H b v := (Finset.mem_filter.mp hv).2
        cases ha : H a v <;> cases hb : H b v <;> simp_all [pm]
      · simp
    have hcard_sum : same.card + diff.card = N := by
      have h1 := card_filter_add_card_filter_not (Finset.univ : Finset (Fin N))
        (fun v => H a v = H b v)
      simpa [same, diff] using h1
    have h2diff : 2 * diff.card = N := hH a b hab
    have hsame_eq : same.card = diff.card := by omega
    rw [hsplit, hsame, hdiff, hsame_eq, add_neg_cancel]

lemma hadamard_orth_cols {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool}
    (hH : ∀ a b : Fin N, a ≠ b →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N)
    (a b : Fin N) :
    ∑ u : Fin N, pm (H u a) * pm (H u b) = if a = b then (N : ℝ) else 0 := by
  let M : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => pm (H i j)
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hmul : M * ((N : ℝ)⁻¹ • M.transpose) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      M, Matrix.of_apply, Matrix.one_apply]
    have hpull : ∑ k : Fin N, pm (H i k) * ((N : ℝ)⁻¹ * pm (H j k)) =
        (N : ℝ)⁻¹ * ∑ k : Fin N, pm (H i k) * pm (H j k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hpull, hadamard_orth_rows hH i j]
    split_ifs <;> simp [hNne]
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr fun h0 => by
    have h1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hmul2 : ((N : ℝ)⁻¹ • M.transpose) * M = 1 := by
    have hinv : (N : ℝ)⁻¹ • M.transpose = M⁻¹ := by
      calc (N : ℝ)⁻¹ • M.transpose = 1 * ((N : ℝ)⁻¹ • M.transpose) := (Matrix.one_mul _).symm
        _ = (M⁻¹ * M) * ((N : ℝ)⁻¹ • M.transpose) := by rw [Matrix.nonsing_inv_mul M hdet]
        _ = M⁻¹ * (M * ((N : ℝ)⁻¹ • M.transpose)) := Matrix.mul_assoc _ _ _
        _ = M⁻¹ * 1 := by rw [hmul]
        _ = M⁻¹ := Matrix.mul_one _
    rw [hinv]
    exact Matrix.nonsing_inv_mul M hdet
  have hentry := congrFun (congrFun hmul2 a) b
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
    M, Matrix.of_apply, Matrix.one_apply] at hentry
  have hpull : ∑ k : Fin N, (N : ℝ)⁻¹ * pm (H k a) * pm (H k b) =
      (N : ℝ)⁻¹ * ∑ k : Fin N, pm (H k a) * pm (H k b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hpull] at hentry
  have hmulN := congrArg (fun z : ℝ => (N : ℝ) * z) hentry
  rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul] at hmulN
  rw [hmulN]
  split_ifs <;> simp

lemma hadamard_swap {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool}
    (hH : ∀ a b : Fin N, a ≠ b →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N) :
    ∀ a b : Fin N, a ≠ b →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H v a ≠ H v b)).card = N := by
  intro a b hab
  have horth := hadamard_orth_cols hN hH a b
  simp only [hab, ↓reduceIte] at horth
  let diff := (Finset.univ : Finset (Fin N)).filter (fun v => H v a ≠ H v b)
  let same := (Finset.univ : Finset (Fin N)).filter (fun v => H v a = H v b)
  have hcard_sum : same.card + diff.card = N := by
    have h1 := card_filter_add_card_filter_not (Finset.univ : Finset (Fin N))
      (fun v => H v a = H v b)
    simpa [same, diff] using h1
  have hsplit : ∑ v : Fin N, pm (H v a) * pm (H v b) = (same.card : ℝ) - (diff.card : ℝ) := by
    have hunion : (Finset.univ : Finset (Fin N)) = same ∪ diff := by
      ext v
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, same, diff]
      exact eq_or_ne _ _
    have hdisj : Disjoint same diff := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    conv_lhs => rw [hunion]
    rw [Finset.sum_union hdisj]
    have hs : ∑ v ∈ same, pm (H v a) * pm (H v b) = (same.card : ℝ) := by
      trans ∑ v ∈ same, (1 : ℝ)
      · refine Finset.sum_congr rfl fun v hv => ?_
        rw [(Finset.mem_filter.mp hv).2, pm_mul_self]
      · simp
    have hd : ∑ v ∈ diff, pm (H v a) * pm (H v b) = -(diff.card : ℝ) := by
      trans ∑ v ∈ diff, (-1 : ℝ)
      · refine Finset.sum_congr rfl fun v hv => ?_
        have hne : H v a ≠ H v b := (Finset.mem_filter.mp hv).2
        cases ha : H v a <;> cases hb : H v b <;> simp_all [pm]
      · simp
    rw [hs, hd, sub_eq_add_neg]
  rw [hsplit] at horth
  have hsame_eq : same.card = diff.card := by
    have hR : (same.card : ℝ) = (diff.card : ℝ) := sub_eq_zero.mp horth
    exact Nat.cast_injective hR
  change 2 * diff.card = N
  omega

lemma frobenius_rank_loss {N : ℕ} (hN : 0 < N) (H P : Fin N → Fin N → Bool)
    (hH : ∀ a b : Fin N, a ≠ b →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N) :
    let M : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => pm (P i j)
    let e := ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ P i j)).card
    N * (N - M.rank) ≤ 4 * e := by
  intro M e
  let HM : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => pm (H i j)
  let A : Matrix (Fin N) (Fin N) ℝ := HM - M
  let equivE : (Fin N → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.map equivE.toLinearMap (LinearMap.ker M.mulVecLin)
  have hKdim : Module.finrank ℝ K = N - M.rank := by
    have h1 : Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
      equivE.finrank_map_eq (LinearMap.ker M.mulVecLin)
    have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at h2
    have h3 : M.rank = Module.finrank ℝ (LinearMap.range M.mulVecLin) := rfl
    omega
  let B : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K := stdOrthonormalBasis ℝ K
  let bv : Fin (Module.finrank ℝ K) → EuclideanSpace ℝ (Fin N) := fun k => (B k : EuclideanSpace ℝ (Fin N))
  have hortho : Orthonormal ℝ bv := by
    refine ⟨fun k => ?_, fun k1 k2 hne => ?_⟩
    · exact B.orthonormal.1 k
    · exact B.orthonormal.2 hne
  have hrow_bessel : ∀ i : Fin N,
      ∑ k : Fin (Module.finrank ℝ K), (∑ j : Fin N, A i j * bv k j) ^ 2 ≤
        ∑ j : Fin N, (A i j) ^ 2 := by
    intro i
    let u : EuclideanSpace ℝ (Fin N) := equivE (fun j => A i j)
    have hbess := hortho.sum_inner_products_le (s := Finset.univ) u
    have hnorm : ‖u‖ ^ 2 = ∑ j : Fin N, (A i j) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
      rfl
    rw [hnorm] at hbess
    refine le_trans ?_ hbess
    refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
  have hcol_norm : ∀ k : Fin (Module.finrank ℝ K),
      ∑ i : Fin N, (∑ j : Fin N, A i j * bv k j) ^ 2 = (N : ℝ) := by
    intro k
    have hk_ker : M.mulVec (fun j => bv k j) = 0 := by
      rcases Submodule.mem_map.mp (B k).2 with ⟨v, hv, hveq⟩
      have hv_eq : (fun j => bv k j) = v := by
        ext j
        exact congrFun (congrArg (fun z : EuclideanSpace ℝ (Fin N) => (z : Fin N → ℝ)) hveq.symm) j
      rw [hv_eq]
      exact hv
    have hA_eq : ∀ i : Fin N, ∑ j : Fin N, A i j * bv k j = ∑ j : Fin N, pm (H i j) * bv k j := by
      intro i
      have hi : ∑ j : Fin N, M i j * bv k j = 0 := congrFun hk_ker i
      have hsub : ∑ j : Fin N, A i j * bv k j =
          (∑ j : Fin N, HM i j * bv k j) - (∑ j : Fin N, M i j * bv k j) := by
        simp only [A, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [hsub, hi, sub_zero]
      rfl
    simp_rw [hA_eq]
    have hsq : ∀ i : Fin N,
        (∑ j : Fin N, pm (H i j) * bv k j) ^ 2 =
          ∑ j1 : Fin N, ∑ j2 : Fin N, (bv k j1 * bv k j2) * (pm (H i j1) * pm (H i j2)) := by
      intro i
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j2 _ => by ring
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hswap :
        ∑ j1 : Fin N, ∑ i : Fin N, ∑ j2 : Fin N, (bv k j1 * bv k j2) * (pm (H i j1) * pm (H i j2)) =
          ∑ j1 : Fin N, ∑ j2 : Fin N, (bv k j1 * bv k j2) * (∑ i : Fin N, pm (H i j1) * pm (H i j2)) := by
      refine Finset.sum_congr rfl fun j1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j2 _ => (Finset.mul_sum _ _ _).symm
    rw [hswap]
    simp_rw [hadamard_orth_cols hN hH]
    have hdiag : ∀ j1 : Fin N,
        ∑ j2 : Fin N, (bv k j1 * bv k j2) * (if j1 = j2 then (N : ℝ) else 0) =
          (N : ℝ) * (bv k j1) ^ 2 := by
      intro j1
      have hterm : ∀ j2 : Fin N,
          (bv k j1 * bv k j2) * (if j1 = j2 then (N : ℝ) else 0) =
            if j2 = j1 then (N : ℝ) * (bv k j1) ^ 2 else 0 := by
        intro j2
        by_cases h12 : j2 = j1
        · subst h12; simp [sq]; ring
        · have h21 : j1 ≠ j2 := Ne.symm h12
          simp [h12, h21]
      simp [hterm]
    simp_rw [hdiag, ← Finset.mul_sum]
    have hunit : ∑ j1 : Fin N, (bv k j1) ^ 2 = 1 := by
      have h1 : ‖bv k‖ ^ 2 = 1 := by rw [hortho.1 k, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at h1
      convert h1 using 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    rw [hunit, mul_one]
  have hfrob : ∑ i : Fin N, ∑ j : Fin N, (A i j) ^ 2 = (4 * e : ℝ) := by
    have hrow : ∀ i : Fin N,
        ∑ j : Fin N, (A i j) ^ 2 =
          4 * (((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ P i j)).card : ℝ) := by
      intro i
      have hentry : ∀ j : Fin N, (A i j) ^ 2 = if H i j ≠ P i j then (4 : ℝ) else 0 := by
        intro j
        change (pm (H i j) - pm (P i j)) ^ 2 = _
        cases H i j <;> cases P i j <;> norm_num [pm]
      simp_rw [hentry]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
      ring
    simp_rw [hrow, ← Finset.mul_sum]
    dsimp only [e]
    push_cast
    rfl
  have hreal : ((N * (N - M.rank) : ℕ) : ℝ) ≤ ((4 * e : ℕ) : ℝ) := by
    have hsum1 : ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ K), (∑ j : Fin N, A i j * bv k j) ^ 2 ≤
        ∑ i : Fin N, ∑ j : Fin N, (A i j) ^ 2 :=
      Finset.sum_le_sum fun i _ => hrow_bessel i
    rw [Finset.sum_comm] at hsum1
    simp_rw [hcol_norm] at hsum1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKdim, hfrob] at hsum1
    push_cast at hsum1 ⊢
    linarith
  exact Nat.cast_le.mp hreal

def evalTri (t : ℕ) (lam mu : (k : Fin t) → Fin k.val → ZMod 2)
    (d : Fin (2 * t) → ZMod 2) : (k : ℕ) → k ≤ t → ZMod 2
  | 0, _ => 0
  | k + 1, hk =>
    let lk := d ⟨2 * k, by omega⟩ +
      ∑ l : Fin k, lam ⟨k, hk⟩ l * evalTri t lam mu d (l.val + 1) (by omega)
    let rk := d ⟨2 * k + 1, by omega⟩ +
      ∑ l : Fin k, mu ⟨k, hk⟩ l * evalTri t lam mu d (l.val + 1) (by omega)
    lk * rk

def triGate {t : ℕ} (lam mu : (k : Fin t) → Fin k.val → ZMod 2)
    (d : Fin (2 * t) → ZMod 2) (k : Fin t) : ZMod 2 :=
  evalTri t lam mu d (k.val + 1) k.isLt

lemma evalTri_congr {t1 t2 : ℕ} {lam1 mu1 : (k : Fin t1) → Fin k.val → ZMod 2}
    {lam2 mu2 : (k : Fin t2) → Fin k.val → ZMod 2}
    {d1 : Fin (2 * t1) → ZMod 2} {d2 : Fin (2 * t2) → ZMod 2}
    (n : ℕ) (h1 : n ≤ t1) (h2 : n ≤ t2)
    (hd : ∀ i : ℕ, (hi : i < 2 * n) → d1 ⟨i, by omega⟩ = d2 ⟨i, by omega⟩)
    (hlam : ∀ (k : ℕ) (hk : k < n) (l : Fin k), lam1 ⟨k, by omega⟩ l = lam2 ⟨k, by omega⟩ l)
    (hmu : ∀ (k : ℕ) (hk : k < n) (l : Fin k), mu1 ⟨k, by omega⟩ l = mu2 ⟨k, by omega⟩ l) :
    evalTri t1 lam1 mu1 d1 n h1 = evalTri t2 lam2 mu2 d2 n h2 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [evalTri.eq_1, evalTri.eq_1]
    | succ k =>
      rw [evalTri.eq_2, evalTri.eq_2]
      have hd1 : d1 ⟨2 * k, by omega⟩ = d2 ⟨2 * k, by omega⟩ := hd (2 * k) (by omega)
      have hd2 : d1 ⟨2 * k + 1, by omega⟩ = d2 ⟨2 * k + 1, by omega⟩ := hd (2 * k + 1) (by omega)
      have hsum1 :
          ∑ l : Fin k, lam1 ⟨k, h1⟩ l * evalTri t1 lam1 mu1 d1 (l.val + 1) (by omega) =
          ∑ l : Fin k, lam2 ⟨k, h2⟩ l * evalTri t2 lam2 mu2 d2 (l.val + 1) (by omega) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hlam k (Nat.lt_succ_self k) l]
        congr 1
        exact ih (l.val + 1) (by omega) (by omega) (by omega)
          (fun i hi => hd i (by omega))
          (fun j hj m => hlam j (by omega) m)
          (fun j hj m => hmu j (by omega) m)
      have hsum2 :
          ∑ l : Fin k, mu1 ⟨k, h1⟩ l * evalTri t1 lam1 mu1 d1 (l.val + 1) (by omega) =
          ∑ l : Fin k, mu2 ⟨k, h2⟩ l * evalTri t2 lam2 mu2 d2 (l.val + 1) (by omega) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hmu k (Nat.lt_succ_self k) l]
        congr 1
        exact ih (l.val + 1) (by omega) (by omega) (by omega)
          (fun i hi => hd i (by omega))
          (fun j hj m => hlam j (by omega) m)
          (fun j hj m => hmu j (by omega) m)
      rw [hd1, hd2, hsum1, hsum2]

lemma triGate_pure {t : ℕ} (d : Fin (2 * t) → ZMod 2) (k : Fin t) :
    triGate (fun _ _ => 0) (fun _ _ => 0) d k =
      d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩ := by
  dsimp only [triGate]
  rw [evalTri.eq_2]
  simp

def fourierCoeff {m : ℕ} (F : (Fin m → ZMod 2) → ZMod 2) (ω : Fin m → ZMod 2) : ℝ :=
  ∑ d : Fin m → ZMod 2, pmZ2 (F d) * chi ω d

noncomputable def fourierSupp {m : ℕ} (F : (Fin m → ZMod 2) → ZMod 2) : Finset (Fin m → ZMod 2) :=
  Finset.univ.filter (fun ω => fourierCoeff F ω ≠ 0)

lemma sum_pmZ2_pair (u v a b : ZMod 2) :
    ∑ x : ZMod 2, ∑ y : ZMod 2, pmZ2 ((x + a) * (y + b) + u * x + v * y) =
      2 * pmZ2 (u * v + u * a + v * b) := by
  rcases z2_zero_or_one u with rfl | rfl <;>
    rcases z2_zero_or_one v with rfl | rfl <;>
    rcases z2_zero_or_one a with rfl | rfl <;>
    rcases z2_zero_or_one b with rfl | rfl <;>
    simp only [sum_z2, pmZ2, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      show (1 : ZMod 2) + 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte] <;>
    norm_num

def splitVec {t : ℕ} (d : Fin (2 * (t + 1)) → ZMod 2) :
    (Fin (2 * t) → ZMod 2) × (ZMod 2 × ZMod 2) :=
  (fun i => d ⟨i.val, by omega⟩, (d ⟨2 * t, by omega⟩, d ⟨2 * t + 1, by omega⟩))

def joinVec {t : ℕ} (p : (Fin (2 * t) → ZMod 2) × (ZMod 2 × ZMod 2)) :
    Fin (2 * (t + 1)) → ZMod 2 :=
  fun i =>
    if h1 : i.val < 2 * t then p.1 ⟨i.val, h1⟩
    else if i.val = 2 * t then p.2.1
    else p.2.2

def splitEquiv (t : ℕ) :
    (Fin (2 * (t + 1)) → ZMod 2) ≃ (Fin (2 * t) → ZMod 2) × (ZMod 2 × ZMod 2) where
  toFun := splitVec
  invFun := joinVec
  left_inv := fun d => by
    ext i
    simp only [joinVec, splitVec]
    split_ifs with h1 h2
    · rfl
    · congr 1; exact Fin.ext h2.symm
    · have h3 : i.val = 2 * t + 1 := by omega
      congr 1; exact Fin.ext h3.symm
  right_inv := fun ⟨d', x, y⟩ => by
    apply Prod.ext
    · ext i
      simp [splitVec, joinVec]
    · apply Prod.ext
      · simp [splitVec, joinVec]
      · simp [splitVec, joinVec]

lemma chi_joinVec {t : ℕ} (ω' d' : Fin (2 * t) → ZMod 2) (u v x y : ZMod 2) :
    chi (joinVec (ω', (u, v))) (joinVec (d', (x, y))) =
      chi ω' d' * pmZ2 (u * x + v * y) := by
  simp only [chi, ← pmZ2_add]
  congr 1
  let e : Fin ((2 * t + 1) + 1) ≃ Fin (2 * (t + 1)) := finCongr (by omega)
  rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have ha : ∀ i : Fin (2 * t),
      joinVec (ω', (u, v)) (e i.castSucc.castSucc) * joinVec (d', (x, y)) (e i.castSucc.castSucc) =
        ω' i * d' i := by
    intro i
    simp [e, joinVec, i.isLt]
  have hb : joinVec (ω', (u, v)) (e (Fin.last (2 * t)).castSucc) *
      joinVec (d', (x, y)) (e (Fin.last (2 * t)).castSucc) = u * x := by
    simp [e, joinVec]
  have hc : joinVec (ω', (u, v)) (e (Fin.last (2 * t + 1))) *
      joinVec (d', (x, y)) (e (Fin.last (2 * t + 1))) = v * y := by
    simp [e, joinVec]
  rw [Finset.sum_congr rfl fun i _ => ha i, hb, hc, add_assoc]

lemma fourierSupp_pure_le {t : ℕ} (c : Fin t → ZMod 2) (hnot : ∃ k : Fin t, c k = 0) :
    (fourierSupp (fun d : Fin (2 * t) → ZMod 2 =>
      ∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩))).card ≤
      4 ^ (t - 1) := by
  obtain ⟨k0, hk0⟩ := hnot
  have hsub :
      fourierSupp (fun d : Fin (2 * t) → ZMod 2 =>
        ∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) ⊆
      (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter
        (fun ω => ω ⟨2 * k0.val, by omega⟩ = 0 ∧ ω ⟨2 * k0.val + 1, by omega⟩ = 0) := by
    intro ω hω
    have hne : fourierCoeff (fun d : Fin (2 * t) → ZMod 2 =>
        ∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) ω ≠ 0 :=
      (Finset.mem_filter.mp hω).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · by_contra hne0
      have h1 : ω ⟨2 * k0.val, by omega⟩ = 1 := by
        rcases z2_zero_or_one (ω ⟨2 * k0.val, by omega⟩) with h0 | h1
        · exact False.elim (hne0 h0)
        · exact h1
      apply hne
      let idx : Fin (2 * t) := ⟨2 * k0.val, by omega⟩
      let F0 := (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter (fun d => d idx = 0)
      let F1 := (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter (fun d => d idx = 1)
      have hunion : (Finset.univ : Finset (Fin (2 * t) → ZMod 2)) = F0 ∪ F1 := by
        ext d
        simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, F0, F1]
        exact z2_zero_or_one (d idx)
      have hdisj : Disjoint F0 F1 := by
        rw [Finset.disjoint_left]
        intro d h0 h1'
        have ha : d idx = 0 := (Finset.mem_filter.mp h0).2
        have hb : d idx = 1 := (Finset.mem_filter.mp h1').2
        rw [ha] at hb
        exact zero_ne_one hb
      have hneg :
          ∑ d ∈ F1, pmZ2 (∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) * chi ω d =
          -(∑ d ∈ F0, pmZ2 (∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) * chi ω d) := by
        rw [← Finset.sum_neg_distrib]
        symm
        refine Finset.sum_bij (fun d _ => Function.update d idx 1) ?_ ?_ ?_ ?_
        · intro d _; simp [F1]
        · intro d1 hd1 d2 hd2 heq
          ext i
          by_cases hi : i = idx
          · subst hi
            exact ((Finset.mem_filter.mp hd1).2).trans ((Finset.mem_filter.mp hd2).2).symm
          · simpa [Function.update_of_ne hi] using congrFun heq i
        · intro d hd
          refine ⟨Function.update d idx 0, by simp [F0], ?_⟩
          ext i
          by_cases hi : i = idx
          · subst hi; simp [(Finset.mem_filter.mp hd).2]
          · simp [Function.update_of_ne hi]
        · intro d hd
          have hd0 : d idx = 0 := (Finset.mem_filter.mp hd).2
          have hupd : Function.update d idx 1 = d + Pi.single idx 1 := by
            ext i
            by_cases hi : i = idx
            · subst hi; simp [hd0]
            · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
          have hsameF :
              ∑ k : Fin t, c k * (Function.update d idx 1 ⟨2 * k.val, by omega⟩ *
                  Function.update d idx 1 ⟨2 * k.val + 1, by omega⟩) =
              ∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            by_cases hkk : k = k0
            · subst hkk; simp [hk0]
            · have hne1 : (⟨2 * k.val, by omega⟩ : Fin (2 * t)) ≠ idx := by
                intro h; exact hkk (Fin.ext (by have := congrArg Fin.val h; dsimp [idx] at this; omega))
              have hne2 : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * t)) ≠ idx := by
                intro h; have := congrArg Fin.val h; dsimp [idx] at this; omega
              simp [Function.update_of_ne hne1, Function.update_of_ne hne2]
          rw [hsameF, hupd, chi_add_right]
          have hsing : chi ω (Pi.single idx 1) = -1 := by
            simp only [chi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte, idx, h1, pmZ2]
          rw [hsing, mul_neg_one, mul_neg]
      dsimp only [fourierCoeff]
      rw [hunion, Finset.sum_union hdisj, hneg, add_neg_cancel]
    · by_contra hne0
      have h1 : ω ⟨2 * k0.val + 1, by omega⟩ = 1 := by
        rcases z2_zero_or_one (ω ⟨2 * k0.val + 1, by omega⟩) with h0 | h1
        · exact False.elim (hne0 h0)
        · exact h1
      apply hne
      let idx : Fin (2 * t) := ⟨2 * k0.val + 1, by omega⟩
      let F0 := (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter (fun d => d idx = 0)
      let F1 := (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter (fun d => d idx = 1)
      have hunion : (Finset.univ : Finset (Fin (2 * t) → ZMod 2)) = F0 ∪ F1 := by
        ext d
        simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, F0, F1]
        exact z2_zero_or_one (d idx)
      have hdisj : Disjoint F0 F1 := by
        rw [Finset.disjoint_left]
        intro d h0 h1'
        have ha : d idx = 0 := (Finset.mem_filter.mp h0).2
        have hb : d idx = 1 := (Finset.mem_filter.mp h1').2
        rw [ha] at hb
        exact zero_ne_one hb
      have hneg :
          ∑ d ∈ F1, pmZ2 (∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) * chi ω d =
          -(∑ d ∈ F0, pmZ2 (∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩)) * chi ω d) := by
        rw [← Finset.sum_neg_distrib]
        symm
        refine Finset.sum_bij (fun d _ => Function.update d idx 1) ?_ ?_ ?_ ?_
        · intro d _; simp [F1]
        · intro d1 hd1 d2 hd2 heq
          ext i
          by_cases hi : i = idx
          · subst hi
            exact ((Finset.mem_filter.mp hd1).2).trans ((Finset.mem_filter.mp hd2).2).symm
          · simpa [Function.update_of_ne hi] using congrFun heq i
        · intro d hd
          refine ⟨Function.update d idx 0, by simp [F0], ?_⟩
          ext i
          by_cases hi : i = idx
          · subst hi; simp [(Finset.mem_filter.mp hd).2]
          · simp [Function.update_of_ne hi]
        · intro d hd
          have hd0 : d idx = 0 := (Finset.mem_filter.mp hd).2
          have hupd : Function.update d idx 1 = d + Pi.single idx 1 := by
            ext i
            by_cases hi : i = idx
            · subst hi; simp [hd0]
            · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
          have hsameF :
              ∑ k : Fin t, c k * (Function.update d idx 1 ⟨2 * k.val, by omega⟩ *
                  Function.update d idx 1 ⟨2 * k.val + 1, by omega⟩) =
              ∑ k : Fin t, c k * (d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            by_cases hkk : k = k0
            · subst hkk; simp [hk0]
            · have hne1 : (⟨2 * k.val, by omega⟩ : Fin (2 * t)) ≠ idx := by
                intro h; have := congrArg Fin.val h; dsimp [idx] at this; omega
              have hne2 : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * t)) ≠ idx := by
                intro h; exact hkk (Fin.ext (by have := congrArg Fin.val h; dsimp [idx] at this; omega))
              simp [Function.update_of_ne hne1, Function.update_of_ne hne2]
          rw [hsameF, hupd, chi_add_right]
          have hsing : chi ω (Pi.single idx 1) = -1 := by
            simp only [chi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte, idx, h1, pmZ2]
          rw [hsing, mul_neg_one, mul_neg]
      dsimp only [fourierCoeff]
      rw [hunion, Finset.sum_union hdisj, hneg, add_neg_cancel]
  refine le_trans (Finset.card_le_card hsub) ?_
  let i1 : Fin (2 * t) := ⟨2 * k0.val, by omega⟩
  let i2 : Fin (2 * t) := ⟨2 * k0.val + 1, by omega⟩
  have hi12 : i1 ≠ i2 := by
    intro h; have := congrArg Fin.val h; dsimp [i1, i2] at this; omega
  let S0 : Finset (Fin (2 * t)) := {i1, i2}
  have hS0card : S0.card = 2 := Finset.card_pair hi12
  let e : { ω : Fin (2 * t) → ZMod 2 // ω i1 = 0 ∧ ω i2 = 0 } ≃
      ({ i : Fin (2 * t) // i ∉ S0 } → ZMod 2) :=
    { toFun := fun ⟨ω, _⟩ ⟨i, _⟩ => ω i
      invFun := fun g => ⟨fun i => if h : i ∈ S0 then 0 else g ⟨i, h⟩, by simp [S0]⟩
      left_inv := fun ⟨ω, h1, h2⟩ => by
        apply Subtype.ext
        ext i
        by_cases hi : i ∈ S0
        · simp only [hi, ↓reduceDIte]
          rcases Finset.mem_insert.mp hi with rfl | hmem
          · exact h1.symm
          · rw [Finset.mem_singleton.mp hmem]; exact h2.symm
        · simp [hi]
      right_inv := fun g => by
        ext ⟨i, hi⟩
        simp [hi] }
  have hcard :
      ((Finset.univ : Finset (Fin (2 * t) → ZMod 2)).filter
        (fun ω => ω i1 = 0 ∧ ω i2 = 0)).card = 4 ^ (t - 1) := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card,
      Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hS0card]
    have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact Fin.elim0 k0)
    have hexp : 2 * t - 2 = 2 * (t - 1) := by omega
    rw [hexp, pow_mul]
    norm_num
  exact le_of_eq hcard

lemma triangular_spectrum_cutoff : ∀ (t : ℕ)
    (lam mu : (k : Fin t) → Fin k.val → ZMod 2) (c : Fin t → ZMod 2),
    let F : (Fin (2 * t) → ZMod 2) → ZMod 2 := fun d => ∑ k : Fin t, c k * triGate lam mu d k
    8 * (fourierSupp F).card ≤ 5 * 4 ^ t ∨
    ((∀ k : Fin t, c k = 1) ∧ (∀ k : Fin t, ∀ l : Fin k.val, lam k l = 0 ∧ mu k l = 0)) := by
  intro t
  induction t with
  | zero =>
    intro lam mu c
    right
    exact ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k⟩
  | succ t ih =>
    intro lam mu c F
    let lam' : (k : Fin t) → Fin k.val → ZMod 2 := fun k l => lam k.castSucc l
    let mu' : (k : Fin t) → Fin k.val → ZMod 2 := fun k l => mu k.castSucc l
    let c' : Fin t → ZMod 2 := fun k => c k.castSucc
    let α : Fin t → ZMod 2 := fun l => lam (Fin.last t) l
    let β : Fin t → ZMod 2 := fun l => mu (Fin.last t) l
    have htri_prev : ∀ (d' : Fin (2 * t) → ZMod 2) (x y : ZMod 2) (k : Fin t),
        triGate lam mu (joinVec (d', (x, y))) k.castSucc = triGate lam' mu' d' k := by
      intro d' x y k
      dsimp only [triGate]
      refine evalTri_congr (k.val + 1) _ _ ?_ ?_ ?_
      · intro i hi
        have hlt : i < 2 * t := by omega
        simp [joinVec, hlt]
      · intro j hj l; rfl
      · intro j hj l; rfl
    have htri_last : ∀ (d' : Fin (2 * t) → ZMod 2) (x y : ZMod 2),
        triGate lam mu (joinVec (d', (x, y))) (Fin.last t) =
          (x + ∑ l : Fin t, α l * triGate lam' mu' d' l) *
          (y + ∑ l : Fin t, β l * triGate lam' mu' d' l) := by
      intro d' x y
      dsimp only [triGate]
      rw [evalTri.eq_2]
      simp only [Fin.val_last]
      have hx : joinVec (d', (x, y)) ⟨2 * t, by omega⟩ = x := by simp [joinVec]
      have hy : joinVec (d', (x, y)) ⟨2 * t + 1, by omega⟩ = y := by simp [joinVec]
      rw [hx, hy]
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 1
        exact htri_prev d' x y l
      · congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 1
        exact htri_prev d' x y l
    have hF_join : ∀ (d' : Fin (2 * t) → ZMod 2) (x y : ZMod 2),
        F (joinVec (d', (x, y))) =
          (∑ k : Fin t, c' k * triGate lam' mu' d' k) +
          c (Fin.last t) *
            ((x + ∑ l : Fin t, α l * triGate lam' mu' d' l) *
             (y + ∑ l : Fin t, β l * triGate lam' mu' d' l)) := by
      intro d' x y
      dsimp only [F]
      rw [Fin.sum_univ_castSucc, htri_last]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [htri_prev]
    rcases z2_zero_or_one (c (Fin.last t)) with hclast | hclast
    · left
      have hsub : fourierSupp F ⊆
          (Finset.univ : Finset (Fin (2 * (t + 1)) → ZMod 2)).filter
            (fun ω => ω ⟨2 * t, by omega⟩ = 0 ∧ ω ⟨2 * t + 1, by omega⟩ = 0) := by
        intro ω hω
        have hne : fourierCoeff F ω ≠ 0 := (Finset.mem_filter.mp hω).2
        have hcalc : fourierCoeff F ω =
            (∑ d' : Fin (2 * t) → ZMod 2,
              pmZ2 (∑ k : Fin t, c' k * triGate lam' mu' d' k) * chi (splitVec ω).1 d') *
            (∑ x : ZMod 2, ∑ y : ZMod 2, pmZ2 ((splitVec ω).2.1 * x + (splitVec ω).2.2 * y)) := by
          dsimp only [fourierCoeff]
          rw [← Equiv.sum_comp (splitEquiv t).symm]
          simp only [splitEquiv, Equiv.coe_fn_symm_mk]
          have hω_eq : ω = joinVec (splitVec ω) := ((splitEquiv t).left_inv ω).symm
          conv_lhs => arg 2; ext p; rw [hω_eq, chi_joinVec]
          rw [Fintype.sum_prod_type, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hF_join, hclast, zero_mul, add_zero]
          ring
        have hxy : ∑ x : ZMod 2, ∑ y : ZMod 2,
            pmZ2 ((splitVec ω).2.1 * x + (splitVec ω).2.2 * y) ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hcalc
          exact hne hcalc
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases z2_zero_or_one (ω ⟨2 * t, by omega⟩) with hu | hu <;>
          rcases z2_zero_or_one (ω ⟨2 * t + 1, by omega⟩) with hv | hv
        · exact ⟨hu, hv⟩
        · exfalso; apply hxy
          simp only [splitVec, hu, hv, sum_z2, pmZ2, zero_mul, one_mul, zero_add,
            show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
          norm_num
        · exfalso; apply hxy
          simp only [splitVec, hu, hv, sum_z2, pmZ2, zero_mul, one_mul, add_zero,
            show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
          norm_num
        · exfalso; apply hxy
          simp only [splitVec, hu, hv, sum_z2, pmZ2, one_mul, add_zero, zero_add,
            show (1 : ZMod 2) + 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
          norm_num
      have hcard_le : (fourierSupp F).card ≤ 4 ^ t := by
        refine le_trans (Finset.card_le_card hsub) ?_
        let e : { ω : Fin (2 * (t + 1)) → ZMod 2 //
            ω ⟨2 * t, by omega⟩ = 0 ∧ ω ⟨2 * t + 1, by omega⟩ = 0 } ≃
            (Fin (2 * t) → ZMod 2) :=
          { toFun := fun ⟨ω, _⟩ => (splitVec ω).1
            invFun := fun ω' => ⟨joinVec (ω', (0, 0)), by simp [joinVec]⟩
            left_inv := fun ⟨ω, h1, h2⟩ => by
              apply Subtype.ext
              change joinVec ((splitVec ω).1, (0, 0)) = ω
              have hsp : splitVec ω = ((splitVec ω).1, (0, 0)) :=
                Prod.ext rfl (Prod.ext h1 h2)
              rw [← hsp]
              exact (splitEquiv t).left_inv ω
            right_inv := fun ω' => by
              ext i
              simp [splitVec, joinVec] }
        rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card,
          Fintype.card_fin, pow_mul]
        norm_num
      have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [pow_succ, mul_comm]
      omega
    · let G : ZMod 2 → ZMod 2 → (Fin (2 * t) → ZMod 2) → ZMod 2 := fun u v d' =>
        ∑ k : Fin t, (c' k + u * α k + v * β k) * triGate lam' mu' d' k
      have hfc_eq : ∀ (ω' : Fin (2 * t) → ZMod 2) (u v : ZMod 2),
          fourierCoeff F (joinVec (ω', (u, v))) =
            2 * pmZ2 (u * v) * fourierCoeff (G u v) ω' := by
        intro ω' u v
        dsimp only [fourierCoeff]
        rw [← Equiv.sum_comp (splitEquiv t).symm]
        simp only [splitEquiv, Equiv.coe_fn_symm_mk]
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [Fintype.sum_prod_type]
        have hinner :
            ∑ x : ZMod 2, ∑ y : ZMod 2,
              pmZ2 (F (joinVec (d', (x, y)))) * chi (joinVec (ω', (u, v))) (joinVec (d', (x, y))) =
            pmZ2 (∑ k : Fin t, c' k * triGate lam' mu' d' k) * chi ω' d' *
              ∑ x : ZMod 2, ∑ y : ZMod 2,
                pmZ2 ((x + ∑ l : Fin t, α l * triGate lam' mu' d' l) *
                      (y + ∑ l : Fin t, β l * triGate lam' mu' d' l) + u * x + v * y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hF_join, hclast, one_mul, chi_joinVec]
          simp only [pmZ2_add]
          ring
        rw [hinner, sum_pmZ2_pair]
        have hG : pmZ2 (G u v d') =
            pmZ2 (∑ k : Fin t, c' k * triGate lam' mu' d' k) *
              pmZ2 (u * (∑ l : Fin t, α l * triGate lam' mu' d' l) +
                    v * (∑ l : Fin t, β l * triGate lam' mu' d' l)) := by
          rw [← pmZ2_add]
          congr 1
          dsimp only [G]
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [hG]
        simp only [pmZ2_add]
        ring
      have hcard_split :
          (fourierSupp F).card =
            (fourierSupp (G 0 0)).card + (fourierSupp (G 1 0)).card +
            (fourierSupp (G 0 1)).card + (fourierSupp (G 1 1)).card := by
        have hbij :
            (fourierSupp F).card =
              ∑ p : ZMod 2 × ZMod 2, (fourierSupp (G p.1 p.2)).card := by
          let S := (Finset.univ : Finset ((Fin (2 * t) → ZMod 2) × (ZMod 2 × ZMod 2))).filter
            (fun p => fourierCoeff (G p.2.1 p.2.2) p.1 ≠ 0)
          have h1 : (fourierSupp F).card = S.card := by
            refine Finset.card_bij (fun ω _ => splitVec ω) ?_ ?_ ?_
            · intro ω hω
              have hne : fourierCoeff F ω ≠ 0 := (Finset.mem_filter.mp hω).2
              have hω_eq : ω = joinVec (splitVec ω) := ((splitEquiv t).left_inv ω).symm
              rw [hω_eq, hfc_eq] at hne
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hne⟩
            · intro ω1 _ ω2 _ heq
              exact (splitEquiv t).injective heq
            · intro ⟨ω', u, v⟩ hp
              have hne : fourierCoeff (G u v) ω' ≠ 0 := (Finset.mem_filter.mp hp).2
              refine ⟨joinVec (ω', (u, v)), ?_, (splitEquiv t).right_inv (ω', (u, v))⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rw [hfc_eq]
              have hnz : 2 * pmZ2 (u * v) ≠ 0 := by
                rcases z2_zero_or_one (u * v) with h | h <;> rw [h] <;> norm_num [pmZ2]
              exact mul_ne_zero hnz hne
          rw [h1]
          rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
          refine Finset.sum_congr rfl fun ⟨u, v⟩ _ => ?_
          refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
          · intro ⟨ω', u', v'⟩ hp
            rcases Finset.mem_filter.mp hp with ⟨hpS, heq⟩
            simp only at heq
            rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hpS).2⟩
          · intro ⟨ω1, p1⟩ hp1 ⟨ω2, p2⟩ hp2 heq
            have h1' : p1 = (u, v) := (Finset.mem_filter.mp hp1).2
            have h2' : p2 = (u, v) := (Finset.mem_filter.mp hp2).2
            exact Prod.ext heq (h1'.trans h2'.symm)
          · intro ω' hω'
            refine ⟨(ω', (u, v)), ?_, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp hω').2⟩, rfl⟩
        rw [hbij, Fintype.sum_prod_type]
        simp only [sum_z2]
        omega
      have hih00 := ih lam' mu' (fun k => c' k + 0 * α k + 0 * β k)
      have hih10 := ih lam' mu' (fun k => c' k + 1 * α k + 0 * β k)
      have hih01 := ih lam' mu' (fun k => c' k + 0 * α k + 1 * β k)
      have hih11 := ih lam' mu' (fun k => c' k + 1 * α k + 1 * β k)
      have hbound_any : ∀ u v : ZMod 2, (fourierSupp (G u v)).card ≤ 4 ^ t := by
        intro u v
        calc
          (fourierSupp (G u v)).card ≤ (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).card :=
            Finset.card_le_univ _
          _ = 4 ^ t := by
            rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_mul]
            norm_num
      have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := by rw [pow_succ, mul_comm]
      by_cases hall_small :
          8 * (fourierSupp (G 0 0)).card ≤ 5 * 4 ^ t ∧
          8 * (fourierSupp (G 1 0)).card ≤ 5 * 4 ^ t ∧
          8 * (fourierSupp (G 0 1)).card ≤ 5 * 4 ^ t ∧
          8 * (fourierSupp (G 1 1)).card ≤ 5 * 4 ^ t
      · left
        rw [hcard_split, hpow]
        omega
      · have hpure_prev : ∀ k : Fin t, ∀ l : Fin k.val, lam' k l = 0 ∧ mu' k l = 0 := by
          by_contra hnot
          have h00 : 8 * (fourierSupp (G 0 0)).card ≤ 5 * 4 ^ t :=
            hih00.elim id (fun h => False.elim (hnot h.2))
          have h10 : 8 * (fourierSupp (G 1 0)).card ≤ 5 * 4 ^ t :=
            hih10.elim id (fun h => False.elim (hnot h.2))
          have h01 : 8 * (fourierSupp (G 0 1)).card ≤ 5 * 4 ^ t :=
            hih01.elim id (fun h => False.elim (hnot h.2))
          have h11 : 8 * (fourierSupp (G 1 1)).card ≤ 5 * 4 ^ t :=
            hih11.elim id (fun h => False.elim (hnot h.2))
          exact hall_small ⟨h00, h10, h01, h11⟩
        have htri_eq_pure : ∀ (d' : Fin (2 * t) → ZMod 2) (k : Fin t),
            triGate lam' mu' d' k = d' ⟨2 * k.val, by omega⟩ * d' ⟨2 * k.val + 1, by omega⟩ := by
          intro d' k
          have hzero : triGate lam' mu' d' k = triGate (fun _ _ => 0) (fun _ _ => 0) d' k := by
            dsimp only [triGate]
            refine evalTri_congr (k.val + 1) _ _ (fun _ _ => rfl) ?_ ?_
            · intro j hj l; exact (hpure_prev ⟨j, by omega⟩ l).1
            · intro j hj l; exact (hpure_prev ⟨j, by omega⟩ l).2
          rw [hzero, triGate_pure]
        have hG_small : ∀ (u v : ZMod 2), (∃ k : Fin t, c' k + u * α k + v * β k = 0) →
            (fourierSupp (G u v)).card ≤ 4 ^ (t - 1) := by
          intro u v hzero
          have hGeq : G u v = fun d' =>
              ∑ k : Fin t, (c' k + u * α k + v * β k) *
                (d' ⟨2 * k.val, by omega⟩ * d' ⟨2 * k.val + 1, by omega⟩) := by
            funext d'
            dsimp only [G]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [htri_eq_pure]
          rw [hGeq]
          exact fourierSupp_pure_le _ hzero
        by_cases hab0 : ∀ k : Fin t, α k = 0 ∧ β k = 0
        · have hc_all1 : ∀ k : Fin t, c' k = 1 := by
            by_contra hnot1
            have hex0 : ∃ k : Fin t, c' k = 0 := by
              by_contra hall
              apply hnot1
              intro k
              rcases z2_zero_or_one (c' k) with h0 | h1
              · exact False.elim (hall ⟨k, h0⟩)
              · exact h1
            have h00 : (fourierSupp (G 0 0)).card ≤ 4 ^ (t - 1) :=
              hG_small 0 0 (by rcases hex0 with ⟨k, hk⟩; exact ⟨k, by simp [hk]⟩)
            have h10 : (fourierSupp (G 1 0)).card ≤ 4 ^ (t - 1) :=
              hG_small 1 0 (by rcases hex0 with ⟨k, hk⟩; exact ⟨k, by simp [hk, (hab0 k).1]⟩)
            have h01 : (fourierSupp (G 0 1)).card ≤ 4 ^ (t - 1) :=
              hG_small 0 1 (by rcases hex0 with ⟨k, hk⟩; exact ⟨k, by simp [hk, (hab0 k).2]⟩)
            have h11 : (fourierSupp (G 1 1)).card ≤ 4 ^ (t - 1) :=
              hG_small 1 1 (by rcases hex0 with ⟨k, hk⟩; exact ⟨k, by simp [hk, (hab0 k).1, (hab0 k).2]⟩)
            have ht1 : 1 ≤ t := by
              rcases hex0 with ⟨k, _⟩
              exact Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact Fin.elim0 k)
            have hpow_t : 4 * 4 ^ (t - 1) = 4 ^ t := by
              conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
            apply hall_small
            omega
          right
          constructor
          · intro k
            refine Fin.lastCases ?_ (fun k' => hc_all1 k') k
            exact hclast
          · intro k
            refine Fin.lastCases (fun l => hab0 l) (fun k' l => hpure_prev k' l) k
        · left
          have hex : ∃ k0 : Fin t, α k0 ≠ 0 ∨ β k0 ≠ 0 := by
            by_contra hall
            apply hab0
            intro k
            by_contra hnot
            apply hall
            refine ⟨k, ?_⟩
            by_cases ha : α k = 0
            · right; intro hb; exact hnot ⟨ha, hb⟩
            · left; exact ha
          obtain ⟨k0, hk0⟩ := hex
          have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact Fin.elim0 k0)
          have hpow_t : 4 * 4 ^ (t - 1) = 4 ^ t := by
            conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
          have h4 :
              (fourierSupp (G 0 0)).card + (fourierSupp (G 1 0)).card +
              (fourierSupp (G 0 1)).card + (fourierSupp (G 1 1)).card ≤
                2 * 4 ^ t + 2 * 4 ^ (t - 1) := by
            have hb00 := hbound_any 0 0
            have hb10 := hbound_any 1 0
            have hb01 := hbound_any 0 1
            have hb11 := hbound_any 1 1
            rcases z2_zero_or_one (c' k0) with hc0 | hc0 <;>
              rcases z2_zero_or_one (α k0) with ha0 | ha0 <;>
              rcases z2_zero_or_one (β k0) with hb0 | hb0
            · simp [ha0, hb0] at hk0
            · have hs00 := hG_small 0 0 ⟨k0, by simp [hc0, ha0, hb0]⟩
              have hs10 := hG_small 1 0 ⟨k0, by simp [hc0, ha0, hb0]⟩
              omega
            · have hs00 := hG_small 0 0 ⟨k0, by simp [hc0, ha0, hb0]⟩
              have hs01 := hG_small 0 1 ⟨k0, by simp [hc0, ha0, hb0]⟩
              omega
            · have hs00 := hG_small 0 0 ⟨k0, by simp [hc0, ha0, hb0]⟩
              have hs11 := hG_small 1 1 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              omega
            · simp [ha0, hb0] at hk0
            · have hs01 := hG_small 0 1 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              have hs11 := hG_small 1 1 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              omega
            · have hs10 := hG_small 1 0 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              have hs11 := hG_small 1 1 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              omega
            · have hs10 := hG_small 1 0 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              have hs01 := hG_small 0 1 ⟨k0, by simp [hc0, ha0, hb0, z2_add_self]⟩
              omega
          rw [hcard_split, hpow]
          omega

def nonlinearGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

lemma bool_fun1_affine (h : Bool → Bool) :
    ∃ c0 c1 : ZMod 2, ∀ a : Bool, b2z (h a) = c0 + c1 * b2z a := by
  refine ⟨b2z (h false), b2z (h false) + b2z (h true), fun a => ?_⟩
  cases a <;> cases h false <;> cases h true <;> decide

lemma bool_fun2_poly (h : Bool → Bool → Bool) :
    ∃ c0 c1 c2 c3 : ZMod 2,
      c3 = b2z (xor (xor (h false false) (h false true)) (xor (h true false) (h true true))) ∧
      ∀ a b : Bool, b2z (h a b) = c0 + c1 * b2z a + c2 * b2z b + c3 * b2z a * b2z b := by
  refine ⟨b2z (h false false), b2z (h false false) + b2z (h true false),
    b2z (h false false) + b2z (h false true),
    b2z (xor (xor (h false false) (h false true)) (xor (h true false) (h true true))),
    rfl, fun a b => ?_⟩
  cases a <;> cases b <;> cases h false false <;> cases h false true <;>
    cases h true false <;> cases h true true <;> decide

lemma getD_append_single (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i = l.length then b else l.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · rw [List.getD_append _ _ _ _ hlt]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma circuit_to_triangular {N : ℕ} (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hback : ReadsBack (N + N) C) :
    let t := C.gates.countP nonlinearGate
    ∃ (lam mu : (k : Fin t) → Fin k.val → ZMod 2)
      (U W : Fin N → Fin (2 * t) → ZMod 2)
      (pOut qOut : Fin N → ZMod 2)
      (cOut : Fin t → ZMod 2),
      ∀ x y : Fin N,
        b2z (C.eval (oneEach x y)) =
          pOut x + qOut y + ∑ k : Fin t, cOut k * triGate lam mu (U x + W y) k := by
  have hgen :
      ∀ (gs : List Gate) (t : ℕ), gs.countP nonlinearGate = t →
        (∀ g ∈ gs, g.inputs.length ≤ 2) →
        (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j) →
        ∃ (lam mu : (k : Fin t) → Fin k.val → ZMod 2)
          (U W : Fin N → Fin (2 * t) → ZMod 2)
          (pW qW : Fin (N + N + gs.length) → Fin N → ZMod 2)
          (cW : Fin (N + N + gs.length) → Fin t → ZMod 2),
          ∀ (x y : Fin N) (idx : Fin (N + N + gs.length)),
            b2z ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
              (oneEach x y)).getD idx.val false) =
              pW idx x + qW idx y + ∑ k : Fin t, cW idx k * triGate lam mu (U x + W y) k := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro t ht _ _
      have ht0 : t = 0 := by simpa using ht.symm
      subst ht0
      refine ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k,
        fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i,
        fun idx x => if idx.val < N then (if idx.val = x.val then 1 else 0) else 0,
        fun idx y => if N ≤ idx.val then (if idx.val - N = y.val then 1 else 0) else 0,
        fun _ k => Fin.elim0 k, ?_⟩
      intro x y idx
      simp only [List.foldl_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hlen1 : (List.ofFn (fun i : Fin N => decide (i = x))).length = N := by simp
      by_cases hlt : idx.val < N
      · have hnot : ¬ N ≤ idx.val := by omega
        simp only [hlt, hnot, ↓reduceIte, add_zero]
        dsimp only [oneEach]
        rw [List.getD_append _ _ _ _ (by rw [hlen1]; exact hlt)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
          Option.getD_some, b2z, decide_eq_true_eq, Fin.ext_iff]
      · have hge : N ≤ idx.val := by omega
        have hlt2 : idx.val - N < N := by
          have := idx.isLt
          simp only [List.length_nil, Nat.add_zero] at this
          omega
        simp only [hlt, hge, ↓reduceIte, zero_add]
        dsimp only [oneEach]
        rw [List.getD_append_right _ _ _ _ (by rw [hlen1]; exact hge), hlen1]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2, ↓reduceDIte,
          Option.getD_some, b2z, decide_eq_true_eq, Fin.ext_iff]
    | append_singleton gs g ih =>
      intro t_all ht_all hlen_all hback_all
      have hlen_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
        fun g' hg' => hlen_all g' (List.mem_append_left _ hg')
      have hback_gs : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j := by
        intro j hj i hi
        have h1 := hback_all j (by simp; omega) i
        rw [List.getD_append _ _ _ _ hj] at h1
        exact h1 hi
      generalize ht_def : gs.countP nonlinearGate = t
      obtain ⟨lam, mu, U, W, pW, qW, cW, hspec⟩ := ih t ht_def hlen_gs hback_gs
      have hg_len : g.inputs.length ≤ 2 := hlen_all g (by simp)
      have hg_back : ∀ i ∈ g.inputs, i < N + N + gs.length := by
        intro i hi
        have h1 := hback_all gs.length (by simp) i
        have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
          simp
        rw [hget] at h1
        exact h1 hi
      have hfold_eq : ∀ x y : Fin N,
          ((gs ++ [g]).foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
            (oneEach x y)) =
          let prev := gs.foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
            (oneEach x y)
          prev ++ [g.op.eval (g.inputs.map fun i => prev.getD i false)] := by
        intro x y
        simp [List.foldl_append]
      have hprev_len : ∀ x y : Fin N,
          (gs.foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
            (oneEach x y)).length = N + N + gs.length := by
        intro x y
        rw [wires_length]
        simp [oneEach]
      have hcount : (gs ++ [g]).countP nonlinearGate =
          t + (if nonlinearGate g then 1 else 0) := by
        rw [List.countP_append, ht_def, List.countP_cons, List.countP_nil]
        cases nonlinearGate g <;> simp
      by_cases hnl : nonlinearGate g = true
      · have ht_all_eq : t_all = t + 1 := by
          rw [← ht_all, hcount, hnl]; simp
        subst ht_all_eq
        have hgin2 : g.inputs.length = 2 := by
          dsimp only [nonlinearGate] at hnl
          simp only [Bool.and_eq_true, beq_iff_eq] at hnl
          exact hnl.1
        obtain ⟨i1, i2, hgin⟩ : ∃ i1 i2 : ℕ, g.inputs = [i1, i2] := by
          cases hin : g.inputs with
          | nil => simp [hin] at hgin2
          | cons a rest =>
            cases rest with
            | nil => simp [hin] at hgin2
            | cons b rest2 =>
              cases rest2 with
              | nil => exact ⟨a, b, rfl⟩
              | cons _ _ => simp [hin] at hgin2
        have hi1 : i1 < N + N + gs.length := hg_back i1 (by rw [hgin]; simp)
        have hi2 : i2 < N + N + gs.length := hg_back i2 (by rw [hgin]; simp)
        let idx1 : Fin (N + N + gs.length) := ⟨i1, hi1⟩
        let idx2 : Fin (N + N + gs.length) := ⟨i2, hi2⟩
        obtain ⟨c0, c1, c2, c3, hc3, hpoly⟩ := bool_fun2_poly (fun a b => g.op.eval [a, b])
        have hc3_1 : c3 = 1 := by
          rw [hc3]
          dsimp only [nonlinearGate] at hnl
          simp only [Bool.and_eq_true, beq_iff_eq] at hnl
          rw [hnl.2]
          rfl
        let lam1 : (k : Fin (t + 1)) → Fin k.val → ZMod 2 := fun k =>
          Fin.lastCases (cW idx1) (fun k' => lam k') k
        let mu1 : (k : Fin (t + 1)) → Fin k.val → ZMod 2 := fun k =>
          Fin.lastCases (cW idx2) (fun k' => mu k') k
        let U1 : Fin N → Fin (2 * (t + 1)) → ZMod 2 := fun x =>
          joinVec (U x, (pW idx1 x + c2, pW idx2 x + c1))
        let W1 : Fin N → Fin (2 * (t + 1)) → ZMod 2 := fun y =>
          joinVec (W y, (qW idx1 y, qW idx2 y))
        let pW1 : Fin (N + N + (gs ++ [g]).length) → Fin N → ZMod 2 := fun idx x =>
          if hlt : idx.val < N + N + gs.length then pW ⟨idx.val, hlt⟩ x else c0 + c1 * c2
        let qW1 : Fin (N + N + (gs ++ [g]).length) → Fin N → ZMod 2 := fun idx y =>
          if hlt : idx.val < N + N + gs.length then qW ⟨idx.val, hlt⟩ y else 0
        let cW1 : Fin (N + N + (gs ++ [g]).length) → Fin (t + 1) → ZMod 2 := fun idx k =>
          if hlt : idx.val < N + N + gs.length then
            Fin.lastCases 0 (fun k' => cW ⟨idx.val, hlt⟩ k') k
          else
            Fin.lastCases 1 (fun _ => 0) k
        have hUW_add : ∀ x y : Fin N,
            U1 x + W1 y = joinVec (U x + W y, (pW idx1 x + c2 + qW idx1 y, pW idx2 x + c1 + qW idx2 y)) := by
          intro x y
          ext i
          simp only [Pi.add_apply, U1, W1, joinVec]
          split_ifs <;> simp
        have htri_old : ∀ (x y : Fin N) (k : Fin t),
            triGate lam1 mu1 (U1 x + W1 y) k.castSucc = triGate lam mu (U x + W y) k := by
          intro x y k
          rw [hUW_add]
          dsimp only [triGate]
          refine evalTri_congr (k.val + 1) _ _ ?_ ?_ ?_
          · intro i hi
            have hlt : i < 2 * t := by omega
            simp [joinVec, hlt]
          · intro j hj l
            dsimp only [lam1]
            exact congrFun (Fin.lastCases_castSucc (motive := fun x : Fin (t + 1) => Fin x.val → ZMod 2)
              (⟨j, by omega⟩ : Fin t)) l
          · intro j hj l
            dsimp only [mu1]
            exact congrFun (Fin.lastCases_castSucc (motive := fun x : Fin (t + 1) => Fin x.val → ZMod 2)
              (⟨j, by omega⟩ : Fin t)) l
        have htri_new : ∀ x y : Fin N,
            triGate lam1 mu1 (U1 x + W1 y) (Fin.last t) =
              (pW idx1 x + qW idx1 y + ∑ l : Fin t, cW idx1 l * triGate lam mu (U x + W y) l + c2) *
              (pW idx2 x + qW idx2 y + ∑ l : Fin t, cW idx2 l * triGate lam mu (U x + W y) l + c1) := by
          intro x y
          conv_lhs => dsimp only [triGate]; rw [evalTri.eq_2]; simp only [Fin.val_last]
          have h1 : (U1 x + W1 y) ⟨2 * t, by omega⟩ = pW idx1 x + c2 + qW idx1 y := by
            rw [hUW_add]; simp [joinVec]
          have h2 : (U1 x + W1 y) ⟨2 * t + 1, by omega⟩ = pW idx2 x + c1 + qW idx2 y := by
            rw [hUW_add]; simp [joinVec]
          rw [h1, h2]
          have hs1 : ∑ l : Fin t, lam1 ⟨t, by omega⟩ l * evalTri (t + 1) lam1 mu1 (U1 x + W1 y) (l.val + 1) (by omega) =
              ∑ l : Fin t, cW idx1 l * triGate lam mu (U x + W y) l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            have hlam_last : lam1 ⟨t, by omega⟩ l = cW idx1 l := by
              dsimp only [lam1]
              exact congrFun (Fin.lastCases_last (motive := fun x : Fin (t + 1) => Fin x.val → ZMod 2)) l
            rw [hlam_last]
            congr 1
            exact htri_old x y l
          have hs2 : ∑ l : Fin t, mu1 ⟨t, by omega⟩ l * evalTri (t + 1) lam1 mu1 (U1 x + W1 y) (l.val + 1) (by omega) =
              ∑ l : Fin t, cW idx2 l * triGate lam mu (U x + W y) l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            have hmu_last : mu1 ⟨t, by omega⟩ l = cW idx2 l := by
              dsimp only [mu1]
              exact congrFun (Fin.lastCases_last (motive := fun x : Fin (t + 1) => Fin x.val → ZMod 2)) l
            rw [hmu_last]
            congr 1
            exact htri_old x y l
          rw [hs1, hs2]
          ring
        refine ⟨lam1, mu1, U1, W1, pW1, qW1, cW1, fun x y idx => ?_⟩
        rw [hfold_eq, getD_append_single, hprev_len]
        by_cases hlt : idx.val < N + N + gs.length
        · have hne : idx.val ≠ N + N + gs.length := by omega
          simp only [hne, hlt, ↓reduceIte, ↓reduceDIte, pW1, qW1, cW1]
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          rw [hspec x y ⟨idx.val, hlt⟩]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [htri_old]
        · have heq : idx.val = N + N + gs.length := by
            have := idx.isLt
            simp only [List.length_append, List.length_singleton] at this
            omega
          simp only [pW1, qW1, cW1, hlt, ↓reduceDIte, add_zero]
          simp only [heq, ↓reduceIte]
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, Finset.sum_const_zero,
            zero_add, one_mul, htri_new, hgin, List.map_cons, List.map_nil]
          rw [hpoly, hc3_1, one_mul, hspec x y idx1, hspec x y idx2]
          have hgoal :
              c0 + c1 * (pW idx1 x + qW idx1 y + ∑ k : Fin t, cW idx1 k * triGate lam mu (U x + W y) k) +
                c2 * (pW idx2 x + qW idx2 y + ∑ k : Fin t, cW idx2 k * triGate lam mu (U x + W y) k) +
                (pW idx1 x + qW idx1 y + ∑ k : Fin t, cW idx1 k * triGate lam mu (U x + W y) k) *
                  (pW idx2 x + qW idx2 y + ∑ k : Fin t, cW idx2 k * triGate lam mu (U x + W y) k) =
              c0 + c1 * c2 +
                (pW idx1 x + qW idx1 y + ∑ l : Fin t, cW idx1 l * triGate lam mu (U x + W y) l + c2) *
                  (pW idx2 x + qW idx2 y + ∑ l : Fin t, cW idx2 l * triGate lam mu (U x + W y) l + c1) := by
            generalize (pW idx1 x + qW idx1 y + ∑ k : Fin t, cW idx1 k * triGate lam mu (U x + W y) k) = A
            generalize (pW idx2 x + qW idx2 y + ∑ k : Fin t, cW idx2 k * triGate lam mu (U x + W y) k) = B
            have hcc := z2_add_self (c1 * c2)
            linear_combination -hcc
          exact hgoal
      · have hnlf : nonlinearGate g = false := Bool.eq_false_iff.mpr hnl
        have ht_all_eq : t_all = t := by
          rw [← ht_all, hcount, hnlf]; simp
        clear ht_all
        subst t_all
        have hg_aff : ∃ (pg qg : Fin N → ZMod 2) (cg : Fin t → ZMod 2),
            ∀ x y : Fin N,
              b2z (g.op.eval (g.inputs.map fun i =>
                (gs.foldl (fun w g' => w ++ [g'.op.eval (g'.inputs.map fun j => w.getD j false)])
                  (oneEach x y)).getD i false)) =
                pg x + qg y + ∑ k : Fin t, cg k * triGate lam mu (U x + W y) k := by
          cases hin : g.inputs with
          | nil =>
            refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun _ => 0, fun x y => ?_⟩
            simp
          | cons i1 rest =>
            cases rest with
            | nil =>
              have hi1 : i1 < N + N + gs.length := hg_back i1 (by rw [hin]; simp)
              obtain ⟨c0, c1, haff1⟩ := bool_fun1_affine (fun a => g.op.eval [a])
              refine ⟨fun x => c0 + c1 * pW ⟨i1, hi1⟩ x, fun y => c1 * qW ⟨i1, hi1⟩ y,
                fun k => c1 * cW ⟨i1, hi1⟩ k, fun x y => ?_⟩
              simp only [List.map_cons, List.map_nil, haff1, hspec x y ⟨i1, hi1⟩]
              rw [mul_add, mul_add, Finset.mul_sum]
              have hsum : ∑ k : Fin t, c1 * cW ⟨i1, hi1⟩ k * triGate lam mu (U x + W y) k =
                  ∑ k : Fin t, c1 * (cW ⟨i1, hi1⟩ k * triGate lam mu (U x + W y) k) :=
                Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
              rw [hsum]
              ring
            | cons i2 rest2 =>
              cases rest2 with
              | nil =>
                have hi1 : i1 < N + N + gs.length := hg_back i1 (by rw [hin]; simp)
                have hi2 : i2 < N + N + gs.length := hg_back i2 (by rw [hin]; simp)
                obtain ⟨c0, c1, c2, c3, hc3, hpoly⟩ := bool_fun2_poly (fun a b => g.op.eval [a, b])
                have hc3_0 : c3 = 0 := by
                  rw [hc3]
                  dsimp only [nonlinearGate] at hnlf
                  simp only [hin, List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hnlf
                  rw [hnlf]
                  rfl
                refine ⟨fun x => c0 + c1 * pW ⟨i1, hi1⟩ x + c2 * pW ⟨i2, hi2⟩ x,
                  fun y => c1 * qW ⟨i1, hi1⟩ y + c2 * qW ⟨i2, hi2⟩ y,
                  fun k => c1 * cW ⟨i1, hi1⟩ k + c2 * cW ⟨i2, hi2⟩ k, fun x y => ?_⟩
                simp only [List.map_cons, List.map_nil, hpoly, hc3_0, zero_mul, add_zero,
                  hspec x y ⟨i1, hi1⟩, hspec x y ⟨i2, hi2⟩]
                simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
                ring
              | cons _ _ =>
                simp [hin] at hg_len
        obtain ⟨pg, qg, cg, hgspec⟩ := hg_aff
        refine ⟨lam, mu, U, W,
          fun idx x => if hlt : idx.val < N + N + gs.length then pW ⟨idx.val, hlt⟩ x else pg x,
          fun idx y => if hlt : idx.val < N + N + gs.length then qW ⟨idx.val, hlt⟩ y else qg y,
          fun idx k => if hlt : idx.val < N + N + gs.length then cW ⟨idx.val, hlt⟩ k else cg k,
          fun x y idx => ?_⟩
        rw [hfold_eq, getD_append_single, hprev_len]
        by_cases hlt : idx.val < N + N + gs.length
        · have hne : idx.val ≠ N + N + gs.length := by omega
          simp only [hne, hlt, ↓reduceIte, ↓reduceDIte]
          exact hspec x y ⟨idx.val, hlt⟩
        · have heq : idx.val = N + N + gs.length := by
            have := idx.isLt
            simp only [List.length_append, List.length_singleton] at this
            omega
          simp only [hlt, ↓reduceDIte]
          simp only [heq, ↓reduceIte]
          exact hgspec x y
  have hback' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j :=
    hback
  obtain ⟨lam, mu, U, W, pW, qW, cW, hspec⟩ := hgen C.gates (C.gates.countP nonlinearGate) rfl hlen hback'
  by_cases hout : C.output < N + N + C.gates.length
  · refine ⟨lam, mu, U, W, pW ⟨C.output, hout⟩, qW ⟨C.output, hout⟩, cW ⟨C.output, hout⟩, fun x y => ?_⟩
    exact hspec x y ⟨C.output, hout⟩
  · refine ⟨lam, mu, U, W, fun _ => 0, fun _ => 0, fun _ => 0, fun x y => ?_⟩
    simp only [Circuit.eval, Circuit.wires, zero_mul, Finset.sum_const_zero, add_zero]
    rw [List.getD_eq_default _ _ (by rw [wires_length]; simp only [oneEach, List.length_append, List.length_ofFn]; omega)]
    rfl

lemma rank_le_fourierSupp {N t : ℕ}
    (U W : Fin N → Fin (2 * t) → ZMod 2)
    (pOut qOut : Fin N → ZMod 2)
    (F : (Fin (2 * t) → ZMod 2) → ZMod 2)
    (P : Fin N → Fin N → Bool)
    (hP : ∀ x y : Fin N, b2z (P x y) = pOut x + qOut y + F (U x + W y)) :
    (Matrix.of fun x y : Fin N => pm (P x y)).rank ≤ (fourierSupp F).card := by
  let M : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun x y => pm (P x y)
  let S := fourierSupp F
  let L2 : (Fin N → ℝ) →ₗ[ℝ] ({ ω // ω ∈ S } → ℝ) :=
    { toFun := fun v ω =>
        ∑ y : Fin N, ((4 ^ t : ℝ)⁻¹ * fourierCoeff F ω.1 * pmZ2 (qOut y) * chi ω.1 (W y)) * v y
      map_add' := fun v1 v2 => by
        ext ω
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        ext ω
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring }
  let L1 : ({ ω // ω ∈ S } → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    { toFun := fun c x => ∑ ω : { ω // ω ∈ S }, (pmZ2 (pOut x) * chi ω.1 (U x)) * c ω
      map_add' := fun c1 c2 => by
        ext x
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => by ring }
  have hcomp : M.mulVecLin = L1.comp L2 := by
    apply LinearMap.ext
    intro v
    ext x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply,
      LinearMap.comp_apply, L1, L2, LinearMap.coe_mk, AddHom.coe_mk]
    have hfactor : ∀ y : Fin N,
        pm (P x y) = ∑ ω : { ω // ω ∈ S },
          (pmZ2 (pOut x) * chi ω.1 (U x)) *
            ((4 ^ t : ℝ)⁻¹ * fourierCoeff F ω.1 * pmZ2 (qOut y) * chi ω.1 (W y)) := by
      intro y
      rw [pm_eq_pmZ2, hP x y, pmZ2_add, pmZ2_add]
      have h4 : (2 ^ (2 * t) : ℝ) = (4 ^ t : ℝ) := by
        rw [pow_mul]
        norm_num
      have h4ne : (4 ^ t : ℝ) ≠ 0 := pow_ne_zero t (by norm_num)
      have hinv := fourier_inv (fun d : Fin (2 * t) → ZMod 2 => pmZ2 (F d)) (U x + W y)
      rw [h4] at hinv
      have hF : pmZ2 (F (U x + W y)) =
          (4 ^ t : ℝ)⁻¹ * ∑ ω ∈ S, fourierCoeff F ω * chi ω (U x + W y) := by
        have hdrop : ∑ ω : Fin (2 * t) → ZMod 2, fourierCoeff F ω * chi ω (U x + W y) =
            ∑ ω ∈ S, fourierCoeff F ω * chi ω (U x + W y) := by
          dsimp only [S, fourierSupp]
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => fourierCoeff F ω ≠ 0)]
          have h0 : ∑ ω ∈ Finset.univ.filter (fun ω => ¬ fourierCoeff F ω ≠ 0),
              fourierCoeff F ω * chi ω (U x + W y) = 0 := by
            refine Finset.sum_eq_zero fun ω hω => ?_
            have hfc0 : fourierCoeff F ω = 0 := not_not.mp (Finset.mem_filter.mp hω).2
            simp [hfc0]
          rw [h0, add_zero]
        rw [← hdrop]
        dsimp only [fourierCoeff]
        rw [hinv, inv_mul_cancel_left₀ h4ne]
      rw [hF, Finset.mul_sum]
      trans ∑ ω ∈ S,
          (pmZ2 (pOut x) * chi ω (U x)) *
            ((4 ^ t : ℝ)⁻¹ * fourierCoeff F ω * pmZ2 (qOut y) * chi ω (W y))
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [chi_add_right]
        ring
      · rw [← Finset.sum_attach S]
        refine Finset.sum_bij (fun ω _ => ω) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => h) (fun ω _ => ⟨ω, Finset.mem_attach _ _, rfl⟩) (fun _ _ => rfl)
    simp_rw [hfactor, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range L1 := by
    rw [hcomp]
    exact LinearMap.range_comp_le_range L2 L1
  calc
    M.rank = Module.finrank ℝ (LinearMap.range M.mulVecLin) := rfl
    _ ≤ Module.finrank ℝ (LinearMap.range L1) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ ({ ω // ω ∈ S } → ℝ) := LinearMap.finrank_range_le L1
    _ = S.card := by rw [Module.finrank_pi, Fintype.card_coe]

lemma box_parity_ineq : ∀ e11 e12 e21 e22 : Bool,
    (if xor e11 e21 then 1 else 0) + (if xor e12 e22 then 1 else 0) +
    (if xor e11 e12 then 1 else 0) + (if xor e21 e22 then 1 else 0) ≤
    (if e11 then 1 else 0) + (if e12 then 1 else 0) +
    (if e21 then 1 else 0) + (if e22 then 1 else 0) + 2 := by
  decide

lemma signed_sample_not_both_noninj {s : ℕ} (hs : 2 ≤ s)
    (H : Fin (4 ^ s) → Fin (4 ^ s) → Bool)
    (hH : ∀ a b : Fin (4 ^ s), a ≠ b →
      2 * ((Finset.univ : Finset (Fin (4 ^ s))).filter (fun v => H a v ≠ H b v)).card = 4 ^ s)
    (row col : Fin (4 ^ s) → (Fin (2 * s) → ZMod 2))
    (Q R : Fin (4 ^ s) → Bool) :
    let N := 4 ^ s
    let P := fun x y : Fin N => xor (xor (Q x) (R y)) (decide ((∑ b : Fin (2 * s), row x b * col y b) = 1))
    let e := ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ P i j)).card
    e + 2 < N → Function.Injective row ∨ Function.Injective col := by
  intro N P e he
  have hNpos : 0 < N := pow_pos (by decide) s
  by_contra hboth
  have hnr : ¬ Function.Injective row := fun h => hboth (Or.inl h)
  have hnc : ¬ Function.Injective col := fun h => hboth (Or.inr h)
  have hex_r : ∃ x1 x2 : Fin N, x1 ≠ x2 ∧ row x1 = row x2 := by
    by_contra hall
    apply hnr
    intro a b hab
    by_contra hne
    exact hall ⟨a, b, hne, hab⟩
  have hex_c : ∃ y1 y2 : Fin N, y1 ≠ y2 ∧ col y1 = col y2 := by
    by_contra hall
    apply hnc
    intro a b hab
    by_contra hne
    exact hall ⟨a, b, hne, hab⟩
  obtain ⟨x1, x2, hxne, hreq⟩ := hex_r
  obtain ⟨y1, y2, hyne, hceq⟩ := hex_c
  let errSet : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => H p.1 p.2 ≠ P p.1 p.2)
  have he_eq : e = errSet.card := by
    dsimp only [e, errSet]
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.card_bij (fun j _ => (i, j)) ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hj).2⟩, rfl⟩
    · intro j1 _ j2 _ h; exact (Prod.mk.inj h).2
    · intro ⟨i', j⟩ hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hi'⟩
      simp only at hi'
      subst hi'
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp1).2⟩, rfl⟩
  let A_row : Finset (Fin N × Fin N) := errSet.filter (fun p => (p.1 = x1 ∨ p.1 = x2) ∧ p.2 ≠ y1 ∧ p.2 ≠ y2)
  let A_col : Finset (Fin N × Fin N) := errSet.filter (fun p => (p.1 ≠ x1 ∧ p.1 ≠ x2) ∧ (p.2 = y1 ∨ p.2 = y2))
  let A_box : Finset (Fin N × Fin N) := errSet.filter (fun p => (p.1 = x1 ∨ p.1 = x2) ∧ (p.2 = y1 ∨ p.2 = y2))
  have hsub_u : A_row ∪ A_col ∪ A_box ⊆ errSet := by
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h3
    · rcases Finset.mem_union.mp h1 with h1' | h2
      · exact (Finset.mem_filter.mp h1').1
      · exact (Finset.mem_filter.mp h2).1
    · exact (Finset.mem_filter.mp h3).1
  have hdisj1 : Disjoint A_row A_col := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have ha := (Finset.mem_filter.mp h1).2.1
    have hb := (Finset.mem_filter.mp h2).2.1
    rcases ha with rfl | rfl
    · exact hb.1 rfl
    · exact hb.2 rfl
  have hdisj2 : Disjoint (A_row ∪ A_col) A_box := by
    rw [Finset.disjoint_left]
    intro p h1 h3
    have hc := (Finset.mem_filter.mp h3).2
    rcases Finset.mem_union.mp h1 with ha | hb
    · have ha2 := (Finset.mem_filter.mp ha).2.2
      rcases hc.2 with rfl | rfl
      · exact ha2.1 rfl
      · exact ha2.2 rfl
    · have hb1 := (Finset.mem_filter.mp hb).2.1
      rcases hc.1 with rfl | rfl
      · exact hb1.1 rfl
      · exact hb1.2 rfl
  have he_ge : A_row.card + A_col.card + A_box.card ≤ e := by
    rw [he_eq]
    calc
      A_row.card + A_col.card + A_box.card
          = (A_row ∪ A_col ∪ A_box).card := by
            rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
      _ ≤ errSet.card := Finset.card_le_card hsub_u
  let b1 : Bool := decide (xor (H x1 y1) (H x2 y1) ≠ xor (Q x1) (Q x2))
  let b2 : Bool := decide (xor (H x1 y2) (H x2 y2) ≠ xor (Q x1) (Q x2))
  let c1 : Bool := decide (xor (H x1 y1) (H x1 y2) ≠ xor (R y1) (R y2))
  let c2 : Bool := decide (xor (H x2 y1) (H x2 y2) ≠ xor (R y1) (R y2))
  have hrow_dis :
      2 * ((Finset.univ : Finset (Fin N)).filter (fun y => xor (H x1 y) (H x2 y) ≠ xor (Q x1) (Q x2))).card = N := by
    have h1 := hH x1 x2 hxne
    cases hq : xor (Q x1) (Q x2)
    · have heqset : (Finset.univ : Finset (Fin N)).filter (fun y => xor (H x1 y) (H x2 y) ≠ false) =
          (Finset.univ : Finset (Fin N)).filter (fun y => H x1 y ≠ H x2 y) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
        cases H x1 y <;> cases H x2 y <;> decide
      rw [heqset]
      exact h1
    · have hcomp := card_filter_add_card_filter_not
        (Finset.univ : Finset (Fin N)) (fun y => H x1 y ≠ H x2 y)
      have heqset : (Finset.univ : Finset (Fin N)).filter (fun y => xor (H x1 y) (H x2 y) ≠ true) =
          (Finset.univ : Finset (Fin N)).filter (fun y => ¬ H x1 y ≠ H x2 y) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
        cases H x1 y <;> cases H x2 y <;> decide
      rw [heqset]
      simp only [Finset.card_univ, Fintype.card_fin] at hcomp
      change ((Finset.univ : Finset (Fin N)).filter (fun y => H x1 y ≠ H x2 y)).card +
        ((Finset.univ : Finset (Fin N)).filter (fun y => ¬ H x1 y ≠ H x2 y)).card = N at hcomp
      omega
  have hcol_dis :
      2 * ((Finset.univ : Finset (Fin N)).filter (fun x => xor (H x y1) (H x y2) ≠ xor (R y1) (R y2))).card = N := by
    have h1 := hadamard_swap hNpos hH y1 y2 hyne
    cases hr : xor (R y1) (R y2)
    · have heqset : (Finset.univ : Finset (Fin N)).filter (fun x => xor (H x y1) (H x y2) ≠ false) =
          (Finset.univ : Finset (Fin N)).filter (fun x => H x y1 ≠ H x y2) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
        cases H x y1 <;> cases H x y2 <;> decide
      rw [heqset]
      exact h1
    · have hcomp := card_filter_add_card_filter_not
        (Finset.univ : Finset (Fin N)) (fun x => H x y1 ≠ H x y2)
      have heqset : (Finset.univ : Finset (Fin N)).filter (fun x => xor (H x y1) (H x y2) ≠ true) =
          (Finset.univ : Finset (Fin N)).filter (fun x => ¬ H x y1 ≠ H x y2) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
        cases H x y1 <;> cases H x y2 <;> decide
      rw [heqset]
      simp only [Finset.card_univ, Fintype.card_fin] at hcomp
      change 2 * ((Finset.univ : Finset (Fin N)).filter (fun x => H x y1 ≠ H x y2)).card = N at h1
      change ((Finset.univ : Finset (Fin N)).filter (fun x => H x y1 ≠ H x y2)).card +
        ((Finset.univ : Finset (Fin N)).filter (fun x => ¬ H x y1 ≠ H x y2)).card = N at hcomp
      omega
  have hArow_ge :
      ((Finset.univ : Finset (Fin N)).filter (fun y => xor (H x1 y) (H x2 y) ≠ xor (Q x1) (Q x2))).card ≤
        A_row.card + (if b1 then 1 else 0) + (if b2 then 1 else 0) := by
    let D := (Finset.univ : Finset (Fin N)).filter (fun y => xor (H x1 y) (H x2 y) ≠ xor (Q x1) (Q x2))
    let D' := D.filter (fun y => y ≠ y1 ∧ y ≠ y2)
    have hD_le : D.card ≤ D'.card + (if b1 then 1 else 0) + (if b2 then 1 else 0) := by
      let S1 : Finset (Fin N) := if b1 then {y1} else ∅
      let S2 : Finset (Fin N) := if b2 then {y2} else ∅
      have hsub : D ⊆ D' ∪ S1 ∪ S2 := by
        intro y hy
        by_cases hy1 : y = y1
        · subst hy1
          have hb1 : b1 = true := decide_eq_true (Finset.mem_filter.mp hy).2
          simp [S1, hb1]
        · by_cases hy2 : y = y2
          · subst hy2
            have hb2 : b2 = true := decide_eq_true (Finset.mem_filter.mp hy).2
            simp [S2, hb2]
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hy, hy1, hy2⟩))
      calc
        D.card ≤ (D' ∪ S1 ∪ S2).card := Finset.card_le_card hsub
        _ ≤ (D' ∪ S1).card + S2.card := Finset.card_union_le _ _
        _ ≤ D'.card + S1.card + S2.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = D'.card + (if b1 then 1 else 0) + (if b2 then 1 else 0) := by
          dsimp only [S1, S2]
          cases b1 <;> cases b2 <;> simp
    have hD'_le : D'.card ≤ A_row.card := by
      have hsub : D' ⊆ A_row.image Prod.snd := by
        intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyD, hy1, hy2⟩
        have hdis : xor (H x1 y) (H x2 y) ≠ xor (Q x1) (Q x2) := (Finset.mem_filter.mp hyD).2
        have hPeq : xor (P x1 y) (P x2 y) = xor (Q x1) (Q x2) := by
          dsimp only [P]
          rw [hreq]
          cases Q x1 <;> cases Q x2 <;> cases R y <;>
            cases decide ((∑ b : Fin (2 * s), row x2 b * col y b) = 1) <;> decide
        by_cases he1 : H x1 y ≠ P x1 y
        · exact Finset.mem_image.mpr ⟨(x1, y), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1⟩, Or.inl rfl, hy1, hy2⟩, rfl⟩
        · have he2 : H x2 y ≠ P x2 y := by
            intro h2
            have h1' : H x1 y = P x1 y := not_not.mp he1
            rw [h1', h2, hPeq] at hdis
            exact hdis rfl
          exact Finset.mem_image.mpr ⟨(x2, y), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2⟩, Or.inr rfl, hy1, hy2⟩, rfl⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    exact le_trans hD_le (by omega)
  have hAcol_ge :
      ((Finset.univ : Finset (Fin N)).filter (fun x => xor (H x y1) (H x y2) ≠ xor (R y1) (R y2))).card ≤
        A_col.card + (if c1 then 1 else 0) + (if c2 then 1 else 0) := by
    let D := (Finset.univ : Finset (Fin N)).filter (fun x => xor (H x y1) (H x y2) ≠ xor (R y1) (R y2))
    let D' := D.filter (fun x => x ≠ x1 ∧ x ≠ x2)
    have hD_le : D.card ≤ D'.card + (if c1 then 1 else 0) + (if c2 then 1 else 0) := by
      let S1 : Finset (Fin N) := if c1 then {x1} else ∅
      let S2 : Finset (Fin N) := if c2 then {x2} else ∅
      have hsub : D ⊆ D' ∪ S1 ∪ S2 := by
        intro x hx
        by_cases hx1 : x = x1
        · subst hx1
          have hc1 : c1 = true := decide_eq_true (Finset.mem_filter.mp hx).2
          simp [S1, hc1]
        · by_cases hx2 : x = x2
          · subst hx2
            have hc2 : c2 = true := decide_eq_true (Finset.mem_filter.mp hx).2
            simp [S2, hc2]
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hx, hx1, hx2⟩))
      calc
        D.card ≤ (D' ∪ S1 ∪ S2).card := Finset.card_le_card hsub
        _ ≤ (D' ∪ S1).card + S2.card := Finset.card_union_le _ _
        _ ≤ D'.card + S1.card + S2.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = D'.card + (if c1 then 1 else 0) + (if c2 then 1 else 0) := by
          dsimp only [S1, S2]
          cases c1 <;> cases c2 <;> simp
    have hD'_le : D'.card ≤ A_col.card := by
      have hsub : D' ⊆ A_col.image Prod.fst := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxD, hx1, hx2⟩
        have hdis : xor (H x y1) (H x y2) ≠ xor (R y1) (R y2) := (Finset.mem_filter.mp hxD).2
        have hPeq : xor (P x y1) (P x y2) = xor (R y1) (R y2) := by
          dsimp only [P]
          rw [hceq]
          cases Q x <;> cases R y1 <;> cases R y2 <;>
            cases decide ((∑ b : Fin (2 * s), row x b * col y2 b) = 1) <;> decide
        by_cases he1 : H x y1 ≠ P x y1
        · exact Finset.mem_image.mpr ⟨(x, y1), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1⟩, ⟨hx1, hx2⟩, Or.inl rfl⟩, rfl⟩
        · have he2 : H x y2 ≠ P x y2 := by
            intro h2
            have h1' : H x y1 = P x y1 := not_not.mp he1
            rw [h1', h2, hPeq] at hdis
            exact hdis rfl
          exact Finset.mem_image.mpr ⟨(x, y2), Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2⟩, ⟨hx1, hx2⟩, Or.inr rfl⟩, rfl⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    exact le_trans hD_le (by omega)
  let e11 : Bool := decide (H x1 y1 ≠ P x1 y1)
  let e12 : Bool := decide (H x1 y2 ≠ P x1 y2)
  let e21 : Bool := decide (H x2 y1 ≠ P x2 y1)
  let e22 : Bool := decide (H x2 y2 ≠ P x2 y2)
  have hbox_card : A_box.card =
      (if e11 then 1 else 0) + (if e12 then 1 else 0) +
      (if e21 then 1 else 0) + (if e22 then 1 else 0) := by
    have h4 : A_box = (({(x1, y1), (x1, y2), (x2, y1), (x2, y2)} : Finset (Fin N × Fin N))).filter
        (fun p => H p.1 p.2 ≠ P p.1 p.2) := by
      ext ⟨x, y⟩
      simp only [A_box, errSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      tauto
    rw [h4]
    have hne1 : (x1, y1) ≠ (x1, y2) := fun h => hyne (Prod.mk.inj h).2
    have hne2 : (x1, y1) ≠ (x2, y1) := fun h => hxne (Prod.mk.inj h).1
    have hne3 : (x1, y1) ≠ (x2, y2) := fun h => hxne (Prod.mk.inj h).1
    have hne4 : (x1, y2) ≠ (x2, y1) := fun h => hxne (Prod.mk.inj h).1
    have hne5 : (x1, y2) ≠ (x2, y2) := fun h => hxne (Prod.mk.inj h).1
    have hne6 : (x2, y1) ≠ (x2, y2) := fun h => hyne (Prod.mk.inj h).2
    simp only [Finset.filter_insert, Finset.filter_singleton]
    have hcard_ins : ∀ (a : Fin N × Fin N) (S : Finset (Fin N × Fin N)), a ∉ S →
        (if H a.1 a.2 ≠ P a.1 a.2 then insert a S else S).card =
          (if decide (H a.1 a.2 ≠ P a.1 a.2) then 1 else 0) + S.card := by
      intro a S ha
      by_cases h : H a.1 a.2 ≠ P a.1 a.2
      · simp [h, Finset.card_insert_of_notMem ha, Nat.add_comm]
      · simp [h]
    let S4 : Finset (Fin N × Fin N) := if H x2 y2 ≠ P x2 y2 then {(x2, y2)} else ∅
    have hm1 : (x1, y1) ∉ (if H x1 y2 ≠ P x1 y2 then insert (x1, y2)
        (if H x2 y1 ≠ P x2 y1 then insert (x2, y1) S4 else S4)
        else if H x2 y1 ≠ P x2 y1 then insert (x2, y1) S4 else S4) := by
      dsimp only [S4]
      split_ifs <;> simp [hne1, hne2, hne3]
    have hm2 : (x1, y2) ∉ (if H x2 y1 ≠ P x2 y1 then insert (x2, y1) S4 else S4) := by
      dsimp only [S4]
      split_ifs <;> simp [hne4, hne5]
    have hm3 : (x2, y1) ∉ S4 := by
      dsimp only [S4]
      split_ifs <;> simp [hne6]
    rw [hcard_ins _ _ hm1, hcard_ins _ _ hm2, hcard_ins _ _ hm3]
    dsimp only [S4, e11, e12, e21, e22]
    by_cases h22 : H x2 y2 ≠ P x2 y2 <;> simp [h22] <;> omega
  have hb1_eq : b1 = xor e11 e21 := by
    dsimp only [b1, e11, e21, P]
    simp only [hreq]
    exact decide_ne_xor _ _ _ _ _ _
  have hb2_eq : b2 = xor e12 e22 := by
    dsimp only [b2, e12, e22, P]
    simp only [hreq]
    exact decide_ne_xor _ _ _ _ _ _
  have hc1_eq : c1 = xor e11 e12 := by
    dsimp only [c1, e11, e12, P]
    simp only [hceq]
    exact decide_ne_xor_col _ _ _ _ _ _
  have hc2_eq : c2 = xor e21 e22 := by
    dsimp only [c2, e21, e22, P]
    simp only [hceq]
    exact decide_ne_xor_col _ _ _ _ _ _
  have hbox := box_parity_ineq e11 e12 e21 e22
  rw [← hb1_eq, ← hb2_eq, ← hc1_eq, ← hc2_eq, ← hbox_card] at hbox
  omega

lemma signed_sampling_gap_col_bij {s : ℕ}
    (H : Fin (4 ^ s) → Fin (4 ^ s) → Bool)
    (hH : ∀ a b : Fin (4 ^ s), a ≠ b →
      2 * ((Finset.univ : Finset (Fin (4 ^ s))).filter (fun v => H a v ≠ H b v)).card = 4 ^ s)
    (row : Fin (4 ^ s) → (Fin (2 * s) → ZMod 2))
    (col : Fin (4 ^ s) ≃ (Fin (2 * s) → ZMod 2))
    (Q R : Fin (4 ^ s) → Bool) :
    let N := 4 ^ s
    let V := Fin (2 * s) → ZMod 2
    let P := fun x y : Fin N => xor (xor (Q x) (R y)) (decide ((∑ b : Fin (2 * s), row x b * col y b) = 1))
    let e := ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ P i j)).card
    e < N →
    (∃ (rowH colH : Fin N ≃ V) (QH RH : Fin N → Bool),
      ∀ i j, H i j = xor (xor (QH i) (RH j)) (decide ((∑ b : Fin (2 * s), rowH i b * colH j b) = 1))) ∧
    (e = 0 ∨ (2 * e = N ∧ ∃ i j : Fin N, i ≠ j ∧ ∃ flip : Bool, ∀ x y,
      P x y = if x = i then xor flip (H j y) else H x y)) := by
  intro N V P e he
  have hNpos : 0 < N := pow_pos (by decide) s
  have hN2s : 2 ^ (2 * s) = N := by
    dsimp only [N]
    rw [pow_mul]
    norm_num
  have hN2sR : (2 ^ (2 * s) : ℝ) = (N : ℝ) := by exact_mod_cast hN2s
  let H' : Fin N → V → Bool := fun x w => xor (H x (col.symm w)) (R (col.symm w))
  let P' : Fin N → V → Bool := fun x w => xor (Q x) (decide ((∑ b : Fin (2 * s), row x b * w b) = 1))
  have hHP_iff : ∀ (x : Fin N) (w : V), (H' x w ≠ P' x w) ↔ (H x (col.symm w) ≠ P x (col.symm w)) := by
    intro x w
    simp only [H', P', P, Equiv.apply_symm_apply]
    cases H x (col.symm w) <;> cases R (col.symm w) <;> cases Q x <;>
      cases decide ((∑ b : Fin (2 * s), row x b * w b) = 1) <;> decide
  let ex : Fin N → ℕ := fun x => ((Finset.univ : Finset V).filter (fun w => H' x w ≠ P' x w)).card
  have hex_eq : ∀ x : Fin N,
      ex x = ((Finset.univ : Finset (Fin N)).filter (fun j => H x j ≠ P x j)).card := by
    intro x
    refine Finset.card_bij (fun w _ => col.symm w) ?_ ?_ ?_
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hHP_iff x w).mp (Finset.mem_filter.mp hw).2⟩
    · intro w1 _ w2 _ h; exact col.symm.injective h
    · intro j hj
      refine ⟨col j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, col.symm_apply_apply j⟩
      rw [hHP_iff, col.symm_apply_apply]
      exact (Finset.mem_filter.mp hj).2
  have he_sum : e = ∑ x : Fin N, ex x := by
    dsimp only [e]
    exact Finset.sum_congr rfl fun x _ => (hex_eq x).symm
  have hH'_orth : ∀ a b : Fin N, a ≠ b →
      ∑ w : V, pm (H' a w) * pm (H' b w) = 0 := by
    intro a b hab
    trans ∑ j : Fin N, pm (H a j) * pm (H b j)
    · rw [← Equiv.sum_comp col.symm]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [H', pm_xor]
      have hsq := pm_mul_self (R (col.symm w))
      linear_combination (pm (H a (col.symm w)) * pm (H b (col.symm w))) * hsq
    · rw [hadamard_orth_rows hH a b]
      simp [hab]
  let D : Finset (Fin N) := Finset.univ.filter (fun x => 0 < ex x)
  let Dc : Finset (Fin N) := Dᶜ
  have hDc_eq : ∀ x ∈ Dc, ∀ w : V, H' x w = P' x w := by
    intro x hx w
    have h0 : ex x = 0 := by
      have hnot : ¬ 0 < ex x := by
        have := Finset.mem_compl.mp hx
        simpa [D] using this
      omega
    by_contra hne
    have hpos : 0 < ex x := Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hne⟩⟩
    omega
  have hrow_inj_Dc : ∀ x1 ∈ Dc, ∀ x2 ∈ Dc, row x1 = row x2 → x1 = x2 := by
    intro x1 hx1 x2 hx2 hreq
    by_contra hne
    have horth := hH'_orth x1 x2 hne
    have hval : ∑ w : V, pm (H' x1 w) * pm (H' x2 w) = pm (Q x1) * pm (Q x2) * (N : ℝ) := by
      trans ∑ w : V, pm (Q x1) * pm (Q x2)
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [hDc_eq x1 hx1 w, hDc_eq x2 hx2 w]
        simp only [P', pm_xor, hreq]
        have hsq := pm_mul_self (decide ((∑ b : Fin (2 * s), row x2 b * w b) = 1))
        linear_combination (pm (Q x1) * pm (Q x2)) * hsq
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
          hN2s, nsmul_eq_mul, mul_comm]
    rw [hval] at horth
    have hne0 : pm (Q x1) * pm (Q x2) * (N : ℝ) ≠ 0 := by
      have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos)
      have h1 : pm (Q x1) ≠ 0 := by cases Q x1 <;> norm_num [pm]
      have h2 : pm (Q x2) ≠ 0 := by cases Q x2 <;> norm_num [pm]
      exact mul_ne_zero (mul_ne_zero h1 h2) hNne
    exact hne0 horth
  let U0 : Finset V := Dc.image row
  let W : Finset V := U0ᶜ
  have hU0_card : U0.card = Dc.card := Finset.card_image_of_injOn (fun a ha b hb h => hrow_inj_Dc a ha b hb h)
  have hW_card : W.card = D.card := by
    have h1 : W.card = Fintype.card V - U0.card := Finset.card_compl U0
    have h2 : Dc.card = N - D.card := by
      simpa [Dc] using Finset.card_compl D
    have hV : Fintype.card V = N := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
    have hDle : D.card ≤ N := by simpa using Finset.card_le_univ D
    omega
  let c : Fin N → V → ℝ := fun x u => ∑ w : V, pm (H' x w) * chi u w
  have hc_zero_U0 : ∀ x ∈ D, ∀ u ∈ U0, c x u = 0 := by
    intro x hx u hu
    rcases Finset.mem_image.mp hu with ⟨x', hx', rfl⟩
    have hne : x ≠ x' := by
      intro heq
      subst heq
      exact (Finset.mem_compl.mp hx') hx
    have horth := hH'_orth x x' hne
    have hrel : ∑ w : V, pm (H' x w) * pm (H' x' w) = pm (Q x') * c x (row x') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hDc_eq x' hx' w]
      simp only [P', pm_xor, chi, pmZ2_eq_pm, z2b]
      ring
    rw [hrel] at horth
    have hqne : pm (Q x') ≠ 0 := by cases Q x' <;> norm_num [pm]
    exact (mul_eq_zero.mp horth).resolve_left hqne
  have hc_err : ∀ x : Fin N, pm (Q x) * c x (row x) = (N : ℝ) - 2 * (ex x : ℝ) := by
    intro x
    have h1 : pm (Q x) * c x (row x) = ∑ w : V, pm (H' x w) * pm (P' x w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [P', pm_xor, chi, pmZ2_eq_pm, z2b]
      ring
    rw [h1]
    have hterm : ∀ w : V, pm (H' x w) * pm (P' x w) = if H' x w ≠ P' x w then (-1 : ℝ) else 1 := by
      intro w
      cases H' x w <;> cases P' x w <;> norm_num [pm]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcomp := card_filter_add_card_filter_not
      (Finset.univ : Finset V) (fun w => H' x w ≠ P' x w)
    have hVcard : (Finset.univ : Finset V).card = N := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
    rw [hVcard] at hcomp
    have hnot_card : (((Finset.univ : Finset V).filter (fun w => ¬ H' x w ≠ P' x w)).card : ℝ) =
        (N : ℝ) - (ex x : ℝ) := by
      have : ((Finset.univ : Finset V).filter (fun w => ¬ H' x w ≠ P' x w)).card + ex x = N := by
        dsimp only [ex]; omega
      have hR : (((Finset.univ : Finset V).filter (fun w => ¬ H' x w ≠ P' x w)).card : ℝ) + (ex x : ℝ) = (N : ℝ) := by
        exact_mod_cast this
      linarith
    rw [hnot_card]
    change (ex x : ℝ) * (-1) + ((N : ℝ) - (ex x : ℝ)) * 1 = (N : ℝ) - 2 * (ex x : ℝ)
    ring
  let D1 : Finset (Fin N) := D.filter (fun x => row x ∈ U0)
  let D2 : Finset (Fin N) := D.filter (fun x => row x ∉ U0)
  have hD_split : D = D1 ∪ D2 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, D1, D2]
    tauto
  have hD_disj : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hD_card : D.card = D1.card + D2.card := by
    rw [hD_split, Finset.card_union_of_disjoint hD_disj]
  have he_D : e = ∑ x ∈ D1, ex x + ∑ x ∈ D2, ex x := by
    rw [he_sum, ← Finset.sum_union hD_disj, ← hD_split]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => 0 < ex x)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ 0 < ex x), ex x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have := (Finset.mem_filter.mp hx).2
      omega
    rw [h0, add_zero]
  have hD1_ex : ∀ x ∈ D1, 2 * ex x = N := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxD, hxU0⟩
    have h0 := hc_zero_U0 x hxD (row x) hxU0
    have herr := hc_err x
    rw [h0, mul_zero] at herr
    have hR : (2 * ex x : ℝ) = (N : ℝ) := by linarith
    have hR' : ((2 * ex x : ℕ) : ℝ) = (N : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]; exact hR
    exact Nat.cast_injective hR'
  have hD2_ex : ∀ x ∈ D2, N ≤ D.card * ex x := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxD, hxnotU0⟩
    have hxW : row x ∈ W := Finset.mem_compl.mpr hxnotU0
    have hex_pos : 0 < ex x := (Finset.mem_filter.mp hxD).2
    let gx : V → ℝ := fun w => if H' x w ≠ P' x w then 1 else 0
    have hgx_sq : ∑ w : V, (gx w) ^ 2 = (ex x : ℝ) := by
      have h1 : ∀ w : V, (gx w) ^ 2 = if H' x w ≠ P' x w then (1 : ℝ) else 0 := by
        intro w; dsimp only [gx]; split_ifs <;> norm_num
      simp_rw [h1, Finset.sum_boole]
      rfl
    let T : Finset V := W.image (fun u => u + row x)
    have hT_card : T.card ≤ D.card := by
      rw [← hW_card]
      exact Finset.card_image_le
    have hhat_zero : ∀ v : V, v ∉ T → ∑ w : V, gx w * chi v w = 0 := by
      intro v hv
      have hgx_eq : ∀ w : V, 2 * gx w = 1 - pm (H' x w) * pm (P' x w) := by
        intro w
        dsimp only [gx]
        cases H' x w <;> cases P' x w <;> norm_num [pm]
      have h2sum : 2 * (∑ w : V, gx w * chi v w) =
          (∑ w : V, chi v w) - pm (Q x) * c x (row x + v) := by
        rw [Finset.mul_sum]
        trans ∑ w : V, (chi v w - pm (Q x) * (pm (H' x w) * chi (row x + v) w))
        · refine Finset.sum_congr rfl fun w _ => ?_
          have h1 : 2 * (gx w * chi v w) = (2 * gx w) * chi v w := by ring
          rw [h1, hgx_eq w, chi_add_left]
          have hP' : pm (P' x w) = pm (Q x) * chi (row x) w := by
            simp only [P', pm_xor, chi, pmZ2_eq_pm, z2b]
          rw [hP']
          ring
        · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hv_ne0 : v ≠ 0 := by
        intro hv0
        apply hv
        rw [hv0]
        refine Finset.mem_image.mpr ⟨row x, hxW, ?_⟩
        ext i; exact z2_add_self _
      have hrv_U0 : row x + v ∈ U0 := by
        by_contra hnot
        have hrW : row x + v ∈ W := Finset.mem_compl.mpr hnot
        apply hv
        refine Finset.mem_image.mpr ⟨row x + v, hrW, ?_⟩
        ext i
        change (row x i + v i) + row x i = v i
        rw [add_comm (row x i) (v i), add_assoc, z2_add_self, add_zero]
      rw [sum_chi] at h2sum
      simp only [hv_ne0, ↓reduceIte, hc_zero_U0 x hxD (row x + v) hrv_U0, mul_zero, sub_zero] at h2sum
      linarith
    have hhat_bound : ∀ v : V, (∑ w : V, gx w * chi v w) ^ 2 ≤ (ex x : ℝ) ^ 2 := by
      intro v
      have habs : |∑ w : V, gx w * chi v w| ≤ (ex x : ℝ) := by
        calc
          |∑ w : V, gx w * chi v w| ≤ ∑ w : V, |gx w * chi v w| := Finset.abs_sum_le_sum_abs _ _
          _ = (ex x : ℝ) := by
            have hterm : ∀ w : V, |gx w * chi v w| = if H' x w ≠ P' x w then (1 : ℝ) else 0 := by
              intro w
              dsimp only [gx, chi, pmZ2]
              split_ifs <;> norm_num
            simp_rw [hterm, Finset.sum_boole]
            rfl
      have hsq : |∑ w : V, gx w * chi v w| ^ 2 ≤ (ex x : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa [sq_abs] using hsq
    have hpar := fourier_parseval gx
    rw [hN2sR, hgx_sq] at hpar
    have hsum_T : ∑ v : V, (∑ w : V, gx w * chi v w) ^ 2 =
        ∑ v ∈ T, (∑ w : V, gx w * chi v w) ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ T) ?_
      intro v _ hv
      rw [hhat_zero v hv]
      norm_num
    rw [hsum_T] at hpar
    have hle_R : (N : ℝ) * (ex x : ℝ) ≤ (T.card : ℝ) * (ex x : ℝ) ^ 2 := by
      rw [← hpar]
      calc
        ∑ v ∈ T, (∑ w : V, gx w * chi v w) ^ 2 ≤ ∑ _v ∈ T, (ex x : ℝ) ^ 2 :=
          Finset.sum_le_sum fun v _ => hhat_bound v
        _ = (T.card : ℝ) * (ex x : ℝ) ^ 2 := by simp
    have hpos_R : (0 : ℝ) < (ex x : ℝ) := Nat.cast_pos.mpr hex_pos
    have hle_R2 : (N : ℝ) ≤ (D.card : ℝ) * (ex x : ℝ) := by
      have h1 : (N : ℝ) ≤ (T.card : ℝ) * (ex x : ℝ) := by nlinarith
      have h2 : (T.card : ℝ) ≤ (D.card : ℝ) := Nat.cast_le.mpr hT_card
      nlinarith
    have hle_R3 : (N : ℝ) ≤ ((D.card * ex x : ℕ) : ℝ) := by rw [Nat.cast_mul]; exact hle_R2
    exact Nat.cast_le.mp hle_R3
  have hsumD1 : 2 * ∑ x ∈ D1, ex x = D1.card * N := by
    rw [Finset.mul_sum]
    trans ∑ _x ∈ D1, N
    · exact Finset.sum_congr rfl fun x hx => hD1_ex x hx
    · simp
  have hsumD2 : D2.card * N ≤ D.card * ∑ x ∈ D2, ex x := by
    rw [Finset.mul_sum]
    calc
      D2.card * N = ∑ _x ∈ D2, N := by simp
      _ ≤ ∑ x ∈ D2, D.card * ex x := Finset.sum_le_sum fun x hx => hD2_ex x hx
  have hD1_lt2 : D1.card < 2 := by
    by_contra hge
    have : 2 * N ≤ 2 * e := by
      have h2le : 2 ≤ D1.card := by omega
      have hmul : 2 * N ≤ D1.card * N := Nat.mul_le_mul_right N h2le
      omega
    omega
  have hD2_zero : D2.card = 0 := by
    by_contra hne0
    have hpos2 : 1 ≤ D2.card := Nat.one_le_iff_ne_zero.mpr hne0
    by_cases hD10 : D1.card = 0
    · have hD_eq : D.card = D2.card := by omega
      rw [hD_eq] at hsumD2
      have hle2 : N ≤ ∑ x ∈ D2, ex x := Nat.le_of_mul_le_mul_left hsumD2 hpos2
      omega
    · have hD11 : D1.card = 1 := by omega
      have h2D2 : D.card ≤ 2 * D2.card := by omega
      have h2sum : D.card * N ≤ D.card * (2 * ∑ x ∈ D2, ex x) := by
        calc
          D.card * N ≤ (2 * D2.card) * N := Nat.mul_le_mul_right N h2D2
          _ = 2 * (D2.card * N) := by ring
          _ ≤ 2 * (D.card * ∑ x ∈ D2, ex x) := Nat.mul_le_mul_left 2 hsumD2
          _ = D.card * (2 * ∑ x ∈ D2, ex x) := by ring
      have hDpos : 0 < D.card := by omega
      have hle2 : N ≤ 2 * ∑ x ∈ D2, ex x := Nat.le_of_mul_le_mul_left h2sum hDpos
      rw [hD11, one_mul] at hsumD1
      omega
  have hD2_emp : D2 = ∅ := Finset.card_eq_zero.mp hD2_zero
  by_cases hD10 : D1.card = 0
  · have hD1_emp : D1 = ∅ := Finset.card_eq_zero.mp hD10
    have he0 : e = 0 := by rw [he_D, hD1_emp, hD2_emp]; simp
    have hD_emp : D = ∅ := by rw [hD_split, hD1_emp, hD2_emp]; simp
    have hDc_univ : Dc = Finset.univ := by simp [Dc, hD_emp]
    have hrow_inj : Function.Injective row := fun a b h =>
      hrow_inj_Dc a (by rw [hDc_univ]; exact Finset.mem_univ a)
        b (by rw [hDc_univ]; exact Finset.mem_univ b) h
    have hcard_eq : Fintype.card (Fin N) = Fintype.card V := by
      rw [Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
    let rowEquiv : Fin N ≃ V := Equiv.ofBijective row
      ((Fintype.bijective_iff_injective_and_card row).mpr ⟨hrow_inj, hcard_eq⟩)
    refine ⟨⟨rowEquiv, col, Q, R, fun i j => ?_⟩, Or.inl he0⟩
    have h1 := hDc_eq i (by rw [hDc_univ]; exact Finset.mem_univ i) (col j)
    have h2 : ¬ H i j ≠ P i j := by
      have := (hHP_iff i (col j)).not.mp (by rw [h1]; exact not_not.mpr rfl)
      simpa [Equiv.symm_apply_apply] using this
    exact not_not.mp h2
  · have hD11 : D1.card = 1 := by omega
    obtain ⟨xStar, hxStar_eq⟩ := Finset.card_eq_one.mp hD11
    have hD_eq : D = {xStar} := by rw [hD_split, hxStar_eq, hD2_emp, Finset.union_empty]
    have hxStar_D1 : xStar ∈ D1 := by rw [hxStar_eq]; exact Finset.mem_singleton_self _
    have hxStar_U0 : row xStar ∈ U0 := (Finset.mem_filter.mp hxStar_D1).2
    have h2e : 2 * e = N := by
      rw [he_D, hxStar_eq, hD2_emp, Finset.sum_empty, add_zero, Finset.sum_singleton]
      exact hD1_ex xStar hxStar_D1
    have hW1 : W.card = 1 := by rw [hW_card, hD_eq, Finset.card_singleton]
    obtain ⟨uStar, huStar_eq⟩ := Finset.card_eq_one.mp hW1
    have hc_sq : (c xStar uStar) ^ 2 = (N : ℝ) ^ 2 := by
      have hpar := fourier_parseval (fun w : V => pm (H' xStar w))
      have hsq1 : ∑ w : V, (pm (H' xStar w)) ^ 2 = (N : ℝ) := by
        simp only [pm_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
      rw [hN2sR, hsq1] at hpar
      have hsum_W : ∑ u : V, (c xStar u) ^ 2 = (c xStar uStar) ^ 2 := by
        have hsub : ∑ u : V, (c xStar u) ^ 2 = ∑ u ∈ W, (c xStar u) ^ 2 := by
          symm
          refine Finset.sum_subset (Finset.subset_univ W) ?_
          intro u _ hu
          have huU0 : u ∈ U0 := by
            by_contra hnot
            exact hu (Finset.mem_compl.mpr hnot)
          rw [hc_zero_U0 xStar (by rw [hD_eq]; exact Finset.mem_singleton_self _) u huU0]
          norm_num
        rw [hsub, huStar_eq, Finset.sum_singleton]
      have hpar' : ∑ u : V, (c xStar u) ^ 2 = (N : ℝ) ^ 2 := by
        dsimp only [c]
        have : (N : ℝ) * (N : ℝ) = (N : ℝ) ^ 2 := (sq _).symm
        rw [← this]
        exact hpar
      rw [← hsum_W, hpar']
    have hc_pm : c xStar uStar = (N : ℝ) ∨ c xStar uStar = -(N : ℝ) := sq_eq_sq_iff_eq_or_eq_neg.mp hc_sq
    let qStar : Bool := decide (c xStar uStar = -(N : ℝ))
    have hH'_star : ∀ w : V, H' xStar w = xor qStar (decide ((∑ b : Fin (2 * s), uStar b * w b) = 1)) := by
      intro w
      have hinv := fourier_inv (fun w' : V => pm (H' xStar w')) w
      rw [hN2sR] at hinv
      have hsum_single :
          ∑ u : V, (∑ x : V, pm (H' xStar x) * chi u x) * chi u w = c xStar uStar * chi uStar w := by
        trans ∑ u ∈ W, c xStar u * chi u w
        · symm
          refine Finset.sum_subset (Finset.subset_univ W) ?_
          intro u _ hu
          have huU0 : u ∈ U0 := by
            by_contra hnot
            exact hu (Finset.mem_compl.mpr hnot)
          rw [hc_zero_U0 xStar (by rw [hD_eq]; exact Finset.mem_singleton_self _) u huU0, zero_mul]
        · rw [huStar_eq, Finset.sum_singleton]
      rw [hsum_single] at hinv
      have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos)
      have hpm_eq : pm (H' xStar w) = pm (xor qStar (decide ((∑ b : Fin (2 * s), uStar b * w b) = 1))) := by
        conv_rhs => rw [pm_xor]
        have hchi : pm (decide ((∑ b : Fin (2 * s), uStar b * w b) = 1)) = chi uStar w := by
          simp only [chi, pmZ2_eq_pm, z2b]
        rw [hchi]
        rcases hc_pm with hpos | hneg
        · have hq : qStar = false := by
            dsimp only [qStar]
            rw [decide_eq_false_iff_not]
            linarith [show (0 : ℝ) < (N : ℝ) from Nat.cast_pos.mpr hNpos]
          have hpm0 : pm false = 1 := rfl
          rw [hq, hpm0, one_mul]
          rw [hpos] at hinv
          exact mul_left_cancel₀ hNne (by linarith)
        · have hq : qStar = true := decide_eq_true hneg
          have hpm1 : pm true = -1 := rfl
          rw [hq, hpm1, neg_one_mul]
          rw [hneg] at hinv
          exact mul_left_cancel₀ hNne (by linarith)
      exact pm_eq_pm_iff.mp hpm_eq
    let rowH : Fin N → V := fun x => if x = xStar then uStar else row x
    let QH : Fin N → Bool := fun x => if x = xStar then qStar else Q x
    have hrowH_inj : Function.Injective rowH := by
      intro x1 x2 heq
      by_cases h1 : x1 = xStar <;> by_cases h2 : x2 = xStar
      · exact h1.trans h2.symm
      · exfalso
        have hx2Dc : x2 ∈ Dc := by simp [Dc, hD_eq, h2]
        have huU0 : uStar ∈ U0 := by
          simp only [rowH, h1, h2, ↓reduceIte] at heq
          rw [heq]
          exact Finset.mem_image_of_mem row hx2Dc
        have huW : uStar ∈ W := by rw [huStar_eq]; exact Finset.mem_singleton_self _
        exact (Finset.mem_compl.mp huW) huU0
      · exfalso
        have hx1Dc : x1 ∈ Dc := by simp [Dc, hD_eq, h1]
        have huU0 : uStar ∈ U0 := by
          simp only [rowH, h1, h2, ↓reduceIte] at heq
          rw [← heq]
          exact Finset.mem_image_of_mem row hx1Dc
        have huW : uStar ∈ W := by rw [huStar_eq]; exact Finset.mem_singleton_self _
        exact (Finset.mem_compl.mp huW) huU0
      · simp only [rowH, h1, h2, ↓reduceIte] at heq
        exact hrow_inj_Dc x1 (by simp [Dc, hD_eq, h1]) x2 (by simp [Dc, hD_eq, h2]) heq
    have hcard_eq : Fintype.card (Fin N) = Fintype.card V := by
      rw [Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
    let rowHEquiv : Fin N ≃ V := Equiv.ofBijective rowH
      ((Fintype.bijective_iff_injective_and_card rowH).mpr ⟨hrowH_inj, hcard_eq⟩)
    have hHsylv : ∀ i j, H i j = xor (xor (QH i) (R j))
        (decide ((∑ b : Fin (2 * s), rowHEquiv i b * col j b) = 1)) := by
      intro i j
      by_cases hi : i = xStar
      · subst hi
        have h1 := hH'_star (col j)
        simp only [H', Equiv.symm_apply_apply] at h1
        simp only [QH, rowHEquiv, Equiv.ofBijective_apply, rowH, ↓reduceIte]
        exact xor_eq_xor_imp h1
      · have hiDc : i ∈ Dc := by simp [Dc, hD_eq, hi]
        have h1 := hDc_eq i hiDc (col j)
        simp only [H', P', Equiv.symm_apply_apply] at h1
        simp only [QH, rowHEquiv, Equiv.ofBijective_apply, rowH, hi, ↓reduceIte]
        exact xor_eq_xor_imp h1
    rcases Finset.mem_image.mp hxStar_U0 with ⟨x0, hx0Dc, hrow_x0⟩
    have hxne : xStar ≠ x0 := by
      intro heq
      subst heq
      have : xStar ∈ D := by rw [hD_eq]; exact Finset.mem_singleton_self _
      exact (Finset.mem_compl.mp hx0Dc) this
    refine ⟨⟨rowHEquiv, col, QH, R, hHsylv⟩, Or.inr ⟨h2e, xStar, x0, hxne, xor (Q xStar) (Q x0), ?_⟩⟩
    intro x y
    by_cases hx : x = xStar
    · subst x
      simp only [↓reduceIte, P]
      have hx0_ne : x0 ≠ xStar := Ne.symm hxne
      rw [hHsylv x0 y]
      simp only [QH, rowHEquiv, Equiv.ofBijective_apply, rowH, hx0_ne, ↓reduceIte, hrow_x0]
      exact xor_flip_cancel _ _ _ _
    · simp only [hx, ↓reduceIte, P]
      rw [hHsylv x y]
      simp only [QH, rowHEquiv, Equiv.ofBijective_apply, rowH, hx, ↓reduceIte]

lemma append_gates_wires (gs1 gs2 : List Gate) (init : List Bool) :
    ((gs1 ++ gs2).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init) := by
  exact List.foldl_append

lemma wires_prefix_getD (gs : List Gate) (init : List Bool) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) init).getD i false =
      init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def xorGates (a b : ℕ) (nextWire : ℕ) : List Gate :=
  [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [nextWire]⟩]

lemma xorGates_spec (a b : ℕ) (w : List Bool) :
    let res := (xorGates a b w.length).foldl
      (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w
    res.length = w.length + 2 ∧
    res.getD (w.length + 1) false = xor (w.getD a false) (w.getD b false) := by
  simp only [xorGates, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
  constructor
  · simp
  · rw [getD_append_single]
    have hlen : (w ++ [GateOp.eval (GateOp.mod 2) [w.getD a false, w.getD b false]]).length = w.length + 1 := by
      simp
    simp only [hlen, ↓reduceIte, getD_append_single]
    cases w.getD a false <;> cases w.getD b false <;> decide

lemma xorGates_linear (a b nw : ℕ) : (xorGates a b nw).countP nonlinearGate = 0 := by
  simp [xorGates, nonlinearGate, GateOp.eval]

lemma xorGates_len (a b nw : ℕ) : ∀ g ∈ xorGates a b nw, g.inputs.length ≤ 2 := by
  intro g hg
  simp only [xorGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

def linearFoldXor (wires : List ℕ) (accWire : ℕ) (baseLen : ℕ) : List Gate × ℕ :=
  match wires with
  | [] => ([], accWire)
  | w :: rest =>
    let gs1 := xorGates accWire w baseLen
    let newAcc := baseLen + 1
    let (gs2, outW) := linearFoldXor rest newAcc (baseLen + 2)
    (gs1 ++ gs2, outW)

lemma linearFoldXor_spec : ∀ (wires : List ℕ) (accWire : ℕ) (W : List Bool),
    (accWire < W.length) → (∀ w ∈ wires, w < W.length) →
    let (gs, outW) := linearFoldXor wires accWire W.length
    let W' := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W
    W'.length = W.length + gs.length ∧
    outW < W'.length ∧
    gs.countP nonlinearGate = 0 ∧
    (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < W.length + j) ∧
    W'.getD outW false = wires.foldl (fun acc w => xor acc (W.getD w false)) (W.getD accWire false) := by
  intro wires
  induction wires with
  | nil =>
    intro accWire W hacc _
    simp [linearFoldXor, hacc]
  | cons w rest ih =>
    intro accWire W hacc hwires
    have hw : w < W.length := hwires w (by simp)
    have hrest : ∀ u ∈ rest, u < W.length := fun u hu => hwires u (by simp [hu])
    let gs1 := xorGates accWire w W.length
    let W1 := gs1.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) W
    have h1 := xorGates_spec accWire w W
    have hW1_len : W1.length = W.length + 2 := h1.1
    have hW1_acc : W.length + 1 < W1.length := by omega
    have hW1_rest : ∀ u ∈ rest, u < W1.length := fun u hu => by have := hrest u hu; omega
    have hih := ih (W.length + 1) W1 hW1_acc hW1_rest
    rw [hW1_len] at hih
    simp only [linearFoldXor]
    set p := linearFoldXor rest (W.length + 1) (W.length + 2)
    have hp_eq : p = (p.1, p.2) := Prod.mk.eta.symm
    rcases p with ⟨gs2, outW⟩
    dsimp only at hih ⊢
    rw [append_gates_wires]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hih.1, List.length_append]
      have hgs1_len : (xorGates accWire w W.length).length = 2 := rfl
      rw [hgs1_len]
      omega
    · exact hih.2.1
    · rw [List.countP_append, xorGates_linear, hih.2.2.1]
    · intro g hg
      rcases List.mem_append.mp hg with hg1 | hg2
      · exact xorGates_len accWire w W.length g hg1
      · exact hih.2.2.2.1 g hg2
    · intro j hj i hi
      by_cases hj2 : j < 2
      · rw [List.getD_append _ _ _ _ (by exact hj2)] at hi
        have hj_cases : j = 0 ∨ j = 1 := by omega
        rcases hj_cases with rfl | rfl
        · simp only [xorGates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
        · simp only [xorGates, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hi
          rcases hi with rfl
          omega
      · have hgs1_len : (xorGates accWire w W.length).length = 2 := rfl
        rw [List.getD_append_right _ _ _ _ (by rw [hgs1_len]; omega), hgs1_len] at hi
        have hlt2 : j - 2 < gs2.length := by
          rw [List.length_append, hgs1_len] at hj; omega
        have hi2 := hih.2.2.2.2.1 (j - 2) hlt2 i hi
        omega
    · rw [hih.2.2.2.2.2, h1.2]
      simp only [List.foldl_cons]
      have hcongr : ∀ (l : List ℕ) (initB : Bool),
          (∀ u ∈ l, u < W.length) →
          l.foldl (fun acc u => xor acc (W1.getD u false)) initB =
          l.foldl (fun acc u => xor acc (W.getD u false)) initB := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons u l' ihl =>
          intro initB hl
          simp only [List.foldl_cons]
          have hu : u < W.length := hl u (by simp)
          have hget : W1.getD u false = W.getD u false := wires_prefix_getD gs1 W u hu
          rw [hget]
          exact ihl _ (fun v hv => hl v (by simp [hv]))
      exact hcongr rest _ hrest

lemma foldl_xor_oneHot {N : ℕ} (f : Fin N → Bool) (x : Fin N) (W : List Bool)
    (hW : ∀ i : Fin N, W.getD i.val false = decide (i = x)) :
    ((((List.finRange N).filter (fun i => f i)).map Fin.val).foldl
      (fun acc w => xor acc (W.getD w false)) false) = f x := by
  have hgen : ∀ (l : List (Fin N)) (init : Bool), l.Nodup →
      (((l.filter (fun i => f i)).map Fin.val).foldl
        (fun acc w => xor acc (W.getD w false)) init) =
      xor init (if x ∈ l then f x else false) := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons a rest ih =>
      intro init hnd
      rcases List.nodup_cons.mp hnd with ⟨ha_not, hnd_rest⟩
      simp only [List.filter_cons]
      by_cases hfa : f a = true
      · simp only [hfa, ↓reduceIte, List.map_cons, List.foldl_cons, hW a]
        rw [ih _ hnd_rest]
        by_cases hax : a = x
        · subst hax
          simp [ha_not, hfa]
        · have hxa : x ≠ a := Ne.symm hax
          simp [hax, hxa]
      · have hfaf : f a = false := Bool.eq_false_iff.mpr hfa
        simp only [hfaf, Bool.false_eq_true, ↓reduceIte]
        rw [ih _ hnd_rest]
        by_cases hax : a = x
        · subst hax
          simp [ha_not, hfaf]
        · have hxa : x ≠ a := Ne.symm hax
          simp [hxa]
  have h1 := hgen (List.finRange N) false (List.nodup_finRange N)
  simpa [List.mem_finRange] using h1

lemma foldl_xor_oneHot_right {N : ℕ} (g : Fin N → Bool) (y : Fin N) (W : List Bool)
    (hW : ∀ j : Fin N, W.getD (N + j.val) false = decide (j = y)) :
    ((((List.finRange N).filter (fun j => g j)).map (fun j => N + j.val)).foldl
      (fun acc w => xor acc (W.getD w false)) false) = g y := by
  have hgen : ∀ (l : List (Fin N)) (init : Bool), l.Nodup →
      (((l.filter (fun j => g j)).map (fun j => N + j.val)).foldl
        (fun acc w => xor acc (W.getD w false)) init) =
      xor init (if y ∈ l then g y else false) := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons a rest ih =>
      intro init hnd
      rcases List.nodup_cons.mp hnd with ⟨ha_not, hnd_rest⟩
      simp only [List.filter_cons]
      by_cases hga : g a = true
      · simp only [hga, ↓reduceIte, List.map_cons, List.foldl_cons, hW a]
        rw [ih _ hnd_rest]
        by_cases hay : a = y
        · subst hay
          simp [ha_not, hga]
        · have hya : y ≠ a := Ne.symm hay
          simp [hay, hya]
      · have hgaf : g a = false := Bool.eq_false_iff.mpr hga
        simp only [hgaf, Bool.false_eq_true, ↓reduceIte]
        rw [ih _ hnd_rest]
        by_cases hay : a = y
        · subst hay
          simp [ha_not, hgaf]
        · have hya : y ≠ a := Ne.symm hay
          simp [hya]
  have h1 := hgen (List.finRange N) false (List.nodup_finRange N)
  simpa [List.mem_finRange] using h1

structure BuiltCircuit (N : ℕ) where
  gates : List Gate
  outWire : ℕ
  out_lt : outWire < N + N + gates.length
  len_ok : ∀ g ∈ gates, g.inputs.length ≤ 2
  back_ok : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j
  nl_count : ℕ
  nl_eq : gates.countP nonlinearGate = nl_count

def evalBuilt {N : ℕ} (B : BuiltCircuit N) (x y : Fin N) : Bool :=
  (B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (oneEach x y)).getD B.outWire false

lemma oneEach_len {N : ℕ} (x y : Fin N) : (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_left {N : ℕ} (x y i : Fin N) :
    (oneEach x y).getD i.val false = decide (i = x) := by
  dsimp only [oneEach]
  have h1 : (List.ofFn (fun k : Fin N => decide (k = x))).length = N := by simp
  rw [List.getD_append _ _ _ _ (by rw [h1]; exact i.isLt)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma oneEach_getD_right {N : ℕ} (x y j : Fin N) :
    (oneEach x y).getD (N + j.val) false = decide (j = y) := by
  dsimp only [oneEach]
  have h1 : (List.ofFn (fun k : Fin N => decide (k = x))).length = N := by simp
  rw [List.getD_append_right _ _ _ _ (by rw [h1]; omega), h1]
  have hsub : N + j.val - N = j.val := by omega
  rw [hsub]
  simp [List.getD_eq_getElem?_getD, j.isLt]

lemma exists_built_const_false (N : ℕ) :
    ∃ B : BuiltCircuit N, B.nl_count = 0 ∧ ∀ x y : Fin N, evalBuilt B x y = false := by
  refine ⟨{
    gates := [⟨GateOp.or, []⟩]
    outWire := N + N
    out_lt := by simp
    len_ok := by intro g hg; simp at hg; subst hg; decide
    back_ok := by intro j hj i hi; simp at hj; subst hj; simp at hi
    nl_count := 0
    nl_eq := by decide
  }, rfl, fun x y => ?_⟩
  simp [evalBuilt, oneEach_len, GateOp.eval]

lemma exists_built_append_xor {N : ℕ} (B : BuiltCircuit N) (w1 w2 : ℕ)
    (hw1 : w1 < N + N + B.gates.length) (hw2 : w2 < N + N + B.gates.length) :
    ∃ B' : BuiltCircuit N,
      B'.gates = B.gates ++ xorGates w1 w2 (N + N + B.gates.length) ∧
      B'.nl_count = B.nl_count ∧
      ∀ x y : Fin N,
        let W := B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
        evalBuilt B' x y = xor (W.getD w1 false) (W.getD w2 false) := by
  let gs1 := xorGates w1 w2 (N + N + B.gates.length)
  refine ⟨{
    gates := B.gates ++ gs1
    outWire := N + N + B.gates.length + 1
    out_lt := by simp [gs1, xorGates]; omega
    len_ok := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact B.len_ok g h1
      · exact xorGates_len _ _ _ g h2
    back_ok := by
      intro j hj i hi
      by_cases hlt : j < B.gates.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        exact B.back_ok j hlt i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have hlen1 : gs1.length = 2 := rfl
        have hsub : j - B.gates.length = 0 ∨ j - B.gates.length = 1 := by
          rw [List.length_append, hlen1] at hj; omega
        rcases hsub with hs | hs
        · rw [hs] at hi
          simp only [gs1, xorGates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
        · rw [hs] at hi
          simp only [gs1, xorGates, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hi
          rcases hi with rfl
          omega
    nl_count := B.nl_count
    nl_eq := by rw [List.countP_append, B.nl_eq, xorGates_linear, Nat.add_zero]
  }, rfl, rfl, fun x y => ?_⟩
  dsimp only [evalBuilt]
  rw [append_gates_wires]
  set W := B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
  have hWlen : W.length = N + N + B.gates.length := by rw [wires_length, oneEach_len]
  have hsp := xorGates_spec w1 w2 W
  rw [hWlen] at hsp
  exact hsp.2

lemma exists_built_append_and {N : ℕ} (B : BuiltCircuit N) (w1 w2 : ℕ)
    (hw1 : w1 < N + N + B.gates.length) (hw2 : w2 < N + N + B.gates.length) :
    ∃ B' : BuiltCircuit N,
      B'.gates = B.gates ++ [⟨GateOp.and, [w1, w2]⟩] ∧
      B'.nl_count = B.nl_count + 1 ∧
      ∀ x y : Fin N,
        let W := B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
        evalBuilt B' x y = (W.getD w1 false && W.getD w2 false) := by
  refine ⟨{
    gates := B.gates ++ [⟨GateOp.and, [w1, w2]⟩]
    outWire := N + N + B.gates.length
    out_lt := by simp
    len_ok := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact B.len_ok g h1
      · simp at h2; subst h2; simp
    back_ok := by
      intro j hj i hi
      by_cases hlt : j < B.gates.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        exact B.back_ok j hlt i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have hsub : j - B.gates.length = 0 := by
          rw [List.length_append, List.length_singleton] at hj; omega
        rw [hsub] at hi
        simp only [List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
    nl_count := B.nl_count + 1
    nl_eq := by
      rw [List.countP_append, B.nl_eq]
      have h1 : ([⟨GateOp.and, [w1, w2]⟩] : List Gate).countP nonlinearGate = 1 := by
        simp [nonlinearGate, GateOp.eval]
      rw [h1]
  }, rfl, rfl, fun x y => ?_⟩
  dsimp only [evalBuilt]
  rw [append_gates_wires]
  set W := B.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
  have hWlen : W.length = N + N + B.gates.length := by rw [wires_length, oneEach_len]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
  rw [getD_append_single, hWlen]
  simp [GateOp.eval]

lemma exists_built_extend_affine {N : ℕ} (B : BuiltCircuit N) (fx gy : Fin N → Bool) :
    ∃ B' : BuiltCircuit N,
      (∃ ext : List Gate, B'.gates = B.gates ++ ext) ∧
      B'.nl_count = B.nl_count ∧
      ∀ x y : Fin N, evalBuilt B' x y = xor (fx x) (gy y) := by
  let g0 : List Gate := [⟨GateOp.or, []⟩]
  let base0 := N + N + B.gates.length
  let wsX : List ℕ := ((List.finRange N).filter (fun i => fx i)).map Fin.val
  let wsY : List ℕ := ((List.finRange N).filter (fun j => gy j)).map (fun j => N + j.val)
  let ws : List ℕ := wsX ++ wsY
  let res := linearFoldXor ws base0 (base0 + 1)
  let gs := g0 ++ res.1
  have hws_lt : ∀ w ∈ ws, w < base0 + 1 := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨i, _, rfl⟩
      have := i.isLt
      omega
    · rcases List.mem_map.mp h2 with ⟨j, _, rfl⟩
      have := j.isLt
      omega
  have hspec_all : ∀ x y : Fin N,
      let W0 := (B.gates ++ g0).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
      W0.length = base0 + 1 ∧
      W0.getD base0 false = false ∧
      (∀ i : Fin N, W0.getD i.val false = decide (i = x)) ∧
      (∀ j : Fin N, W0.getD (N + j.val) false = decide (j = y)) := by
    intro x y
    dsimp only
    have hlen : ((B.gates ++ g0).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (oneEach x y)).length = base0 + 1 := by
      rw [wires_length, oneEach_len, List.length_append]
      simp [g0, base0, Nat.add_assoc]
    refine ⟨hlen, ?_, ?_, ?_⟩
    · rw [append_gates_wires]
      simp only [g0, List.foldl_cons, List.foldl_nil, List.map_nil]
      rw [getD_append_single, wires_length, oneEach_len]
      simp [base0, GateOp.eval]
    · intro i
      rw [wires_prefix_getD _ _ i.val (by rw [oneEach_len]; omega), oneEach_getD_left]
    · intro j
      rw [wires_prefix_getD _ _ (N + j.val) (by rw [oneEach_len]; omega), oneEach_getD_right]
  have hDummyW : ∃ W0 : List Bool, W0.length = base0 + 1 := ⟨List.replicate (base0 + 1) false, by simp⟩
  obtain ⟨W0, hW0len⟩ := hDummyW
  have hlin := linearFoldXor_spec ws base0 W0 (by omega) (fun w hw => by rw [hW0len]; exact hws_lt w hw)
  rw [hW0len] at hlin
  refine ⟨{
    gates := B.gates ++ gs
    outWire := res.2
    out_lt := by
      have h1 : res.2 < base0 + 1 + res.1.length := by
        have := hlin.2.1
        rw [hlin.1] at this
        exact this
      simp only [gs, List.length_append, g0, List.length_singleton]
      omega
    len_ok := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact B.len_ok g h1
      · rcases List.mem_append.mp h2 with h3 | h4
        · simp [g0] at h3; subst h3; decide
        · exact hlin.2.2.2.1 g h4
    back_ok := by
      intro j hj i hi
      by_cases h1 : j < B.gates.length
      · rw [List.getD_append _ _ _ _ h1] at hi
        exact B.back_ok j h1 i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        by_cases h2 : j = B.gates.length
        · have hsub : j - B.gates.length = 0 := by omega
          rw [hsub] at hi
          simp [gs, g0] at hi
        · have hgt : 1 ≤ j - B.gates.length := by omega
          dsimp only [gs] at hi
          rw [List.getD_append_right _ _ _ _ (by simp [g0]; omega)] at hi
          simp only [g0, List.length_singleton] at hi
          have hlt : j - B.gates.length - 1 < res.1.length := by
            simp only [gs, List.length_append, g0, List.length_singleton] at hj
            omega
          have hback := hlin.2.2.2.2.1 (j - B.gates.length - 1) hlt i hi
          omega
    nl_count := B.nl_count
    nl_eq := by
      rw [List.countP_append, B.nl_eq, List.countP_append, hlin.2.2.1]
      have h0 : g0.countP nonlinearGate = 0 := by decide
      rw [h0]
      simp
  }, ⟨gs, rfl⟩, rfl, fun x y => ?_⟩
  dsimp only [evalBuilt, gs]
  rw [← List.append_assoc, append_gates_wires]
  have hsp := hspec_all x y
  set Wxy := (B.gates ++ g0).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (oneEach x y)
  have hlin_xy := linearFoldXor_spec ws base0 Wxy (by rw [hsp.1]; omega)
    (fun w hw => by rw [hsp.1]; exact hws_lt w hw)
  rw [hsp.1] at hlin_xy
  rw [hlin_xy.2.2.2.2.2, hsp.2.1]
  dsimp only [ws]
  rw [List.foldl_append, foldl_xor_oneHot fx x Wxy hsp.2.2.1]
  have hgen : ∀ (l : List ℕ) (init : Bool),
      l.foldl (fun acc w => xor acc (Wxy.getD w false)) init =
      xor init (l.foldl (fun acc w => xor acc (Wxy.getD w false)) false) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l' ihl =>
      intro init
      simp only [List.foldl_cons, Bool.false_xor]
      rw [ihl (xor init (Wxy.getD a false)), ihl (Wxy.getD a false)]
      cases init <;> cases Wxy.getD a false <;>
        cases l'.foldl (fun acc w => xor acc (Wxy.getD w false)) false <;> rfl
  rw [hgen, foldl_xor_oneHot_right gy y Wxy hsp.2.2.2]

lemma exists_circuit_signed_sylvester {s : ℕ}
    (f g : Fin (4 ^ s) → Fin (2 * s) → ZMod 2) (q r : Fin (4 ^ s) → Bool) :
    let N := 4 ^ s
    ∃ C : Circuit,
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      ReadsBack (N + N) C ∧
      C.gates.countP nonlinearGate ≤ s ∧
      ∀ x y : Fin N, C.eval (oneEach x y) =
        xor (xor (q x) (r y)) (decide ((∑ b : Fin (2 * s), f x b * g y b) = 1)) := by
  intro N
  let q' : Fin N → Bool := fun x =>
    xor (q x) (z2b (∑ k : Fin s, f x ⟨2 * k.val, by omega⟩ * f x ⟨2 * k.val + 1, by omega⟩))
  let r' : Fin N → Bool := fun y =>
    xor (r y) (z2b (∑ k : Fin s, g y ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩))
  have hstep : ∀ (m : ℕ) (hms : m ≤ s),
      ∃ B : BuiltCircuit N,
        B.nl_count = m ∧
        ∀ x y : Fin N, evalBuilt B x y =
          xor (xor (q' x) (r' y))
            (z2b (∑ k : Fin m,
              (f x ⟨2 * k.val, by omega⟩ + g y ⟨2 * k.val + 1, by omega⟩) *
              (f x ⟨2 * k.val + 1, by omega⟩ + g y ⟨2 * k.val, by omega⟩))) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨B0, h0nl, _⟩ := exists_built_const_false N
      obtain ⟨B1, _, h1nl, h1ev⟩ := exists_built_extend_affine B0 q' r'
      refine ⟨B1, by omega, fun x y => ?_⟩
      rw [h1ev]
      simp [z2b]
    | succ m ih =>
      intro hms
      obtain ⟨B, hBnl, hBev⟩ := ih (Nat.le_of_succ_le hms)
      let fx1 : Fin N → Bool := fun x => z2b (f x ⟨2 * m, by omega⟩)
      let gy1 : Fin N → Bool := fun y => z2b (g y ⟨2 * m + 1, by omega⟩)
      let fx2 : Fin N → Bool := fun x => z2b (f x ⟨2 * m + 1, by omega⟩)
      let gy2 : Fin N → Bool := fun y => z2b (g y ⟨2 * m, by omega⟩)
      obtain ⟨B1, ⟨ext1, hB1g⟩, hB1nl, hB1ev⟩ := exists_built_extend_affine B fx1 gy1
      obtain ⟨B2, ⟨ext2, hB2g⟩, hB2nl, hB2ev⟩ := exists_built_extend_affine B1 fx2 gy2
      have hwB_lt : B.outWire < N + N + B2.gates.length := by
        have := B.out_lt
        rw [hB2g, hB1g, List.length_append, List.length_append]
        omega
      have hw1_lt : B1.outWire < N + N + B2.gates.length := by
        have := B1.out_lt
        rw [hB2g, List.length_append]
        omega
      have hw2_lt : B2.outWire < N + N + B2.gates.length := B2.out_lt
      obtain ⟨B3, hB3g, hB3nl, hB3ev⟩ := exists_built_append_and B2 B1.outWire B2.outWire hw1_lt hw2_lt
      have hwB_lt3 : B.outWire < N + N + B3.gates.length := by
        rw [hB3g, List.length_append]; omega
      obtain ⟨B4, _, hB4nl, hB4ev⟩ := exists_built_append_xor B3 B.outWire B3.outWire hwB_lt3 B3.out_lt
      refine ⟨B4, by omega, fun x y => ?_⟩
      rw [hB4ev x y]
      have hgetB :
          (B3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (oneEach x y)).getD B.outWire false = evalBuilt B x y := by
        rw [hB3g, hB2g, hB1g, List.append_assoc, List.append_assoc, append_gates_wires]
        exact wires_prefix_getD _ _ B.outWire (by rw [wires_length, oneEach_len]; exact B.out_lt)
      have hgetB3 :
          (B3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (oneEach x y)).getD B3.outWire false = evalBuilt B3 x y := rfl
      have hget1 :
          (B2.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (oneEach x y)).getD B1.outWire false = evalBuilt B1 x y := by
        rw [hB2g, append_gates_wires]
        exact wires_prefix_getD _ _ B1.outWire (by rw [wires_length, oneEach_len]; exact B1.out_lt)
      have hget2 :
          (B2.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (oneEach x y)).getD B2.outWire false = evalBuilt B2 x y := rfl
      rw [hgetB, hgetB3, hB3ev x y, hget1, hget2, hBev x y, hB1ev x y, hB2ev x y]
      apply b2z_inj
      simp only [b2z_xor, b2z_and, b2z_z2b, fx1, gy1, fx2, gy2]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      ring
  obtain ⟨B, hBnl, hBev⟩ := hstep s (Nat.le_refl s)
  refine ⟨⟨B.gates, B.outWire⟩, B.len_ok, B.back_ok, by rw [B.nl_eq, hBnl], fun x y => ?_⟩
  change evalBuilt B x y = _
  rw [hBev x y]
  apply b2z_inj
  simp only [b2z_xor, b2z_z2b, q', r']
  have hpair_sum :
      ∑ b : Fin (2 * s), f x b * g y b =
        ∑ k : Fin s,
          (f x ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val, by omega⟩ +
           f x ⟨2 * k.val + 1, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩) := by
    let e : Fin s × Fin 2 ≃ Fin (2 * s) :=
      { toFun := fun ⟨k, p⟩ => ⟨2 * k.val + p.val, by omega⟩
        invFun := fun b => (⟨b.val / 2, by omega⟩, ⟨b.val % 2, Nat.mod_lt _ (by decide)⟩)
        left_inv := fun ⟨k, p⟩ => by
          apply Prod.ext
          · apply Fin.ext; dsimp only; omega
          · apply Fin.ext; dsimp only; omega
        right_inv := fun b => by
          apply Fin.ext; dsimp only; omega }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Fin.sum_univ_two, e]
  have hdec : b2z (decide ((∑ b : Fin (2 * s), f x b * g y b) = 1)) =
      ∑ b : Fin (2 * s), f x b * g y b := b2z_z2b _
  rw [hdec, hpair_sum]
  have hterms :
      ∑ k : Fin s,
          (f x ⟨2 * k.val, by omega⟩ + g y ⟨2 * k.val + 1, by omega⟩) *
          (f x ⟨2 * k.val + 1, by omega⟩ + g y ⟨2 * k.val, by omega⟩) =
        (∑ k : Fin s, f x ⟨2 * k.val, by omega⟩ * f x ⟨2 * k.val + 1, by omega⟩) +
        (∑ k : Fin s, g y ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩) +
        (∑ k : Fin s,
          (f x ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val, by omega⟩ +
           f x ⟨2 * k.val + 1, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hterms]
  generalize (∑ k : Fin s, f x ⟨2 * k.val, by omega⟩ * f x ⟨2 * k.val + 1, by omega⟩) = SX
  generalize (∑ k : Fin s, g y ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩) = SY
  generalize (∑ k : Fin s,
    (f x ⟨2 * k.val, by omega⟩ * g y ⟨2 * k.val, by omega⟩ +
     f x ⟨2 * k.val + 1, by omega⟩ * g y ⟨2 * k.val + 1, by omega⟩)) = SXY
  have hx0 := z2_add_self SX
  have hy0 := z2_add_self SY
  linear_combination hx0 + hy0

lemma card_filter_half_vec {m : ℕ} (a : Fin m → ZMod 2) (ha : a ≠ 0) :
    2 * ((Finset.univ : Finset (Fin m → ZMod 2)).filter
      (fun v => (∑ b : Fin m, a b * v b) = 1)).card = 2 ^ m := by
  have hsum := sum_chi a
  simp only [ha, ↓reduceIte] at hsum
  let S1 := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun v => (∑ b : Fin m, a b * v b) = 1)
  let S0 := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun v => (∑ b : Fin m, a b * v b) ≠ 1)
  have hcomp : S1.card + S0.card = 2 ^ m := by
    have h1 := card_filter_add_card_filter_not
      (Finset.univ : Finset (Fin m → ZMod 2)) (fun v => (∑ b : Fin m, a b * v b) = 1)
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
    exact h1
  have hsplit : ∑ v : Fin m → ZMod 2, chi a v = (S0.card : ℝ) - (S1.card : ℝ) := by
    simp only [chi, pmZ2]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    change (S1.card : ℝ) * (-1) + (S0.card : ℝ) * 1 = (S0.card : ℝ) - (S1.card : ℝ)
    ring
  rw [hsplit] at hsum
  have heq : S0.card = S1.card := Nat.cast_injective (sub_eq_zero.mp hsum)
  change 2 * S1.card = 2 ^ m
  omega

theorem main :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
∀ s : ℕ, 2 ≤ s →
  let N := 4^s
  let V := Fin (2*s) → ZMod 2
  ∀ H : Fin N → Fin N → Bool,
  (∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N) →
  let sylvester := ∃ (row col : Fin N ≃ V) (Q R : Fin N → Bool),
    ∀ i j, H i j = xor (xor (Q i) (R j))
      (decide ((∑ b : Fin (2*s), row i b * col j b) = 1))
  let clone := fun (A B : Fin N → Fin N → Bool) =>
    ∃ i j : Fin N, i ≠ j ∧ ∃ flip : Bool, ∀ x y,
      B x y = if x = i then xor flip (A j y) else A x y
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.gates.countP nonlinear ≤ s
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N) =>
    C.eval (PEqualNP.Represents.oneEach x y)
  let errors := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ value C i j)).card
  (∀ C, valid C → errors C + 2 < N →
    sylvester ∧ (errors C = 0 ∨
      (2 * errors C = N ∧ (clone H (value C) ∨ clone (Function.swap H) (Function.swap (value C)))))) ∧
  (sylvester → (∃ C, valid C ∧ 2 * errors C = N) ∧ (∃ C, valid C ∧ errors C + 2 = N)) := by
  intro nonlinear s hs N V H hH sylvester clone valid value errors
  have hNpos : 0 < N := pow_pos (by decide) s
  have hNge16 : 16 ≤ N := by
    have : 4 ^ 2 ≤ 4 ^ s := Nat.pow_le_pow_right (by decide) hs
    simpa [N] using this
  have hN2s : 2 ^ (2 * s) = N := by
    dsimp only [N]
    rw [pow_mul]
    norm_num
  have hN2sR : (2 ^ (2 * s) : ℝ) = (N : ℝ) := by exact_mod_cast hN2s
  constructor
  · intro C hval herr
    rcases hval with ⟨hlen, hback, hcnt⟩
    have hcnt' : C.gates.countP nonlinearGate ≤ s := hcnt
    set t := C.gates.countP nonlinearGate
    obtain ⟨lam, mu, U, W, pOut, qOut, cOut, htri⟩ := circuit_to_triangular (N := N) C hlen hback
    let F : (Fin (2 * t) → ZMod 2) → ZMod 2 := fun d => ∑ k : Fin t, cOut k * triGate lam mu d k
    have hrank_le : (Matrix.of fun x y : Fin N => pm (value C x y)).rank ≤ (fourierSupp F).card :=
      rank_le_fourierSupp U W pOut qOut F (value C) htri
    have hfrob := frobenius_rank_loss hNpos H (value C) hH
    have hrank_ge : N - 3 ≤ (Matrix.of fun x y : Fin N => pm (value C x y)).rank := by
      have h1 : N * (N - (Matrix.of fun x y : Fin N => pm (value C x y)).rank) < 4 * N := by
        dsimp only [errors] at herr
        omega
      have h2 : N - (Matrix.of fun x y : Fin N => pm (value C x y)).rank < 4 := by
        by_contra hge
        have : 4 * N ≤ N * (N - (Matrix.of fun x y : Fin N => pm (value C x y)).rank) := by
          rw [mul_comm]; exact Nat.mul_le_mul_left N (by omega)
        omega
      omega
    have hsupp_big : 5 * N < 8 * (fourierSupp F).card := by omega
    have hsupp_le_4t : (fourierSupp F).card ≤ 4 ^ t := by
      calc
        (fourierSupp F).card ≤ (Finset.univ : Finset (Fin (2 * t) → ZMod 2)).card :=
          Finset.card_le_univ _
        _ = 4 ^ t := by
          rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_mul]
          norm_num
    have ht_eq : t = s := by
      by_contra hne
      have hlt : t ≤ s - 1 := by omega
      have h4le : 4 ^ t ≤ 4 ^ (s - 1) := Nat.pow_le_pow_right (by decide) hlt
      have h4mul : 4 * 4 ^ (s - 1) = N := by
        dsimp only [N]
        conv_rhs => rw [show s = (s - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    have hcut := triangular_spectrum_cutoff t lam mu cOut
    have hpure : (∀ k : Fin t, cOut k = 1) ∧ (∀ k : Fin t, ∀ l : Fin k.val, lam k l = 0 ∧ mu k l = 0) := by
      rcases hcut with hsmall | hp
      · exfalso
        have h4eq : 4 ^ t = N := by rw [ht_eq]
        change 8 * (fourierSupp F).card ≤ 5 * 4 ^ t at hsmall
        rw [h4eq] at hsmall
        omega
      · exact hp
    subst ht_eq
    have htri_pure : ∀ (d : V) (k : Fin t),
        triGate lam mu d k = d ⟨2 * k.val, by omega⟩ * d ⟨2 * k.val + 1, by omega⟩ := by
      intro d k
      have h0 : triGate lam mu d k = triGate (fun _ _ => 0) (fun _ _ => 0) d k := by
        dsimp only [triGate]
        refine evalTri_congr (k.val + 1) _ _ (fun _ _ => rfl) ?_ ?_
        · intro j hj l; exact (hpure.2 ⟨j, by omega⟩ l).1
        · intro j hj l; exact (hpure.2 ⟨j, by omega⟩ l).2
      rw [h0, triGate_pure]
    let rowP : Fin N → V := fun x => U x
    let colP : Fin N → V := fun y b =>
      if h : b.val % 2 = 0 then W y ⟨b.val + 1, by omega⟩ else W y ⟨b.val - 1, by omega⟩
    let QP : Fin N → Bool := fun x =>
      z2b (pOut x + ∑ k : Fin t, U x ⟨2 * k.val, by omega⟩ * U x ⟨2 * k.val + 1, by omega⟩)
    let RP : Fin N → Bool := fun y =>
      z2b (qOut y + ∑ k : Fin t, W y ⟨2 * k.val, by omega⟩ * W y ⟨2 * k.val + 1, by omega⟩)
    have hval_sylv : ∀ x y : Fin N,
        value C x y = xor (xor (QP x) (RP y)) (decide ((∑ b : Fin (2 * t), rowP x b * colP y b) = 1)) := by
      intro x y
      apply b2z_inj
      have hdec : b2z (decide ((∑ b : Fin (2 * t), rowP x b * colP y b) = 1)) =
          ∑ b : Fin (2 * t), rowP x b * colP y b := b2z_z2b _
      rw [htri x y, b2z_xor, b2z_xor, b2z_z2b, b2z_z2b, hdec]
      have hsum_tri :
          ∑ k : Fin t, cOut k * triGate lam mu (U x + W y) k =
            (∑ k : Fin t, U x ⟨2 * k.val, by omega⟩ * U x ⟨2 * k.val + 1, by omega⟩) +
            (∑ k : Fin t, W y ⟨2 * k.val, by omega⟩ * W y ⟨2 * k.val + 1, by omega⟩) +
            ∑ b : Fin (2 * t), rowP x b * colP y b := by
        have hpair :
            ∑ b : Fin (2 * t), rowP x b * colP y b =
              ∑ k : Fin t,
                (U x ⟨2 * k.val, by omega⟩ * W y ⟨2 * k.val + 1, by omega⟩ +
                 U x ⟨2 * k.val + 1, by omega⟩ * W y ⟨2 * k.val, by omega⟩) := by
          let e : Fin t × Fin 2 ≃ Fin (2 * t) :=
            { toFun := fun ⟨k, p⟩ => ⟨2 * k.val + p.val, by omega⟩
              invFun := fun b => (⟨b.val / 2, by omega⟩, ⟨b.val % 2, Nat.mod_lt _ (by decide)⟩)
              left_inv := fun ⟨k, p⟩ => by
                apply Prod.ext <;> (apply Fin.ext; dsimp only; omega)
              right_inv := fun b => by apply Fin.ext; dsimp only; omega }
          rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Fin.sum_univ_two, e, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, Nat.add_zero,
            rowP, colP]
          have hev : (2 * k.val) % 2 = 0 := by omega
          have hodd : ¬ (2 * k.val + 1) % 2 = 0 := by omega
          simp only [hev, hodd, ↓reduceDIte]
          congr 2
        rw [hpair, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hpure.1 k, one_mul, htri_pure]
        simp only [Pi.add_apply]
        ring
      rw [hsum_tri]
      ring
    have herr_eq :
        errors C = ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j =>
          H i j ≠ xor (xor (QP i) (RP j)) (decide ((∑ b : Fin (2 * t), rowP i b * colP j b) = 1)))).card := by
      dsimp only [errors]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      ext j
      simp [hval_sylv]
    have hinj_or := signed_sample_not_both_noninj hs H hH rowP colP QP RP (by rw [← herr_eq]; exact herr)
    have hcard_eq : Fintype.card (Fin N) = Fintype.card V := by
      rw [Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin, hN2s]
    rcases hinj_or with hrinj | hcinj
    · let rowE : Fin N ≃ V := Equiv.ofBijective rowP
        ((Fintype.bijective_iff_injective_and_card rowP).mpr ⟨hrinj, hcard_eq⟩)
      have hHswap := hadamard_swap hNpos hH
      have herr_swap :
          (∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j =>
            Function.swap H i j ≠ xor (xor (RP i) (QP j))
              (decide ((∑ b : Fin (2 * t), colP i b * rowE j b) = 1)))).card) = errors C := by
        dsimp only [errors]
        have hcomm : ∀ i j : Fin N,
            (Function.swap H i j ≠ xor (xor (RP i) (QP j))
              (decide ((∑ b : Fin (2 * t), colP i b * rowE j b) = 1))) ↔
            (H j i ≠ value C j i) := by
          intro i j
          rw [hval_sylv j i]
          have hdot : ∑ b : Fin (2 * t), colP i b * rowE j b =
              ∑ b : Fin (2 * t), rowP j b * colP i b :=
            Finset.sum_congr rfl fun b _ => mul_comm _ _
          rw [hdot]
          dsimp only [Function.swap]
          cases H j i <;> cases QP j <;> cases RP i <;>
            cases decide ((∑ b : Fin (2 * t), rowP j b * colP i b) = 1) <;> decide
        simp_rw [hcomm]
        have h1 : ∀ f : Fin N → Fin N → Prop, [DecidableRel f] →
            ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => f j i)).card =
            ∑ j : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun i => f j i)).card := by
          intro f _
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          exact Finset.sum_comm
        exact h1 (fun j i => H j i ≠ value C j i)
      have hgap := signed_sampling_gap_col_bij (Function.swap H) hHswap colP rowE RP QP
        (by rw [herr_swap]; omega)
      rcases hgap with ⟨⟨colH, rowH, RH, QH, hHsw⟩, hcls⟩
      have hHsylv : sylvester := by
        refine ⟨rowH, colH, QH, RH, fun i j => ?_⟩
        have h1 := hHsw j i
        dsimp only [Function.swap] at h1
        rw [h1]
        have hdot : ∑ b : Fin (2 * t), colH j b * rowH i b =
            ∑ b : Fin (2 * t), rowH i b * colH j b :=
          Finset.sum_congr rfl fun b _ => mul_comm _ _
        rw [hdot]
        cases QH i <;> cases RH j <;>
          cases decide ((∑ b : Fin (2 * t), rowH i b * colH j b) = 1) <;> decide
      refine ⟨hHsylv, ?_⟩
      rcases hcls with h0 | ⟨h2e, i, j, hij, flip, hcl⟩
      · left
        dsimp only at h0
        rw [herr_swap] at h0
        exact h0
      · right
        dsimp only at h2e
        rw [herr_swap] at h2e
        refine ⟨h2e, Or.inr ⟨i, j, hij, flip, fun x y => ?_⟩⟩
        have h1 := hcl x y
        dsimp only [Function.swap] at h1 ⊢
        rw [hval_sylv y x]
        have hdot : ∑ b : Fin (2 * t), colP x b * rowE y b =
            ∑ b : Fin (2 * t), rowP y b * colP x b :=
          Finset.sum_congr rfl fun b _ => mul_comm _ _
        rw [← hdot]
        have hxor : xor (xor (QP y) (RP x)) (decide ((∑ b : Fin (2 * t), colP x b * rowE y b) = 1)) =
            xor (xor (RP x) (QP y)) (decide ((∑ b : Fin (2 * t), colP x b * rowE y b) = 1)) := by
          cases QP y <;> cases RP x <;>
            cases decide ((∑ b : Fin (2 * t), colP x b * rowE y b) = 1) <;> decide
        rw [hxor]
        exact h1
    · let colE : Fin N ≃ V := Equiv.ofBijective colP
        ((Fintype.bijective_iff_injective_and_card colP).mpr ⟨hcinj, hcard_eq⟩)
      have hcolE_apply : ∀ y, colE y = colP y := fun _ => rfl
      have hgap := signed_sampling_gap_col_bij H hH rowP colE QP RP
        (by dsimp only; simp_rw [hcolE_apply]; rw [← herr_eq]; omega)
      rcases hgap with ⟨hHsylv, hcls⟩
      refine ⟨hHsylv, ?_⟩
      rcases hcls with h0 | ⟨h2e, i, j, hij, flip, hcl⟩
      · left
        dsimp only at h0
        simp_rw [hcolE_apply] at h0
        rw [herr_eq]
        exact h0
      · right
        dsimp only at h2e
        simp_rw [hcolE_apply] at h2e
        refine ⟨by rw [herr_eq]; exact h2e, Or.inl ⟨i, j, hij, flip, fun x y => ?_⟩⟩
        rw [hval_sylv x y]
        exact hcl x y
  · rintro ⟨row, col, Q, R, hHsylv⟩
    let b0 : Fin (2 * s) := ⟨0, by omega⟩
    let b1 : Fin (2 * s) := ⟨1, by omega⟩
    have hb01 : b0 ≠ b1 := by intro h; have := congrArg Fin.val h; dsimp [b0, b1] at this; omega
    let e0 : V := Pi.single b0 1
    let e1 : V := Pi.single b1 1
    have hadd : ∀ b : Fin (2 * s), (e0 + e1) b = e0 b + e1 b := fun _ => rfl
    have hzero : ∀ b : Fin (2 * s), (0 : V) b = 0 := fun _ => rfl
    have he0_ne0 : e0 ≠ 0 := by
      intro h
      have := congrFun h b0
      simp only [e0, hzero, Pi.single_eq_same] at this
      exact one_ne_zero this
    have he01_ne0 : e0 + e1 ≠ 0 := by
      intro h
      have := congrFun h b0
      have hb01' : b0 ≠ b1 := hb01
      simp only [hadd, hzero, e0, e1, Pi.single_eq_same, Pi.single_eq_of_ne hb01', add_zero] at this
      exact one_ne_zero this
    constructor
    · let i0 : Fin N := row.symm 0
      let f1 : Fin N → V := fun x => if x = i0 then e0 else row x
      obtain ⟨C1, h1len, h1back, h1nl, h1ev⟩ := exists_circuit_signed_sylvester f1 col Q R
      refine ⟨C1, ⟨h1len, h1back, h1nl⟩, ?_⟩
      dsimp only [errors, value]
      have hrow_err : ∀ i : Fin N,
          ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C1.eval (oneEach i j))).card =
            if i = i0 then ((Finset.univ : Finset V).filter (fun v => (∑ b : Fin (2 * s), e0 b * v b) = 1)).card
            else 0 := by
        intro i
        by_cases hi : i = i0
        · subst i
          simp only [↓reduceIte]
          refine Finset.card_bij (fun j _ => col j) ?_ ?_ ?_
          · intro j hj
            have hne : H i0 j ≠ C1.eval (oneEach i0 j) := (Finset.mem_filter.mp hj).2
            rw [hHsylv i0 j, h1ev i0 j] at hne
            simp only [f1, ↓reduceIte, i0, Equiv.apply_symm_apply, hzero, zero_mul,
              Finset.sum_const_zero] at hne
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rcases z2_zero_or_one (∑ b : Fin (2 * s), e0 b * col j b) with h0 | h1
            · exfalso; apply hne; simp [h0]
            · exact h1
          · intro j1 _ j2 _ h; exact col.injective h
          · intro v hv
            have hv1 : (∑ b : Fin (2 * s), e0 b * v b) = 1 := (Finset.mem_filter.mp hv).2
            refine ⟨col.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, col.apply_symm_apply v⟩
            rw [hHsylv i0 (col.symm v), h1ev i0 (col.symm v)]
            simp only [f1, ↓reduceIte, i0, Equiv.apply_symm_apply, hzero, zero_mul,
              Finset.sum_const_zero, hv1]
            cases Q (row.symm 0) <;> cases R (col.symm v) <;> decide
        · simp only [hi, ↓reduceIte]
          rw [Finset.card_eq_zero]
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            not_not]
          rw [hHsylv i j, h1ev i j]
          simp [f1, hi]
      simp_rw [hrow_err]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hhalf := card_filter_half_vec e0 he0_ne0
      rw [hN2s] at hhalf
      exact hhalf
    · let i0 : Fin N := row.symm e0
      let j0 : Fin N := col.symm e0
      let f2 : Fin N → V := fun x => if x = i0 then e1 else row x
      let g2 : Fin N → V := fun y => if y = j0 then e1 else col y
      obtain ⟨C2, h2len, h2back, h2nl, h2ev⟩ := exists_circuit_signed_sylvester f2 g2 Q R
      refine ⟨C2, ⟨h2len, h2back, h2nl⟩, ?_⟩
      dsimp only [errors, value]
      have hdot_e00 : (∑ b : Fin (2 * s), e0 b * e0 b) = 1 := by
        simp [e0, Pi.single_apply]
      have hdot_e11 : (∑ b : Fin (2 * s), e1 b * e1 b) = 1 := by
        simp [e1, Pi.single_apply]
      have hdot_e01 : (∑ b : Fin (2 * s), e0 b * e1 b) = 0 := by
        simp [e0, e1, Pi.single_apply, hb01.symm]
      have hiff_err : ∀ i j : Fin N,
          (H i j ≠ C2.eval (oneEach i j)) ↔
          (∑ b : Fin (2 * s), row i b * col j b) ≠ (∑ b : Fin (2 * s), f2 i b * g2 j b) := by
        intro i j
        rw [hHsylv i j, h2ev i j]
        rcases z2_zero_or_one (∑ b : Fin (2 * s), row i b * col j b) with h1 | h1 <;>
          rcases z2_zero_or_one (∑ b : Fin (2 * s), f2 i b * g2 j b) with h2 | h2 <;>
          cases Q i <;> cases R j <;> simp [h1, h2]
      have hrow_i0 :
          2 * (((Finset.univ : Finset (Fin N)).filter (fun j => H i0 j ≠ C2.eval (oneEach i0 j))).card + 1) = N := by
        let S := (Finset.univ : Finset V).filter (fun v => (∑ b : Fin (2 * s), (e0 + e1) b * v b) = 1)
        have hSe0 : e0 ∈ S := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [hadd, add_mul, Finset.sum_add_distrib, hdot_e00]
          have h10 : (∑ b : Fin (2 * s), e1 b * e0 b) = 0 := by
            trans ∑ b : Fin (2 * s), e0 b * e1 b
            · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
            · exact hdot_e01
          rw [h10, add_zero]
        have hbij :
            ((Finset.univ : Finset (Fin N)).filter (fun j => H i0 j ≠ C2.eval (oneEach i0 j))).card =
              (S.erase e0).card := by
          refine Finset.card_bij (fun j _ => col j) ?_ ?_ ?_
          · intro j hj
            have hne := (hiff_err i0 j).mp (Finset.mem_filter.mp hj).2
            have hj_ne : j ≠ j0 := by
              intro h
              subst h
              apply hne
              simp [i0, j0, f2, g2, hdot_e00, hdot_e11]
            refine Finset.mem_erase.mpr ⟨fun h => hj_ne (col.injective (by simp [j0, h])), ?_⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            simp only [i0, f2, g2, Equiv.apply_symm_apply, hj_ne, ↓reduceIte] at hne
            have hsum : ∑ b : Fin (2 * s), (e0 + e1) b * col j b =
                (∑ b : Fin (2 * s), e0 b * col j b) + (∑ b : Fin (2 * s), e1 b * col j b) := by
              simp only [hadd, add_mul, Finset.sum_add_distrib]
            rw [hsum]
            rcases z2_zero_or_one (∑ b : Fin (2 * s), e0 b * col j b) with ha | ha <;>
              rcases z2_zero_or_one (∑ b : Fin (2 * s), e1 b * col j b) with hb | hb <;>
              simp_all
          · intro j1 _ j2 _ h; exact col.injective h
          · intro v hv
            rcases Finset.mem_erase.mp hv with ⟨hvne, hvS⟩
            have hv1 : (∑ b : Fin (2 * s), (e0 + e1) b * v b) = 1 := (Finset.mem_filter.mp hvS).2
            have hjne : col.symm v ≠ j0 := fun h => hvne (by have := congrArg col h; simpa [j0] using this)
            refine ⟨col.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, col.apply_symm_apply v⟩
            rw [hiff_err]
            simp only [i0, f2, g2, Equiv.apply_symm_apply, hjne, ↓reduceIte]
            intro heq
            have hsum : ∑ b : Fin (2 * s), (e0 + e1) b * v b =
                (∑ b : Fin (2 * s), e0 b * v b) + (∑ b : Fin (2 * s), e1 b * v b) := by
              simp only [hadd, add_mul, Finset.sum_add_distrib]
            rw [hsum, heq, z2_add_self] at hv1
            exact zero_ne_one hv1
        rw [hbij, Finset.card_erase_of_mem hSe0]
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨e0, hSe0⟩
        have hhalf := card_filter_half_vec (e0 + e1) he01_ne0
        rw [hN2s] at hhalf
        change 2 * S.card = N at hhalf
        omega
      have hrow_other : ∀ i : Fin N, i ≠ i0 →
          ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j))).card =
            if (∑ b : Fin (2 * s), (e0 + e1) b * row i b) = 1 then 1 else 0 := by
        intro i hi
        have hfilt : (Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j)) =
            if (∑ b : Fin (2 * s), (e0 + e1) b * row i b) = 1 then {j0} else ∅ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff_err]
          by_cases hj : j = j0
          · subst hj
            have hsum : ∑ b : Fin (2 * s), (e0 + e1) b * row i b =
                (∑ b : Fin (2 * s), row i b * e0 b) + (∑ b : Fin (2 * s), row i b * e1 b) := by
              simp only [hadd, add_mul, Finset.sum_add_distrib]
              congr 1 <;> exact Finset.sum_congr rfl fun b _ => mul_comm _ _
            simp only [f2, g2, hi, j0, Equiv.apply_symm_apply, ↓reduceIte, hsum]
            rcases z2_zero_or_one (∑ b : Fin (2 * s), row i b * e0 b) with ha | ha <;>
              rcases z2_zero_or_one (∑ b : Fin (2 * s), row i b * e1 b) with hb | hb <;>
              simp [ha, hb, (by decide : (1 : ZMod 2) + 1 = 0)]
          · simp only [f2, g2, hi, hj, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
            split_ifs <;> simp [hj]
        rw [hfilt]
        split_ifs <;> simp
      have hsum_split :
          ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j))).card =
            ((Finset.univ : Finset (Fin N)).filter (fun j => H i0 j ≠ C2.eval (oneEach i0 j))).card +
            ∑ i ∈ Finset.univ.erase i0,
              ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j))).card :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)).symm
      rw [hsum_split]
      have hother_sum :
          2 * ((∑ i ∈ Finset.univ.erase i0,
            ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j))).card) + 1) = N := by
        let S := (Finset.univ : Finset V).filter (fun v => (∑ b : Fin (2 * s), (e0 + e1) b * v b) = 1)
        have hSe0 : e0 ∈ S := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [hadd, add_mul, Finset.sum_add_distrib, hdot_e00]
          have h10 : (∑ b : Fin (2 * s), e1 b * e0 b) = 0 := by
            trans ∑ b : Fin (2 * s), e0 b * e1 b
            · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
            · exact hdot_e01
          rw [h10, add_zero]
        have hrew :
            ∑ i ∈ Finset.univ.erase i0,
              ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ C2.eval (oneEach i j))).card =
            ((Finset.univ.erase i0).filter (fun i => (∑ b : Fin (2 * s), (e0 + e1) b * row i b) = 1)).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          refine Finset.sum_congr rfl fun i hi => ?_
          exact hrow_other i (Finset.mem_erase.mp hi).1
        rw [hrew]
        have hbij :
            ((Finset.univ.erase i0).filter (fun i => (∑ b : Fin (2 * s), (e0 + e1) b * row i b) = 1)).card =
              (S.erase e0).card := by
          refine Finset.card_bij (fun i _ => row i) ?_ ?_ ?_
          · intro i hi
            rcases Finset.mem_filter.mp hi with ⟨hier, h1⟩
            have hine : i ≠ i0 := (Finset.mem_erase.mp hier).1
            exact Finset.mem_erase.mpr ⟨fun h => hine (row.injective (by simp [i0, h])),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
          · intro i1 _ i2 _ h; exact row.injective h
          · intro v hv
            rcases Finset.mem_erase.mp hv with ⟨hvne, hvS⟩
            have hine : row.symm v ≠ i0 := fun h => hvne (by have := congrArg row h; simpa [i0] using this)
            refine ⟨row.symm v, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hine, Finset.mem_univ _⟩, ?_⟩,
              row.apply_symm_apply v⟩
            simpa [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hvS).2
        rw [hbij, Finset.card_erase_of_mem hSe0]
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨e0, hSe0⟩
        have hhalf := card_filter_half_vec (e0 + e1) he01_ne0
        rw [hN2s] at hhalf
        change 2 * S.card = N at hhalf
        omega
      omega

end PEqualNP.Outside.L_lib_634_aux

theorem PEqualNP.Outside.L_lib_634 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
∀ s : ℕ, 2 ≤ s →
  let N := 4^s
  let V := Fin (2*s) → ZMod 2
  ∀ H : Fin N → Fin N → Bool,
  (∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun v => H a v ≠ H b v)).card = N) →
  let sylvester := ∃ (row col : Fin N ≃ V) (Q R : Fin N → Bool),
    ∀ i j, H i j = xor (xor (Q i) (R j))
      (decide ((∑ b : Fin (2*s), row i b * col j b) = 1))
  let clone := fun (A B : Fin N → Fin N → Bool) =>
    ∃ i j : Fin N, i ≠ j ∧ ∃ flip : Bool, ∀ x y,
      B x y = if x = i then xor flip (A j y) else A x y
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.gates.countP nonlinear ≤ s
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N) =>
    C.eval (PEqualNP.Represents.oneEach x y)
  let errors := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ value C i j)).card
  (∀ C, valid C → errors C + 2 < N →
    sylvester ∧ (errors C = 0 ∨
      (2 * errors C = N ∧ (clone H (value C) ∨ clone (Function.swap H) (Function.swap (value C)))))) ∧
  (sylvester → (∃ C, valid C ∧ 2 * errors C = N) ∧ (∃ C, valid C ∧ errors C + 2 = N)) := by
  exact PEqualNP.Outside.L_lib_634_aux.main
