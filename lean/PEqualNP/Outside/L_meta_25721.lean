import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25721_aux

open Finset

variable {n : ℕ}


def rowR (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) (i : Fin n) : Fin n → ZMod 2 :=
  fun j => if j ∈ R then M i j else 0

noncomputable def rho (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (rowR M R '' (R : Set (Fin n))))

def deg (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) (i : Fin n) : ℕ :=
  (R.filter (fun j => M i j = 1)).card

def projR (R : Finset (Fin n)) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v := fun j => if j ∈ R then v j else 0
  map_add' v w := by funext j; by_cases h : j ∈ R <;> simp [h]
  map_smul' c v := by funext j; by_cases h : j ∈ R <;> simp [h]

lemma zmod2_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

lemma zmod2_eq : ∀ {a b : ZMod 2}, (a = 1 ↔ b = 1) → a = b := by
  decide

lemma rho_drop (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) (i : Fin n) (hi : i ∈ R)
    (hii : M i i = 1) :
    rho M (R \ R.filter (fun j => M i j = 1)) + 1 ≤ rho M R := by
  set B := R.filter (fun j => M i j = 1) with hB
  set R' := R \ B with hR'
  set U := Submodule.span (ZMod 2) (rowR M R '' (R : Set (Fin n))) with hU
  set π := projR (n := n) R' with hπ
  have hle : Submodule.span (ZMod 2) (rowR M R' '' (R' : Set (Fin n))) ≤ U.map π := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hjR : j ∈ R := (Finset.mem_sdiff.mp hj).1
    refine ⟨rowR M R j, Submodule.subset_span ⟨j, hjR, rfl⟩, ?_⟩
    funext l
    simp only [hπ, projR, rowR, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hl : l ∈ R'
    · have : l ∈ R := (Finset.mem_sdiff.mp hl).1
      simp [hl, this]
    · simp [hl]
  have hxU : rowR M R i ∈ U := Submodule.subset_span ⟨i, hi, rfl⟩
  have hx : (⟨rowR M R i, hxU⟩ : U) ∈ LinearMap.ker (π.domRestrict U) := by
    rw [LinearMap.mem_ker]
    funext l
    simp only [LinearMap.domRestrict_apply, hπ, projR, rowR, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_zero, Pi.zero_apply]
    by_cases hl : l ∈ R'
    · have h1 : l ∈ R := (Finset.mem_sdiff.mp hl).1
      have h2 : l ∉ B := (Finset.mem_sdiff.mp hl).2
      have h3 : M i l ≠ 1 := fun h => h2 (Finset.mem_filter.mpr ⟨h1, h⟩)
      simp [hl, h1, zmod2_ne_one h3]
    · simp [hl]
  have hx0 : (⟨rowR M R i, hxU⟩ : U) ≠ 0 := by
    intro h
    have := congrArg (fun x : U => (x : Fin n → ZMod 2) i) h
    simp [rowR, hi, hii] at this
  have hs1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {(⟨rowR M R i, hxU⟩ : U)}) = 1 :=
    finrank_span_singleton hx0
  have hs2 := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)
  have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict U)
  rw [LinearMap.range_domRestrict] at hrn
  have h1 := Submodule.finrank_mono hle
  have e1 : rho M R = Module.finrank (ZMod 2) U := rfl
  have e2 : rho M R' = Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (rowR M R' '' (R' : Set (Fin n)))) := rfl
  rw [e1, e2]
  omega

lemma deg_pos (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) (i : Fin n) (hi : i ∈ R)
    (hii : M i i = 1) : 0 < deg M R i :=
  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hii⟩⟩

lemma deg_mono (M : Fin n → Fin n → ZMod 2) {R S : Finset (Fin n)} (h : S ⊆ R) (i : Fin n) :
    deg M S i ≤ deg M R i :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem bound (M : Fin n → Fin n → ZMod 2) : ∀ (k : ℕ) (R : Finset (Fin n)), R.card ≤ k →
    (∀ i ∈ R, M i i = 1) → ∑ i ∈ R, (1 : ℚ) / deg M R i ≤ rho M R := by
  intro k
  induction k with
  | zero =>
    intro R hR _
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hR)]
    simp
  | succ k ih =>
    intro R hR hdiag
    rcases R.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image R (deg M R) hne
    set B := R.filter (fun j => M i j = 1) with hB
    set R' := R \ B with hR'
    have hBR : B ⊆ R := Finset.filter_subset _ _
    have hiB : i ∈ B := Finset.mem_filter.mpr ⟨hi, hdiag i hi⟩
    have hcard : R'.card ≤ k := by
      have : R'.card < R.card := Finset.card_lt_card (Finset.sdiff_ssubset hBR ⟨i, hiB⟩)
      omega
    have hdiag' : ∀ j ∈ R', M j j = 1 := fun j hj => hdiag j (Finset.mem_sdiff.mp hj).1
    have ih' := ih R' hcard hdiag'
    have hdrop := rho_drop M R i hi (hdiag i hi)
    have hsplit : ∑ j ∈ R, (1:ℚ) / deg M R j =
        ∑ j ∈ R', (1:ℚ) / deg M R j + ∑ j ∈ B, (1:ℚ) / deg M R j :=
      (Finset.sum_sdiff hBR).symm
    have hBsum : ∑ j ∈ B, (1:ℚ) / deg M R j ≤ 1 := by
      have hdi : deg M R i = B.card := rfl
      have hpos : (0:ℚ) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hiB⟩
      calc ∑ j ∈ B, (1:ℚ) / deg M R j ≤ ∑ j ∈ B, (1:ℚ) / deg M R i := by
            apply Finset.sum_le_sum; intro j hj
            apply one_div_le_one_div_of_le
            · rw [hdi]; exact hpos
            · exact_mod_cast hmin j (hBR hj)
        _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul, hdi]
            field_simp
    have hR'sum : ∑ j ∈ R', (1:ℚ) / deg M R j ≤ ∑ j ∈ R', (1:ℚ) / deg M R' j := by
      apply Finset.sum_le_sum; intro j hj
      apply one_div_le_one_div_of_le
      · exact_mod_cast deg_pos M R' j hj (hdiag' j hj)
      · exact_mod_cast deg_mono M Finset.sdiff_subset j
    have : (rho M R' : ℚ) + 1 ≤ rho M R := by exact_mod_cast hdrop
    linarith

theorem tight_facts (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) (hdiag : ∀ j ∈ R, M j j = 1)
    (i : Fin n) (hi : i ∈ R) (hmin : ∀ j ∈ R, deg M R i ≤ deg M R j)
    (htight : (rho M R : ℚ) ≤ ∑ j ∈ R, (1:ℚ) / deg M R j) :
    (∀ j ∈ R, M i j = 1 → deg M R j = deg M R i) ∧
    (∀ j ∈ R, M i j ≠ 1 → ∀ l ∈ R, M i l = 1 → M j l ≠ 1) ∧
    (rho M (R \ R.filter (fun j => M i j = 1)) : ℚ) ≤
      ∑ j ∈ R \ R.filter (fun j => M i j = 1),
        (1:ℚ) / deg M (R \ R.filter (fun j => M i j = 1)) j := by
  set B := R.filter (fun j => M i j = 1) with hB
  set R' := R \ B with hR'
  have hBR : B ⊆ R := Finset.filter_subset _ _
  have hiB : i ∈ B := Finset.mem_filter.mpr ⟨hi, hdiag i hi⟩
  have hdiag' : ∀ j ∈ R', M j j = 1 := fun j hj => hdiag j (Finset.mem_sdiff.mp hj).1
  have hb' := bound M R'.card R' le_rfl hdiag'
  have hdrop := rho_drop M R i hi (hdiag i hi)
  have hsplit : ∑ j ∈ R, (1:ℚ) / deg M R j =
      ∑ j ∈ R', (1:ℚ) / deg M R j + ∑ j ∈ B, (1:ℚ) / deg M R j :=
    (Finset.sum_sdiff hBR).symm
  have hdi : deg M R i = B.card := rfl
  have hpos : (0:ℚ) < B.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hiB⟩
  have hBle : ∀ j ∈ B, (1:ℚ) / deg M R j ≤ 1 / deg M R i := by
    intro j hj
    apply one_div_le_one_div_of_le
    · rw [hdi]; exact hpos
    · exact_mod_cast hmin j (hBR hj)
  have hBeq : ∑ j ∈ B, (1:ℚ) / deg M R i = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hdi]; field_simp
  have hR'le : ∀ j ∈ R', (1:ℚ) / deg M R j ≤ 1 / deg M R' j := by
    intro j hj
    apply one_div_le_one_div_of_le
    · exact_mod_cast deg_pos M R' j hj (hdiag' j hj)
    · exact_mod_cast deg_mono M Finset.sdiff_subset j
  have hBsum : ∑ j ∈ B, (1:ℚ) / deg M R j ≤ 1 := le_trans (Finset.sum_le_sum hBle) hBeq.le
  have hR'sum : ∑ j ∈ R', (1:ℚ) / deg M R j ≤ ∑ j ∈ R', (1:ℚ) / deg M R' j :=
    Finset.sum_le_sum hR'le
  have hdropQ : (rho M R' : ℚ) + 1 ≤ rho M R := by exact_mod_cast hdrop
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hij
    have hjB : j ∈ B := Finset.mem_filter.mpr ⟨hj, hij⟩
    by_contra hne
    have hlt : deg M R i < deg M R j := lt_of_le_of_ne (hmin j hj) (Ne.symm hne)
    have hstrict : ∑ j ∈ B, (1:ℚ) / deg M R j < ∑ j ∈ B, (1:ℚ) / deg M R i := by
      apply Finset.sum_lt_sum hBle
      refine ⟨j, hjB, ?_⟩
      apply one_div_lt_one_div_of_lt
      · rw [hdi]; exact hpos
      · exact_mod_cast hlt
    linarith
  · intro j hj hij l hl hil hjl
    have hjR' : j ∈ R' := Finset.mem_sdiff.mpr ⟨hj, fun h => hij (Finset.mem_filter.mp h).2⟩
    have hlB : l ∈ B := Finset.mem_filter.mpr ⟨hl, hil⟩
    have hsub : R'.filter (fun m => M j m = 1) ⊆ R.filter (fun m => M j m = 1) :=
      Finset.filter_subset_filter _ Finset.sdiff_subset
    have hlt : deg M R' j < deg M R j := by
      apply lt_of_le_of_ne (Finset.card_le_card hsub)
      intro heq
      have := Finset.eq_of_subset_of_card_le hsub (le_of_eq heq.symm)
      have hl2 : l ∈ R.filter (fun m => M j m = 1) := Finset.mem_filter.mpr ⟨hl, hjl⟩
      rw [← this] at hl2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl2).1).2 hlB
    have hstrict : ∑ j ∈ R', (1:ℚ) / deg M R j < ∑ j ∈ R', (1:ℚ) / deg M R' j := by
      apply Finset.sum_lt_sum hR'le
      refine ⟨j, hjR', ?_⟩
      apply one_div_lt_one_div_of_lt
      · exact_mod_cast deg_pos M R' j hjR' (hdiag' j hjR')
      · exact_mod_cast hlt
    linarith
  · linarith

theorem tight_equiv (M : Fin n → Fin n → ZMod 2) : ∀ (k : ℕ) (R : Finset (Fin n)), R.card ≤ k →
    (∀ i ∈ R, M i i = 1) → (rho M R : ℚ) ≤ ∑ j ∈ R, (1:ℚ) / deg M R j →
    ∀ x ∈ R, ∀ y ∈ R, M x y = 1 → ∀ l ∈ R, M x l = M y l := by
  intro k
  induction k with
  | zero =>
    intro R hR _ _ x hx
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hR)] at hx
    simp at hx
  | succ k ih =>
    intro R hR hdiag htight x hx y hy hxy l hl
    have hne : R.Nonempty := ⟨x, hx⟩
    have F0 : ∀ a ∈ R, (∀ j ∈ R, deg M R a ≤ deg M R j) → ∀ b ∈ R, M a b = 1 →
        ∀ j ∈ R, deg M R b ≤ deg M R j := by
      intro a ha hmin b hb hab j hj
      rw [(tight_facts M R hdiag a ha hmin htight).1 b hb hab]; exact hmin j hj
    have F1 : ∀ a ∈ R, (∀ j ∈ R, deg M R a ≤ deg M R j) → ∀ b ∈ R, M a b = 1 → M b a = 1 := by
      intro a ha hmin b hb hab
      by_contra hba
      exact (tight_facts M R hdiag b hb (F0 a ha hmin b hb hab) htight).2.1 a ha hba b hb
        (hdiag b hb) hab
    have F2 : ∀ a ∈ R, (∀ j ∈ R, deg M R a ≤ deg M R j) → ∀ b ∈ R, M a b = 1 →
        ∀ m ∈ R, M a m = 1 → M b m = 1 := by
      intro a ha hmin b hb hab m hm ham
      by_contra hbm
      have hma := F1 a ha hmin m hm ham
      have hba := F1 a ha hmin b hb hab
      exact (tight_facts M R hdiag b hb (F0 a ha hmin b hb hab) htight).2.1 m hm hbm a ha hba hma
    have F3 : ∀ a ∈ R, (∀ j ∈ R, deg M R a ≤ deg M R j) → ∀ b ∈ R, M a b = 1 →
        ∀ m ∈ R, M a m = M b m := by
      intro a ha hmin b hb hab m hm
      apply zmod2_eq
      constructor
      · exact F2 a ha hmin b hb hab m hm
      · exact F2 b hb (F0 a ha hmin b hb hab) a ha (F1 a ha hmin b hb hab) m hm
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image R (deg M R) hne
    obtain ⟨_, T2, T3⟩ := tight_facts M R hdiag i hi hmin htight
    by_cases hix : M i x = 1
    · exact F3 x hx (F0 i hi hmin x hx hix) y hy hxy l hl
    · have hiy : M i y ≠ 1 := fun h => T2 x hx hix y hy h hxy
      have memR' : ∀ z ∈ R, M i z ≠ 1 → z ∈ R \ R.filter (fun j => M i j = 1) :=
        fun z hz hiz => Finset.mem_sdiff.mpr ⟨hz, fun h => hiz (Finset.mem_filter.mp h).2⟩
      by_cases hil : M i l = 1
      · rw [zmod2_ne_one (T2 x hx hix l hl hil), zmod2_ne_one (T2 y hy hiy l hl hil)]
      · have hBR : R.filter (fun j => M i j = 1) ⊆ R := Finset.filter_subset _ _
        have hiB : i ∈ R.filter (fun j => M i j = 1) := Finset.mem_filter.mpr ⟨hi, hdiag i hi⟩
        have hcard : (R \ R.filter (fun j => M i j = 1)).card ≤ k := by
          have : (R \ R.filter (fun j => M i j = 1)).card < R.card :=
            Finset.card_lt_card (Finset.sdiff_ssubset hBR ⟨i, hiB⟩)
          omega
        exact ih _ hcard (fun j hj => hdiag j (Finset.mem_sdiff.mp hj).1) T3 x (memR' x hx hix)
          y (memR' y hy hiy) hxy l (memR' l hl hil)

/-- The numeric core: lower bound and equality structure. -/
theorem matrix_main (s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (M : Fin n → Fin n → ZMod 2)
    (hdiag : ∀ i, M i i = 1) (hrank : rho M univ ≤ s) :
    (s - n % s) * (n / s) * (n / s - 1) + n % s * (n / s + 1) * (n / s) + n ≤ ∑ i, deg M univ i ∧
    (∑ i, deg M univ i = (s - n % s) * (n / s) * (n / s - 1) + n % s * (n / s + 1) * (n / s) + n →
      (∀ i, deg M univ i = n / s ∨ deg M univ i = n / s + 1) ∧
      (∀ x y l, M x y = 1 → M x l = M y l) ∧ ∑ i, (1:ℚ) / deg M univ i = s) := by
  set q := n / s with hq
  set r := n % s with hr
  have hnqr : s * q + r = n := Nat.div_add_mod n s
  have hrs : r < s := Nat.mod_lt n hs
  have hq1 : 1 ≤ q := by
    rw [hq]; exact (Nat.one_le_div_iff hs).mpr hsn
  have hdpos : ∀ i, 0 < deg M univ i := fun i => deg_pos M univ i (Finset.mem_univ i) (hdiag i)
  have hb := bound M n univ (by simp) (fun i _ => hdiag i)
  have hbs : ∑ i, (1:ℚ) / deg M univ i ≤ s := le_trans hb (by exact_mod_cast hrank)
  -- the cast of best + n
  have hbest : (((s - r) * q * (q - 1) + r * (q + 1) * q + n : ℕ) : ℚ) =
      n * (2 * q + 1) - q * (q + 1) * s := by
    have e1 : ((s - r : ℕ) : ℚ) = s - r := by rw [Nat.cast_sub hrs.le]
    have e2 : ((q - 1 : ℕ) : ℚ) = q - 1 := by rw [Nat.cast_sub hq1]; simp
    have e3 : (n : ℚ) = s * q + r := by rw [← hnqr]; push_cast; ring
    push_cast [e1, e2]
    rw [e3]; ring
  -- per-term inequality
  set f : Fin n → ℚ := fun i => (deg M univ i : ℚ) + q * (q + 1) / deg M univ i - (2 * q + 1)
    with hf
  have hfnn : ∀ i, 0 ≤ f i := by
    intro i
    have hD : (0:ℚ) < deg M univ i := by exact_mod_cast hdpos i
    have key : (0:ℚ) ≤ ((deg M univ i : ℚ) - q) * ((deg M univ i : ℚ) - q - 1) := by
      rcases le_or_gt (deg M univ i) q with h | h
      · have h' : (deg M univ i : ℚ) ≤ q := by exact_mod_cast h
        nlinarith
      · have h' : (q : ℚ) + 1 ≤ deg M univ i := by exact_mod_cast h
        nlinarith
    have : f i = ((deg M univ i : ℚ) - q) * ((deg M univ i : ℚ) - q - 1) / deg M univ i := by
      rw [hf]; field_simp; ring
    rw [this]; positivity
  have hfsum : ∑ i, f i = (∑ i, (deg M univ i : ℚ)) + q * (q + 1) * ∑ i, (1:ℚ) / deg M univ i
      - n * (2 * q + 1) := by
    have h1 : ∀ i, f i = (deg M univ i : ℚ) + (q * (q+1)) * (1 / deg M univ i) - (2*q+1) := by
      intro i; rw [hf]; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum0 : 0 ≤ ∑ i, f i := Finset.sum_nonneg (fun i _ => hfnn i)
  have hqq : (0:ℚ) < q * (q + 1) := by
    have : (1:ℚ) ≤ q := by exact_mod_cast hq1
    nlinarith
  have hcastsum : ((∑ i, deg M univ i : ℕ) : ℚ) = ∑ i, (deg M univ i : ℚ) := by push_cast; rfl
  refine ⟨?_, ?_⟩
  · have : (((s - r) * q * (q - 1) + r * (q + 1) * q + n : ℕ) : ℚ) ≤ ((∑ i, deg M univ i : ℕ) : ℚ) := by
      rw [hbest, hcastsum]
      nlinarith
    exact_mod_cast this
  · intro heq
    have heqQ : ((∑ i, deg M univ i : ℕ) : ℚ) = n * (2 * q + 1) - q * (q + 1) * s := by
      rw [heq, hbest]
    rw [hcastsum] at heqQ
    have hS : ∑ i, (1:ℚ) / deg M univ i = s := by nlinarith
    have hf0 : ∑ i, f i = 0 := by rw [hfsum, heqQ, hS]; ring
    have hfi : ∀ i, f i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hfnn i)).mp hf0 i (Finset.mem_univ i)
    refine ⟨?_, ?_, hS⟩
    · intro i
      have hD : (0:ℚ) < deg M univ i := by exact_mod_cast hdpos i
      have h0 : ((deg M univ i : ℚ) - q) * ((deg M univ i : ℚ) - q - 1) = 0 := by
        have := hfi i
        rw [hf] at this
        simp only at this
        field_simp at this
        linear_combination this
      rcases mul_eq_zero.mp h0 with h | h
      · left; exact_mod_cast (sub_eq_zero.mp h)
      · right
        have : (deg M univ i : ℚ) = q + 1 := by linarith
        exact_mod_cast this
    · intro x y l hxy
      have htight : (rho M univ : ℚ) ≤ ∑ j ∈ univ, (1:ℚ) / deg M univ j := by
        rw [hS]; exact_mod_cast hrank
      exact tight_equiv M n univ (by simp) (fun i _ => hdiag i) htight x (Finset.mem_univ x)
        y (Finset.mem_univ y) hxy l (Finset.mem_univ l)

theorem mk_hash (M : Fin n → Fin n → ZMod 2) (s : ℕ) (hdiag : ∀ i, M i i = 1)
    (hrow : ∀ x y l, M x y = 1 → M x l = M y l) (hsum : ∑ i, (1:ℚ) / deg M univ i = s) :
    ∃ h : Fin n → Fin s, (∀ i j, M i j = 1 ↔ h i = h j) ∧ ∀ v, ∃ u, h u = v := by
  have hsymm : ∀ x y, M x y = 1 → M y x = 1 := fun x y hxy => by
    have := hrow x y x hxy; rw [hdiag x] at this; exact this.symm
  have htrans : ∀ x y l, M x y = 1 → M y l = 1 → M x l = 1 := fun x y l hxy hyl => by
    rw [hrow x y l hxy]; exact hyl
  let cls : Fin n → Finset (Fin n) := fun x => univ.filter (fun j => M x j = 1)
  have hne : ∀ x, (cls x).Nonempty := fun x => ⟨x, by simp [cls, hdiag x]⟩
  have hcls : ∀ x y, M x y = 1 → cls x = cls y := by
    intro x y hxy; ext l; simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hrow x y l hxy]
  let rep : Fin n → Fin n := fun x => (cls x).min' (hne x)
  have hrep_rel : ∀ x, M x (rep x) = 1 := fun x => by
    have := Finset.min'_mem (cls x) (hne x)
    simpa [cls] using this
  have hrep_eq : ∀ x y, M x y = 1 → rep x = rep y := by
    intro x y hxy
    simp only [rep, hcls x y hxy]
  have hrep_iff : ∀ x y, rep x = rep y ↔ M x y = 1 := by
    intro x y; constructor
    · intro h; have h1 := hrep_rel x; have h2 := hrep_rel y; rw [← h] at h2
      exact htrans x (rep x) y h1 (hsymm _ _ h2)
    · exact hrep_eq x y
  set Reps := univ.image rep with hReps
  have hcard : Reps.card = s := by
    have key : ∑ i, (1:ℚ) / deg M univ i =
        ∑ r ∈ Reps, ∑ i ∈ univ.filter (fun i => rep i = r), (1:ℚ) / deg M univ i :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem rep (Finset.mem_univ i)) _).symm
    have inner : ∀ r ∈ Reps,
        ∑ i ∈ univ.filter (fun i => rep i = r), (1:ℚ) / deg M univ i = 1 := by
      intro r hr
      obtain ⟨x0, _, rfl⟩ := Finset.mem_image.mp hr
      have hfib : univ.filter (fun i => rep i = rep x0) = cls x0 := by
        ext i; simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hrep_iff]; exact ⟨hsymm i x0, hsymm x0 i⟩
      rw [hfib]
      have hdeg : ∀ i ∈ cls x0, deg M univ i = (cls x0).card := by
        intro i hi
        simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        show (cls i).card = (cls x0).card
        rw [hcls i x0 (hsymm _ _ hi)]
      rw [Finset.sum_congr rfl (fun i hi => by rw [hdeg i hi]), Finset.sum_const, nsmul_eq_mul]
      have : (0:ℚ) < (cls x0).card := by exact_mod_cast (hne x0).card_pos
      field_simp
    rw [Finset.sum_congr rfl inner, Finset.sum_const, nsmul_eq_mul, mul_one] at key
    exact_mod_cast (key.symm.trans hsum)
  refine ⟨fun i => Fin.cast hcard
    (Reps.equivFin ⟨rep i, Finset.mem_image_of_mem rep (Finset.mem_univ i)⟩), ?_, ?_⟩
  · intro i j
    rw [← hrep_iff]
    constructor
    · intro h
      exact congrArg (fun z => Fin.cast hcard (Reps.equivFin z)) (Subtype.ext h)
    · intro h
      simpa using h
  · intro v
    obtain ⟨⟨r, hr⟩, hv⟩ := Reps.equivFin.surjective (Fin.cast hcard.symm v)
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨u, ?_⟩
    simp only [hv]
    simp

lemma best_eq (s r q : ℕ) (hrs : r ≤ s) :
    (s - r) * q * (q - 1) + r * (q + 1) * q = s * (q * (q - 1)) + 2 * q * r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [Nat.add_sub_cancel_left]
  cases q with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; ring

theorem count_from_hash (s : ℕ) (hs : 0 < s) (h : Fin n → Fin s)
    (hsz : ∀ v, (univ.filter (fun u => h u = v)).card = n / s ∨
      (univ.filter (fun u => h u = v)).card = n / s + 1) :
    ∑ i, ((univ.erase i).filter (fun j => h i = h j)).card =
      (s - n % s) * (n / s) * (n / s - 1) + n % s * (n / s + 1) * (n / s) := by
  set q := n / s with hq
  set r := n % s with hr
  have hnqr : s * q + r = n := Nat.div_add_mod n s
  have hrs : r < s := Nat.mod_lt n hs
  set c : Fin s → ℕ := fun v => (univ.filter (fun u => h u = v)).card with hc
  have h1 : ∀ i, ((univ.erase i).filter (fun j => h i = h j)).card = c (h i) - 1 := by
    intro i
    rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp)]
    simp only [hc]
    congr 2
    ext j; simp [eq_comm]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  have h2 : ∀ F : Fin s → ℕ, ∑ i, F (h i) = ∑ v, c v * F v := by
    intro F
    rw [← Finset.sum_fiberwise univ h (fun i => F (h i))]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
      smul_eq_mul]
  rw [h2 (fun v => c v - 1)]
  have h3 : ∑ v, c v = n := by
    have := h2 (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    exact this.symm
  set ind : Fin s → ℕ := fun v => if c v = q + 1 then 1 else 0 with hind
  have e1 : ∀ v, c v = q + ind v := by
    intro v; rcases hsz v with hv | hv
    · have : c v = q := hv
      simp [hind, this]
    · have : c v = q + 1 := hv
      simp [hind, this]
  have e2 : ∀ v, c v * (c v - 1) = q * (q - 1) + 2 * q * ind v := by
    intro v; rcases hsz v with hv | hv
    · have : c v = q := hv
      simp [hind, this]
    · have : c v = q + 1 := hv
      simp only [hind, this, if_true]
      cases q with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl (fun v _ => e2 v), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  have hA : ∑ v, ind v = r := by
    rw [Finset.sum_congr rfl (fun v _ => e1 v), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    omega
  rw [hA, best_eq s r q hrs.le]

section circuits

open PEqualNP.CircuitLowerBounds

def nonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def stepD (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bz (b : Bool) : ZMod 2 := if b then 1 else 0

def Sep (W : Fin n → Fin n → ZMod 2) : Prop := ∃ f g : Fin n → ZMod 2, ∀ a b, W a b = f a + g b

def Form (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (W : Fin n → Fin n → ZMod 2) : Prop :=
  ∃ g : Fin n → ZMod 2, ∀ a, (fun b => W a b - g b) ∈ V

def one : Fin n → ZMod 2 := fun _ => 1

def Inv (ws : Fin n → Fin n → List Bool) (ds : List ℕ)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  (∀ a b, (ws a b).length = ds.length) ∧ one ∈ V ∧
  ∀ i, (ds.getD i 0 = 0 → Sep (fun a b => bz ((ws a b).getD i false))) ∧
       (ds.getD i 0 ≤ 1 → Form V (fun a b => bz ((ws a b).getD i false)))

lemma getD_snoc {α : Type} (w : List α) (x d : α) (i : ℕ) :
    (w ++ [x]).getD i d = if i < w.length then w.getD i d else if i = w.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma sep_form {V : Submodule (ZMod 2) (Fin n → ZMod 2)} (h1 : one ∈ V)
    {W : Fin n → Fin n → ZMod 2} (h : Sep W) : Form V W := by
  obtain ⟨f, g, hW⟩ := h
  refine ⟨g, fun a => ?_⟩
  have : (fun b => W a b - g b) = f a • (one : Fin n → ZMod 2) := by
    funext b; simp [hW, one]
  rw [this]; exact V.smul_mem _ h1

lemma form_mono {V V' : Submodule (ZMod 2) (Fin n → ZMod 2)} (hle : V ≤ V')
    {W : Fin n → Fin n → ZMod 2} (h : Form V W) : Form V' W := by
  obtain ⟨g, hg⟩ := h; exact ⟨g, fun a => hle (hg a)⟩

lemma form_affine {V : Submodule (ZMod 2) (Fin n → ZMod 2)} (c0 c1 c2 : ZMod 2)
    {W1 W2 : Fin n → Fin n → ZMod 2} (hW1 : Form V W1) (hW2 : Form V W2) :
    Form V (fun a b => c0 + c1 * W1 a b + c2 * W2 a b) := by
  obtain ⟨g1, hg1⟩ := hW1
  obtain ⟨g2, hg2⟩ := hW2
  refine ⟨fun b => c0 + c1 * g1 b + c2 * g2 b, fun a => ?_⟩
  have : (fun b => c0 + c1 * W1 a b + c2 * W2 a b - (c0 + c1 * g1 b + c2 * g2 b)) =
      c1 • (fun b => W1 a b - g1 b) + c2 • (fun b => W2 a b - g2 b) := by
    funext b; simp; ring
  rw [this]; exact V.add_mem (V.smul_mem _ (hg1 a)) (V.smul_mem _ (hg2 a))

lemma sep_affine (c0 c1 c2 : ZMod 2) {W1 W2 : Fin n → Fin n → ZMod 2} (hW1 : Sep W1)
    (hW2 : Sep W2) : Sep (fun a b => c0 + c1 * W1 a b + c2 * W2 a b) := by
  obtain ⟨f1, g1, h1⟩ := hW1
  obtain ⟨f2, g2, h2⟩ := hW2
  exact ⟨fun a => c0 + c1 * f1 a + c2 * f2 a, fun b => c1 * g1 b + c2 * g2 b,
    fun a b => by beta_reduce; rw [h1, h2]; ring⟩

lemma form_prod {V : Submodule (ZMod 2) (Fin n → ZMod 2)} (h1 : one ∈ V) (c0 c1 c2 : ZMod 2)
    {W1 W2 : Fin n → Fin n → ZMod 2} (f1 g1 f2 g2 : Fin n → ZMod 2)
    (hW1 : ∀ a b, W1 a b = f1 a + g1 b) (hW2 : ∀ a b, W2 a b = f2 a + g2 b) :
    Form (V ⊔ Submodule.span (ZMod 2) (Set.range ![g1, g2]))
      (fun a b => c0 + c1 * W1 a b + c2 * W2 a b + 1 * W1 a b * W2 a b) := by
  refine ⟨fun b => c1 * g1 b + c2 * g2 b + g1 b * g2 b, fun a => ?_⟩
  have : (fun b => c0 + c1 * W1 a b + c2 * W2 a b + 1 * W1 a b * W2 a b -
      (c1 * g1 b + c2 * g2 b + g1 b * g2 b)) =
      (c0 + c1 * f1 a + c2 * f2 a + f1 a * f2 a) • (one : Fin n → ZMod 2) +
        (f1 a • g2 + f2 a • g1) := by
    funext b; simp [hW1, hW2, one]; ring
  rw [this]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ h1)
  · apply Submodule.mem_sup_right
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)

lemma anf1 (F : List Bool → Bool) (x : Bool) :
    bz (F [x]) = bz (F [false]) + (bz (F [false]) + bz (F [true])) * bz x := by
  cases x <;> cases h0 : F [false] <;> cases h1 : F [true] <;> simp [bz, h0, h1] <;> decide

lemma anf2 (F : List Bool → Bool) (x y : Bool) :
    bz (F [x, y]) = bz (F [false, false]) + (bz (F [false, false]) + bz (F [true, false])) * bz x
      + (bz (F [false, false]) + bz (F [false, true])) * bz y
      + bz (xor (xor (F [false, false]) (F [false, true])) (xor (F [true, false]) (F [true, true])))
        * bz x * bz y := by
  cases x <;> cases y <;> cases h0 : F [false, false] <;> cases h1 : F [false, true] <;>
    cases h2 : F [true, false] <;> cases h3 : F [true, true] <;> simp [bz, h0, h1, h2, h3] <;>
    decide

lemma new_wire (g : Gate) (hfan : g.inputs.length ≤ 2) (ws : Fin n → Fin n → List Bool)
    (ds : List ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (hone : one ∈ V)
    (hwire : ∀ i, (ds.getD i 0 = 0 → Sep (fun a b => bz ((ws a b).getD i false))) ∧
       (ds.getD i 0 ≤ 1 → Form V (fun a b => bz ((ws a b).getD i false)))) :
    ∃ V', V ≤ V' ∧ Module.finrank (ZMod 2) V' ≤ Module.finrank (ZMod 2) V + 2 * (nonlin g).toNat ∧
      ((g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat = 0 →
        Sep (fun a b => bz (g.op.eval (g.inputs.map fun i => (ws a b).getD i false)))) ∧
      ((g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat ≤ 1 →
        Form V' (fun a b => bz (g.op.eval (g.inputs.map fun i => (ws a b).getD i false)))) := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
  · have hnl : nonlin ⟨op, []⟩ = false := by simp [nonlin]
    have hsep : Sep (fun (a b : Fin n) => bz (op.eval (([] : List ℕ).map
        fun i => (ws a b).getD i false))) :=
      ⟨fun _ => bz (op.eval []), fun _ => 0, fun a b => by simp⟩
    refine ⟨V, le_rfl, by simp, fun _ => hsep, fun _ => sep_form hone hsep⟩
  · have hnl : nonlin ⟨op, [u]⟩ = false := by simp [nonlin]
    have hd : (([u] : List ℕ).map (fun a => ds.getD a 0)).foldr max 0 + (nonlin ⟨op, [u]⟩).toNat
        = ds.getD u 0 := by simp [hnl]
    have hval : (fun a b => bz (op.eval (([u] : List ℕ).map fun i => (ws a b).getD i false))) =
        (fun a b => bz (op.eval [false]) + (bz (op.eval [false]) + bz (op.eval [true])) *
          bz ((ws a b).getD u false) + 0 * bz ((ws a b).getD u false)) := by
      funext a b; simp only [List.map_cons, List.map_nil]; rw [anf1]; ring
    refine ⟨V, le_rfl, by simp, ?_, ?_⟩
    · intro h0; rw [hd] at h0
      simp only at hval ⊢
      rw [hval]
      exact sep_affine _ _ _ ((hwire u).1 h0) ((hwire u).1 h0)
    · intro h1; rw [hd] at h1
      simp only at hval ⊢
      rw [hval]
      exact form_affine _ _ _ ((hwire u).2 h1) ((hwire u).2 h1)
  · have hnl : nonlin ⟨op, [u, v]⟩ = xor (xor (op.eval [false, false]) (op.eval [false, true]))
        (xor (op.eval [true, false]) (op.eval [true, true])) := by simp [nonlin]
    have hd : (([u, v] : List ℕ).map (fun a => ds.getD a 0)).foldr max 0 =
        max (ds.getD u 0) (max (ds.getD v 0) 0) := by simp
    have hm1 : ds.getD u 0 ≤ max (ds.getD u 0) (max (ds.getD v 0) 0) := le_max_left _ _
    have hm2 : ds.getD v 0 ≤ max (ds.getD u 0) (max (ds.getD v 0) 0) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hm3 : ∀ k, ds.getD u 0 ≤ k → ds.getD v 0 ≤ k →
        max (ds.getD u 0) (max (ds.getD v 0) 0) ≤ k :=
      fun k h1 h2 => max_le h1 (max_le h2 (Nat.zero_le _))
    have hval : (fun a b => bz (op.eval (([u, v] : List ℕ).map fun i => (ws a b).getD i false))) =
        (fun a b => bz (op.eval [false, false]) +
          (bz (op.eval [false, false]) + bz (op.eval [true, false])) * bz ((ws a b).getD u false)
          + (bz (op.eval [false, false]) + bz (op.eval [false, true])) * bz ((ws a b).getD v false)
          + bz (nonlin ⟨op, [u, v]⟩) * bz ((ws a b).getD u false) * bz ((ws a b).getD v false)) := by
      funext a b; simp only [List.map_cons, List.map_nil]; rw [anf2, hnl]
    simp only at hval ⊢
    rw [hval, hd]
    cases hX : nonlin ⟨op, [u, v]⟩
    · have hval2 : ∀ (W1 W2 : Fin n → Fin n → ZMod 2) (c0 c1 c2 : ZMod 2),
          (fun a b => c0 + c1 * W1 a b + c2 * W2 a b + bz false * W1 a b * W2 a b) =
          (fun a b => c0 + c1 * W1 a b + c2 * W2 a b) := by
        intro W1 W2 c0 c1 c2; funext a b; simp [bz]
      rw [hval2]
      refine ⟨V, le_rfl, by simp, ?_, ?_⟩
      · intro h0
        simp only [Bool.toNat_false, add_zero] at h0
        exact sep_affine _ _ _ ((hwire u).1 (by omega)) ((hwire v).1 (by omega))
      · intro h1
        simp only [Bool.toNat_false, add_zero] at h1
        exact form_affine _ _ _ ((hwire u).2 (by omega)) ((hwire v).2 (by omega))
    · have hb1 : bz true = 1 := rfl
      rw [hb1]
      by_cases hdd : ds.getD u 0 = 0 ∧ ds.getD v 0 = 0
      · obtain ⟨f1, g1, h1⟩ := (hwire u).1 hdd.1
        obtain ⟨f2, g2, h2⟩ := (hwire v).1 hdd.2
        refine ⟨V ⊔ Submodule.span (ZMod 2) (Set.range ![g1, g2]), le_sup_left, ?_, ?_, ?_⟩
        · have := Submodule.finrank_add_le_finrank_add_finrank V
            (Submodule.span (ZMod 2) (Set.range ![g1, g2]))
          have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![g1, g2])) ≤ 2 :=
            (finrank_range_le_card (R := ZMod 2) ![g1, g2]).trans (by simp)
          simp only [Bool.toNat_true]
          omega
        · intro h0; simp only [Bool.toNat_true] at h0; omega
        · intro _
          exact form_prod hone _ _ _ f1 g1 f2 g2 h1 h2
      · refine ⟨V, le_rfl, by simp, ?_, ?_⟩
        · intro h0; simp only [Bool.toNat_true] at h0; omega
        · intro h0; simp only [Bool.toNat_true] at h0
          exfalso; apply hdd; constructor <;> omega
  · simp at hfan

theorem step_inv (g : Gate) (hfan : g.inputs.length ≤ 2) (ws : Fin n → Fin n → List Bool)
    (ds : List ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (hinv : Inv ws ds V) :
    ∃ V', Inv (fun a b => stepW (ws a b) g) (stepD ds g) V' ∧
      Module.finrank (ZMod 2) V' ≤ Module.finrank (ZMod 2) V + 2 * (nonlin g).toNat := by
  obtain ⟨hlen, hone, hwire⟩ := hinv
  obtain ⟨V', hle, hrank, hs0, hs1⟩ := new_wire g hfan ws ds V hone hwire
  refine ⟨V', ⟨?_, hle hone, ?_⟩, hrank⟩
  · intro a b; simp [stepW, stepD, hlen a b]
  · intro i
    simp only [stepW, stepD]
    rw [getD_snoc ds]
    have hw : ∀ a b, ((ws a b) ++ [g.op.eval (g.inputs.map fun i => (ws a b).getD i false)]).getD
        i false = if i < ds.length then (ws a b).getD i false else if i = ds.length then
        g.op.eval (g.inputs.map fun i => (ws a b).getD i false) else false := by
      intro a b; rw [getD_snoc, hlen a b]
    simp only [hw]
    by_cases h1 : i < ds.length
    · simp only [h1, if_true]
      exact ⟨(hwire i).1, fun h => form_mono hle ((hwire i).2 h)⟩
    · by_cases h2 : i = ds.length
      · subst h2
        simp only [lt_self_iff_false, ↓reduceIte]
        exact ⟨hs0, hs1⟩
      · simp only [h1, h2, ↓reduceIte]
        have hsep : Sep (fun (a b : Fin n) => bz false) :=
          ⟨fun _ => 0, fun _ => 0, fun a b => by simp [bz]⟩
        exact ⟨fun _ => hsep, fun _ => sep_form (hle hone) hsep⟩

theorem fold_inv : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (ws : Fin n → Fin n → List Bool) (ds : List ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
    Inv ws ds V → ∃ V', Inv (fun a b => gs.foldl stepW (ws a b)) (gs.foldl stepD ds) V' ∧
      Module.finrank (ZMod 2) V' ≤ Module.finrank (ZMod 2) V + 2 * gs.countP (fun g => nonlin g)
  | [], _, ws, ds, V, h => ⟨V, h, by simp⟩
  | g :: gs, hfan, ws, ds, V, h => by
    obtain ⟨V1, h1, r1⟩ := step_inv g (hfan g (by simp)) ws ds V h
    obtain ⟨V2, h2, r2⟩ := fold_inv gs (fun g' hg' => hfan g' (by simp [hg'])) _ _ V1 h1
    refine ⟨V2, h2, ?_⟩
    rw [List.countP_cons]
    cases hn : nonlin g <;> simp only [hn, Bool.toNat_false, Bool.toNat_true] at r1 <;> simp <;>
      omega

lemma oneEach_getD (a b : Fin n) (i : ℕ) :
    (PEqualNP.Represents.oneEach a b).getD i false =
      (decide (i = a.val) || decide (i = n + b.val)) := by
  have ha := a.isLt
  have hb := b.isLt
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < n
  · rw [List.getElem?_append_left (by simpa using h1),
      List.getElem?_eq_getElem (by simpa using h1), List.getElem_ofFn]
    have h2 : ¬ i = n + b.val := by omega
    simp [h2, Fin.ext_iff]
  · have hle : (List.ofFn fun i : Fin n => decide (i = a)).length ≤ i := by
      simpa using (not_lt.mp h1)
    rw [List.getElem?_append_right hle]
    simp only [List.length_ofFn]
    by_cases h3 : i - n < n
    · rw [List.getElem?_eq_getElem (by simpa using h3), List.getElem_ofFn]
      have h2 : ¬ i = a.val := by omega
      simp only [h2, decide_false, Bool.false_or, Option.getD_some]
      simp only [Fin.ext_iff, decide_eq_decide]
      constructor <;> intro <;> omega
    · rw [List.getElem?_eq_none (by simpa using (not_lt.mp h3))]
      have h2 : ¬ i = a.val := by omega
      have h4 : ¬ i = n + b.val := by omega
      simp [h2, h4]

lemma rho_le_n (M : Fin n → Fin n → ZMod 2) (R : Finset (Fin n)) : rho M R ≤ n := by
  unfold rho
  exact (Submodule.finrank_le _).trans (by simp)

theorem circuit_rank (t : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdepth : (C.gates.foldl stepD (List.replicate (n+n) 0)).getD C.output 0 ≤ 1)
    (hcount : C.gates.countP (fun g => nonlin g) ≤ t) :
    rho (fun a b : Fin n => bz (C.eval (PEqualNP.Represents.oneEach a b))) univ ≤ 2 * t + 2 := by
  set V0 : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range (fun _ : Fin 1 => (one : Fin n → ZMod 2))) with hV0
  have hV0r : Module.finrank (ZMod 2) V0 ≤ 1 := by
    exact (finrank_range_le_card (R := ZMod 2) (fun _ : Fin 1 => (one : Fin n → ZMod 2))).trans
      (by simp)
  have hinv0 : Inv (fun a b => PEqualNP.Represents.oneEach a b) (List.replicate (n+n) 0) V0 := by
    refine ⟨?_, Submodule.subset_span ⟨0, rfl⟩, ?_⟩
    · intro a b; simp [PEqualNP.Represents.oneEach]
    · intro i
      have hsep : Sep (fun (a b : Fin n) => bz ((PEqualNP.Represents.oneEach a b).getD i false)) := by
        refine ⟨fun a => bz (decide (i = a.val)), fun b => bz (decide (i = n + b.val)),
          fun a b => ?_⟩
        beta_reduce
        rw [oneEach_getD]
        have := a.isLt
        have := b.isLt
        by_cases h1 : i = a.val
        · have h2 : ¬ i = n + b.val := by omega
          simp [h1, bz] <;> omega
        · by_cases h2 : i = n + b.val <;> simp [h1, h2, bz] <;> omega
      have hone0 : one ∈ V0 := Submodule.subset_span ⟨0, rfl⟩
      exact ⟨fun _ => hsep, fun _ => sep_form hone0 hsep⟩
  obtain ⟨V', hinv', hr'⟩ := fold_inv C.gates hfan _ _ V0 hinv0
  obtain ⟨_, _, hwire⟩ := hinv'
  obtain ⟨G, hG⟩ := (hwire C.output).2 hdepth
  set V2 := V' ⊔ Submodule.span (ZMod 2) (Set.range (fun _ : Fin 1 => G)) with hV2
  have hV2r : Module.finrank (ZMod 2) V2 ≤ Module.finrank (ZMod 2) V' + 1 := by
    have := Submodule.finrank_add_le_finrank_add_finrank V'
      (Submodule.span (ZMod 2) (Set.range (fun _ : Fin 1 => G)))
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun _ : Fin 1 => G)))
        ≤ 1 := (finrank_range_le_card (R := ZMod 2) (fun _ : Fin 1 => G)).trans (by simp)
    rw [← hV2] at this
    omega
  have hle : Submodule.span (ZMod 2)
      (rowR (fun a b : Fin n => bz (C.eval (PEqualNP.Represents.oneEach a b))) univ ''
        ((univ : Finset (Fin n)) : Set (Fin n))) ≤ V2 := by
    rw [Submodule.span_le]
    rintro _ ⟨a, _, rfl⟩
    have hrow : rowR (fun a b : Fin n => bz (C.eval (PEqualNP.Represents.oneEach a b))) univ a =
        (fun b => bz ((C.gates.foldl stepW (PEqualNP.Represents.oneEach a b)).getD C.output false)
          - G b) + G := by
      funext b; simp [rowR]; rfl
    rw [hrow]
    exact V2.add_mem (Submodule.mem_sup_left (hG a))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨0, rfl⟩))
  have := Submodule.finrank_mono hle
  unfold rho
  omega

end circuits

lemma mod_sizes (s : ℕ) (hs : 0 < s) (v : Fin s) :
    (univ.filter (fun u : Fin n => (⟨u.val % s, Nat.mod_lt _ hs⟩ : Fin s) = v)).card = n / s ∨
    (univ.filter (fun u : Fin n => (⟨u.val % s, Nat.mod_lt _ hs⟩ : Fin s) = v)).card
      = n / s + 1 := by
  have h1 : (univ.filter (fun u : Fin n => (⟨u.val % s, Nat.mod_lt _ hs⟩ : Fin s) = v)).card =
      ((range n).filter (fun x => x % s = v.val)).card := by
    apply Finset.card_bij (fun u _ => u.val)
    · intro u hu
      rw [Finset.mem_filter] at hu ⊢
      rw [Finset.mem_range]
      exact ⟨u.isLt, by rw [← hu.2]⟩
    · intro a _ b _ h; exact Fin.ext h
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Fin.ext hx.2⟩
  have h2 : (range n).filter (fun x => x % s = v.val) = (range n).filter (fun x => x ≡ v.val [MOD s]) := by
    apply Finset.filter_congr; intro x _
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt v.isLt]
  rw [h1, h2, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card n hs v.val]
  split_ifs <;> simp

lemma bool_eq_decide (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b <;> by_cases hP : P <;> simp_all

lemma bz_eq_one (b : Bool) : bz b = 1 ↔ b = true := by
  cases b <;> simp [bz]

section construction

open PEqualNP.CircuitLowerBounds

def chainG (acc cur : ℕ) : List ℕ → List Gate
  | [] => []
  | i :: L => ⟨GateOp.mod 2, [acc, i]⟩ :: ⟨GateOp.not, [cur]⟩ :: chainG (cur + 1) (cur + 2) L

def chainOut (acc cur : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: L => chainOut (cur + 1) (cur + 2) L

def par (w : List Bool) (L : List ℕ) : Bool := (L.map (fun i => w.getD i false)).foldr xor false

lemma chainOut_lt : ∀ (L : List ℕ) (acc cur : ℕ), acc < cur →
    chainOut acc cur L < cur + 2 * L.length
  | [], acc, cur, h => by simp [chainOut]; omega
  | _ :: L, acc, cur, h => by
    have := chainOut_lt L (cur + 1) (cur + 2) (by omega)
    simp only [chainOut, List.length_cons]; omega

lemma chainG_length : ∀ (L : List ℕ) (acc cur : ℕ), (chainG acc cur L).length = 2 * L.length
  | [], _, _ => rfl
  | _ :: L, acc, cur => by simp only [chainG, List.length_cons, chainG_length L]; ring

lemma getD_app_left {α : Type} (w R : List α) (d : α) (i : ℕ) (h : i < w.length) :
    (w ++ R).getD i d = w.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma par_congr (w w' : List Bool) (L : List ℕ) (h : ∀ i ∈ L, w'.getD i false = w.getD i false) :
    par w' L = par w L := by
  unfold par; congr 1; exact List.map_congr_left h

lemma eval_mod2 (x y : Bool) : GateOp.eval (GateOp.mod 2) [x, y] = !(xor x y) := by
  cases x <;> cases y <;> rfl

lemma chain_val : ∀ (L : List ℕ) (acc cur : ℕ) (w : List Bool), w.length = cur → acc < cur →
    (∀ i ∈ L, i < cur) →
    ∃ R, (chainG acc cur L).foldl stepW w = w ++ R ∧ R.length = 2 * L.length ∧
      (w ++ R).getD (chainOut acc cur L) false = xor (w.getD acc false) (par w L)
  | [], acc, cur, w, _, _, _ => ⟨[], by simp [chainG], by simp, by simp [chainOut, par]⟩
  | i :: L, acc, cur, w, hw, ha, hL => by
    have hi : i < cur := hL i (by simp)
    have hw1 : stepW w ⟨GateOp.mod 2, [acc, i]⟩ =
        w ++ [!(xor (w.getD acc false) (w.getD i false))] := by
      simp only [stepW, List.map_cons, List.map_nil, eval_mod2]
    have hw2 : stepW (w ++ [!(xor (w.getD acc false) (w.getD i false))]) ⟨GateOp.not, [cur]⟩ =
        w ++ [!(xor (w.getD acc false) (w.getD i false)),
          xor (w.getD acc false) (w.getD i false)] := by
      simp only [stepW, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      rw [getD_snoc]; simp [hw]
    obtain ⟨R', h1, h2, h3⟩ := chain_val L (cur+1) (cur+2)
      (w ++ [!(xor (w.getD acc false) (w.getD i false)), xor (w.getD acc false) (w.getD i false)])
      (by simp [hw]) (by omega) (fun j hj => by have := hL j (by simp [hj]); omega)
    refine ⟨[!(xor (w.getD acc false) (w.getD i false)),
      xor (w.getD acc false) (w.getD i false)] ++ R', ?_, ?_, ?_⟩
    · simp only [chainG, List.foldl_cons, hw1, hw2, h1, List.append_assoc]
    · simp [h2]; ring
    · simp only [chainOut, ← List.append_assoc]
      rw [h3]
      have e1 : (w ++ [!(xor (w.getD acc false) (w.getD i false)),
          xor (w.getD acc false) (w.getD i false)]).getD (cur + 1) false =
          xor (w.getD acc false) (w.getD i false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp [hw]
      have e2 : par (w ++ [!(xor (w.getD acc false) (w.getD i false)),
          xor (w.getD acc false) (w.getD i false)]) L = par w L :=
        par_congr _ _ _ (fun j hj => getD_app_left _ _ _ _ (by have := hL j (by simp [hj]); omega))
      rw [e1, e2]
      simp [par, Bool.xor_assoc]

lemma nonlin_mod2 (a b : ℕ) : nonlin ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
lemma nonlin_not (a : ℕ) : nonlin ⟨GateOp.not, [a]⟩ = false := rfl
lemma nonlin_and2 (a b : ℕ) : nonlin ⟨GateOp.and, [a, b]⟩ = true := rfl

lemma chain_dep : ∀ (L : List ℕ) (acc cur : ℕ) (ds : List ℕ) (D : ℕ), ds.length = cur →
    acc < cur → (∀ i ∈ L, i < cur) → ds.getD acc 0 ≤ D → (∀ i ∈ L, ds.getD i 0 ≤ D) →
    ∃ R, (chainG acc cur L).foldl stepD ds = ds ++ R ∧ R.length = 2 * L.length ∧
      (ds ++ R).getD (chainOut acc cur L) 0 ≤ D
  | [], acc, cur, ds, D, _, _, _, hD, _ =>
    ⟨[], by simp [chainG], by simp, by simpa [chainOut] using hD⟩
  | i :: L, acc, cur, ds, D, hw, ha, hL, hD, hLD => by
    have hi : i < cur := hL i (by simp)
    have hiD : ds.getD i 0 ≤ D := hLD i (by simp)
    have hd1D : max (ds.getD acc 0) (max (ds.getD i 0) 0) ≤ D :=
      max_le hD (max_le hiD (Nat.zero_le _))
    have hs1 : stepD ds ⟨GateOp.mod 2, [acc, i]⟩ =
        ds ++ [max (ds.getD acc 0) (max (ds.getD i 0) 0)] := by
      simp only [stepD, nonlin_mod2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        Bool.toNat_false, add_zero]
    have hs2 : stepD (ds ++ [max (ds.getD acc 0) (max (ds.getD i 0) 0)]) ⟨GateOp.not, [cur]⟩ =
        ds ++ [max (ds.getD acc 0) (max (ds.getD i 0) 0),
          max (max (ds.getD acc 0) (max (ds.getD i 0) 0)) 0] := by
      simp only [stepD, nonlin_not, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        Bool.toNat_false, add_zero]
      rw [getD_snoc]; simp [hw]
    obtain ⟨R', h1, h2, h3⟩ := chain_dep L (cur+1) (cur+2)
      (ds ++ [max (ds.getD acc 0) (max (ds.getD i 0) 0),
          max (max (ds.getD acc 0) (max (ds.getD i 0) 0)) 0]) D (by simp [hw]) (by omega)
      (fun j hj => by have := hL j (by simp [hj]); omega)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hw,
            Nat.add_sub_cancel_left]
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
          exact max_le hd1D (Nat.zero_le _))
      (fun j hj => by
        have hj' := hL j (by simp [hj])
        rw [getD_app_left _ _ _ _ (by omega)]; exact hLD j (by simp [hj]))
    refine ⟨[max (ds.getD acc 0) (max (ds.getD i 0) 0),
          max (max (ds.getD acc 0) (max (ds.getD i 0) 0)) 0] ++ R', ?_, ?_, ?_⟩
    · simp only [chainG, List.foldl_cons, hs1, hs2, h1, List.append_assoc]
    · simp [h2]; ring
    · simp only [chainOut, ← List.append_assoc]; exact h3

lemma chain_countP : ∀ (L : List ℕ) (acc cur : ℕ),
    (chainG acc cur L).countP (fun g => nonlin g) = 0
  | [], _, _ => rfl
  | _ :: L, acc, cur => by
    simp [chainG, List.countP_cons, nonlin_mod2, nonlin_not, chain_countP L]

lemma chain_fan : ∀ (L : List ℕ) (acc cur : ℕ), ∀ g ∈ chainG acc cur L, g.inputs.length ≤ 2
  | [], _, _ => by simp [chainG]
  | _ :: L, acc, cur => by
    intro g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact chain_fan L _ _ g hg

def RB : ℕ → List Gate → Prop
  | _, [] => True
  | c, g :: gs => (∀ i ∈ g.inputs, i < c) ∧ RB (c+1) gs

lemma RB_append : ∀ (gs1 gs2 : List Gate) (c : ℕ), RB c gs1 → RB (c + gs1.length) gs2 →
    RB c (gs1 ++ gs2)
  | [], gs2, c, _, h2 => by simpa using h2
  | g :: gs1, gs2, c, h1, h2 => by
    refine ⟨h1.1, RB_append gs1 gs2 (c+1) h1.2 ?_⟩
    have : c + 1 + gs1.length = c + (g :: gs1).length := by simp; omega
    rw [this]; exact h2

lemma RB_reads : ∀ (gs : List Gate) (c : ℕ), RB c gs → ∀ j < gs.length,
    ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < c + j
  | [], c, _, j, hj => by simp at hj
  | g :: gs, c, h, 0, _ => by simpa using h.1
  | g :: gs, c, h, j+1, hj => by
    intro i hi
    have := RB_reads gs (c+1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

lemma chain_RB : ∀ (L : List ℕ) (acc cur : ℕ), acc < cur → (∀ i ∈ L, i < cur) →
    RB cur (chainG acc cur L)
  | [], _, _, _, _ => trivial
  | i :: L, acc, cur, ha, hL => by
    refine ⟨?_, ?_, chain_RB L (cur+1) (cur+2) (by omega)
      (fun j hj => by have := hL j (by simp [hj]); omega)⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hL _ (by simp)
    · intro x hx; simp at hx; omega

def blockG (Z c : ℕ) (LA LB : List ℕ) : List Gate :=
  chainG Z c LA ++ chainG Z (c + 2 * LA.length) LB ++
    [⟨GateOp.and, [chainOut Z c LA, chainOut Z (c + 2 * LA.length) LB]⟩]

def blen (LA LB : List ℕ) : ℕ := 2 * LA.length + 2 * LB.length + 1

def blocks (Z : ℕ) (LA LB : ℕ → List ℕ) : ℕ → ℕ → ℕ → List Gate
  | _, _, 0 => []
  | c, j, m+1 => blockG Z c (LA j) (LB j) ++ blocks Z LA LB (c + blen (LA j) (LB j)) (j+1) m

def bwires (LA LB : ℕ → List ℕ) : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | c, j, m+1 => (c + 2 * (LA j).length + 2 * (LB j).length) ::
      bwires LA LB (c + blen (LA j) (LB j)) (j+1) m

def bend (LA LB : ℕ → List ℕ) : ℕ → ℕ → ℕ → ℕ
  | c, _, 0 => c
  | c, j, m+1 => bend LA LB (c + blen (LA j) (LB j)) (j+1) m

lemma bend_ge (LA LB : ℕ → List ℕ) : ∀ m c j, c ≤ bend LA LB c j m
  | 0, c, j => le_rfl
  | m+1, c, j => by
    have := bend_ge LA LB m (c + blen (LA j) (LB j)) (j+1)
    have h2 : c ≤ c + blen (LA j) (LB j) := Nat.le_add_right _ _
    simp only [bend]; omega

lemma bwires_lt (LA LB : ℕ → List ℕ) : ∀ m c j, ∀ p ∈ bwires LA LB c j m, p < bend LA LB c j m
  | 0, c, j => by simp [bwires]
  | m+1, c, j => by
    intro p hp
    simp only [bwires, List.mem_cons] at hp
    have h1 := bend_ge LA LB m (c + blen (LA j) (LB j)) (j+1)
    simp only [bend]
    rcases hp with rfl | hp
    · have h2 : c + 2 * (LA j).length + 2 * (LB j).length < c + blen (LA j) (LB j) := by
        unfold blen; omega
      omega
    · exact bwires_lt LA LB m _ _ p hp

lemma blocks_length (Z : ℕ) (LA LB : ℕ → List ℕ) : ∀ m c j,
    c + (blocks Z LA LB c j m).length = bend LA LB c j m
  | 0, c, j => by simp [blocks, bend]
  | m+1, c, j => by
    have := blocks_length Z LA LB m (c + blen (LA j) (LB j)) (j+1)
    simp only [blocks, bend, blockG, List.length_append, chainG_length, List.length_singleton]
    unfold blen at this ⊢; omega

lemma blocks_countP (Z : ℕ) (LA LB : ℕ → List ℕ) : ∀ m c j,
    (blocks Z LA LB c j m).countP (fun g => nonlin g) = m
  | 0, c, j => by simp [blocks]
  | m+1, c, j => by
    simp only [blocks, blockG, List.countP_append, chain_countP, blocks_countP Z LA LB m]
    simp [List.countP_cons, nonlin_and2]; ring

lemma blocks_fan (Z : ℕ) (LA LB : ℕ → List ℕ) : ∀ m c j,
    ∀ g ∈ blocks Z LA LB c j m, g.inputs.length ≤ 2
  | 0, c, j => by simp [blocks]
  | m+1, c, j => by
    intro g hg
    simp only [blocks, blockG, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | rfl) | hg
    · exact chain_fan _ _ _ g hg
    · exact chain_fan _ _ _ g hg
    · simp
    · exact blocks_fan Z LA LB m _ _ g hg

lemma blocks_RB (Z c0 : ℕ) (LA LB : ℕ → List ℕ) (hZ : Z < c0) (hA : ∀ l, ∀ i ∈ LA l, i < c0)
    (hB : ∀ l, ∀ i ∈ LB l, i < c0) : ∀ m c j, c0 ≤ c → RB c (blocks Z LA LB c j m)
  | 0, c, j, _ => trivial
  | m+1, c, j, hc => by
    simp only [blocks, blockG]
    have hoA := chainOut_lt (LA j) Z c (by omega)
    have hoB := chainOut_lt (LB j) Z (c + 2 * (LA j).length) (by omega)
    apply RB_append
    · apply RB_append
      · apply RB_append
        · exact chain_RB _ _ _ (by omega) (fun i hi => by have := hA j i hi; omega)
        · rw [chainG_length]
          exact chain_RB _ _ _ (by omega) (fun i hi => by have := hB j i hi; omega)
      · simp only [List.length_append, chainG_length]
        refine ⟨?_, trivial⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> omega
    · simp only [List.length_append, chainG_length, List.length_singleton]
      have := blocks_RB Z c0 LA LB hZ hA hB m (c + blen (LA j) (LB j)) (j+1)
        (by unfold blen; omega)
      exact this

lemma blocks_val (Z c0 : ℕ) (LA LB : ℕ → List ℕ) (w0 : List Bool) (hZ : Z < c0)
    (hA : ∀ l, ∀ i ∈ LA l, i < c0) (hB : ∀ l, ∀ i ∈ LB l, i < c0)
    (hZ0 : w0.getD Z false = false) : ∀ m c j (w : List Bool), w.length = c → c0 ≤ c →
    (∀ i < c0, w.getD i false = w0.getD i false) →
    ∃ R, (blocks Z LA LB c j m).foldl stepW w = w ++ R ∧
      (w ++ R).length = bend LA LB c j m ∧
      (bwires LA LB c j m).map (fun p => (w ++ R).getD p false) =
        (List.range m).map (fun l => par w0 (LA (j+l)) && par w0 (LB (j+l)))
  | 0, c, j, w, hw, _, _ => ⟨[], by simp [blocks], by simp [bend, hw], by simp [bwires]⟩
  | m+1, c, j, w, hw, hc, hw0 => by
    obtain ⟨RA, hA1, hA2, hA3⟩ := chain_val (LA j) Z c w hw (by omega)
      (fun i hi => by have := hA j i hi; omega)
    obtain ⟨RB, hB1, hB2, hB3⟩ := chain_val (LB j) Z (c + 2 * (LA j).length) (w ++ RA)
      (by simp [hw, hA2]) (by omega) (fun i hi => by have := hB j i hi; omega)
    have hoA := chainOut_lt (LA j) Z c (by omega)
    have hoB := chainOut_lt (LB j) Z (c + 2 * (LA j).length) (by omega)
    have hparA : par w (LA j) = par w0 (LA j) :=
      par_congr _ _ _ (fun i hi => hw0 i (hA j i hi))
    have hparB : par (w ++ RA) (LB j) = par w0 (LB j) :=
      par_congr _ _ _ (fun i hi => by
        rw [getD_app_left _ _ _ _ (by have := hB j i hi; omega)]
        exact hw0 i (hB j i hi))
    have hZw : w.getD Z false = false := by rw [hw0 Z hZ]; exact hZ0
    have hZwA : (w ++ RA).getD Z false = false := by
      rw [getD_app_left _ _ _ _ (by omega)]; exact hZw
    have hvA : (w ++ RA ++ RB).getD (chainOut Z c (LA j)) false = par w0 (LA j) := by
      rw [getD_app_left _ _ _ _ (by simp [hw, hA2]; omega), hA3, hZw, hparA]; simp
    have hvB : (w ++ RA ++ RB).getD (chainOut Z (c + 2 * (LA j).length) (LB j)) false =
        par w0 (LB j) := by
      rw [hB3, hZwA, hparB]; simp
    have hstep : stepW (w ++ RA ++ RB)
        ⟨GateOp.and, [chainOut Z c (LA j), chainOut Z (c + 2 * (LA j).length) (LB j)]⟩ =
        w ++ RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)] := by
      simp only [stepW, List.map_cons, List.map_nil, hvA, hvB, GateOp.eval]
      simp
    have hlen : (w ++ RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)]).length =
        c + blen (LA j) (LB j) := by
      simp [hw, hA2, hB2, blen]; ring
    obtain ⟨R', h1, h2, h3⟩ := blocks_val Z c0 LA LB w0 hZ hA hB hZ0 m (c + blen (LA j) (LB j))
      (j+1) (w ++ RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)]) hlen (by unfold blen; omega)
      (fun i hi => by
        rw [getD_app_left _ _ _ _ (by simp [hw]; omega), getD_app_left _ _ _ _ (by simp [hw]; omega),
          getD_app_left _ _ _ _ (by omega)]
        exact hw0 i hi)
    refine ⟨RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)] ++ R', ?_, ?_, ?_⟩
    · simp only [blocks, blockG]
      rw [List.foldl_append, List.foldl_append, List.foldl_append, hA1, hB1, List.foldl_cons,
        List.foldl_nil, hstep, h1]
      simp
    · simp only [bend]; rw [← h2]; simp
    · have e : w ++ (RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)] ++ R') =
          w ++ RA ++ RB ++ [par w0 (LA j) && par w0 (LB j)] ++ R' := by simp
      rw [e]
      simp only [bwires, List.map_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · rw [getD_app_left _ _ _ _ (by rw [hlen]; unfold blen; omega)]
        have hp : c + 2 * (LA j).length + 2 * (LB j).length = (w ++ RA ++ RB).length := by
          simp [hw, hA2, hB2]; ring
        rw [hp, getD_snoc]; simp
      · rw [h3]
        apply List.map_congr_left
        intro l _
        simp only [Function.comp]
        rw [show j + (l + 1) = j + 1 + l by omega]

lemma blocks_dep (Z c0 : ℕ) (LA LB : ℕ → List ℕ) (hZ : Z < c0)
    (hA : ∀ l, ∀ i ∈ LA l, i < c0) (hB : ∀ l, ∀ i ∈ LB l, i < c0) :
    ∀ m c j (ds : List ℕ), ds.length = c → c0 ≤ c → (∀ i < c0, ds.getD i 0 = 0) →
    ∃ R, (blocks Z LA LB c j m).foldl stepD ds = ds ++ R ∧
      (ds ++ R).length = bend LA LB c j m ∧
      ∀ p ∈ bwires LA LB c j m, (ds ++ R).getD p 0 ≤ 1
  | 0, c, j, ds, hw, _, _ => ⟨[], by simp [blocks], by simp [bend, hw], by simp [bwires]⟩
  | m+1, c, j, ds, hw, hc, hd0 => by
    obtain ⟨RA, hA1, hA2, hA3⟩ := chain_dep (LA j) Z c ds 0 hw (by omega)
      (fun i hi => by have := hA j i hi; omega) (by rw [hd0 Z hZ])
      (fun i hi => by rw [hd0 i (hA j i hi)])
    obtain ⟨RB, hB1, hB2, hB3⟩ := chain_dep (LB j) Z (c + 2 * (LA j).length) (ds ++ RA) 0
      (by simp [hw, hA2]) (by omega) (fun i hi => by have := hB j i hi; omega)
      (by rw [getD_app_left _ _ _ _ (by omega), hd0 Z hZ])
      (fun i hi => by
        rw [getD_app_left _ _ _ _ (by have := hB j i hi; omega), hd0 i (hB j i hi)])
    have hoA := chainOut_lt (LA j) Z c (by omega)
    have hdA : (ds ++ RA ++ RB).getD (chainOut Z c (LA j)) 0 = 0 := by
      rw [getD_app_left _ _ _ _ (by simp [hw, hA2]; omega)]; omega
    have hdB : (ds ++ RA ++ RB).getD (chainOut Z (c + 2 * (LA j).length) (LB j)) 0 = 0 := by
      omega
    have hstep : stepD (ds ++ RA ++ RB)
        ⟨GateOp.and, [chainOut Z c (LA j), chainOut Z (c + 2 * (LA j).length) (LB j)]⟩ =
        ds ++ RA ++ RB ++ [1] := by
      simp only [stepD, List.map_cons, List.map_nil, hdA, hdB, nonlin_and2, List.foldr_cons,
        List.foldr_nil, Bool.toNat_true]
      rfl
    have hlen : (ds ++ RA ++ RB ++ [1]).length = c + blen (LA j) (LB j) := by
      simp [hw, hA2, hB2, blen]; ring
    obtain ⟨R', h1, h2, h3⟩ := blocks_dep Z c0 LA LB hZ hA hB m (c + blen (LA j) (LB j))
      (j+1) (ds ++ RA ++ RB ++ [1]) hlen (by unfold blen; omega)
      (fun i hi => by
        rw [getD_app_left _ _ _ _ (by simp [hw]; omega), getD_app_left _ _ _ _ (by simp [hw]; omega),
          getD_app_left _ _ _ _ (by omega)]
        exact hd0 i hi)
    refine ⟨RA ++ RB ++ [1] ++ R', ?_, ?_, ?_⟩
    · simp only [blocks, blockG]
      rw [List.foldl_append, List.foldl_append, List.foldl_append, hA1, hB1, List.foldl_cons,
        List.foldl_nil, hstep, h1]
      simp
    · simp only [bend]; rw [← h2]; simp
    · have e : ds ++ (RA ++ RB ++ [1] ++ R') = ds ++ RA ++ RB ++ [1] ++ R' := by simp
      rw [e]
      intro p hp
      simp only [bwires, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [getD_app_left _ _ _ _ (by rw [hlen]; unfold blen; omega)]
        have hp : c + 2 * (LA j).length + 2 * (LB j).length = (ds ++ RA ++ RB).length := by
          simp [hw, hA2, hB2]; ring
        rw [hp, getD_snoc]; simp
      · exact h3 p hp

end construction


section identity

def idxs (m : ℕ) (F G : ℕ → Bool) : List ℕ :=
  (List.range m).filter F ++ ((List.range m).filter G).map (fun j => m + j)

lemma idxs_lt (m : ℕ) (F G : ℕ → Bool) : ∀ i ∈ idxs m F G, i < m + m := by
  intro i hi
  simp only [idxs, List.mem_append, List.mem_filter, List.mem_range, List.mem_map] at hi
  rcases hi with ⟨h, _⟩ | ⟨j, ⟨h, _⟩, rfl⟩ <;> omega

lemma foldr_xor_init : ∀ (l : List Bool) (b : Bool), l.foldr xor b = xor (l.foldr xor false) b
  | [], b => by simp
  | x :: l, b => by
    simp only [List.foldr_cons]; rw [foldr_xor_init l b]; simp [Bool.xor_assoc]

lemma par_append (w : List Bool) (L1 L2 : List ℕ) :
    par w (L1 ++ L2) = xor (par w L1) (par w L2) := by
  unfold par; rw [List.map_append, List.foldr_append, foldr_xor_init]

lemma foldr_decide (x : ℕ) : ∀ L : List ℕ, L.Nodup →
    (L.map (fun i => decide (i = x))).foldr xor false = decide (x ∈ L)
  | [], _ => by simp
  | i :: L, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.foldr_cons, foldr_decide x L h.2, List.mem_cons]
    by_cases hx : x = i
    · subst hx; simp [h.1]
    · have : ¬ i = x := fun e => hx e.symm
      simp [hx, this]

lemma par_idxs (a b : Fin n) (w : List Bool)
    (hw : ∀ i < n + n, w.getD i false = (PEqualNP.Represents.oneEach a b).getD i false)
    (F G : ℕ → Bool) : par w (idxs n F G) = xor (F a.val) (G b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  unfold idxs
  rw [par_append]
  congr 1
  · have e : par w ((List.range n).filter F) =
        (((List.range n).filter F).map (fun i => decide (i = a.val))).foldr xor false := by
      unfold par; congr 1; apply List.map_congr_left; intro i hi
      have hi' : i < n := by
        have := (List.mem_filter.mp hi).1
        simpa using this
      rw [hw i (by omega), oneEach_getD]
      have : ¬ i = n + b.val := by omega
      simp [this]
    rw [e, foldr_decide _ _ (List.Nodup.filter _ List.nodup_range)]
    simp [List.mem_filter, ha]
  · have e : par w (((List.range n).filter G).map (fun j => n + j)) =
        (((List.range n).filter G).map (fun j => decide (j = b.val))).foldr xor false := by
      unfold par; rw [List.map_map]; congr 1; apply List.map_congr_left; intro j hj
      have hj' : j < n := by
        have := (List.mem_filter.mp hj).1
        simpa using this
      simp only [Function.comp]
      rw [hw (n + j) (by omega), oneEach_getD]
      have : ¬ n + j = a.val := by omega
      simp [this]
    rw [e, foldr_decide _ _ (List.Nodup.filter _ List.nodup_range)]
    simp [List.mem_filter, hb]

def fa (t l x : ℕ) : Bool := xor (decide (x = 2*l)) (decide (x = 2*t))
def ga (t l y : ℕ) : Bool := xor (decide (y < 2*t+1)) (decide (y = 2*l+1))
def fb (t l x : ℕ) : Bool := xor (decide (x = 2*l+1)) (decide (x = 2*t))
def gb (t l y : ℕ) : Bool := xor (decide (y < 2*t+1)) (decide (y = 2*l))
def fl (t x : ℕ) : Bool := xor (decide (x < 2*t+1)) (decide (t % 2 = 1) && decide (x = 2*t))
def gl (t y : ℕ) : Bool := xor (decide (t % 2 = 0) && decide (y < 2*t+1)) (decide (y < 2*t))

lemma bz_xor (x y : Bool) : bz (xor x y) = bz x + bz y := by
  cases x <;> cases y <;> simp [bz] <;> decide
lemma bz_and (x y : Bool) : bz (x && y) = bz x * bz y := by
  cases x <;> cases y <;> simp [bz]
lemma bz_decide (P : Prop) [Decidable P] : bz (decide P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [bz, h]
lemma bz_inj {x y : Bool} (h : bz x = bz y) : x = y := by
  cases x <;> cases y <;> simp_all [bz]

lemma bz_foldr_range (f : ℕ → Bool) : ∀ t, bz (((List.range t).map f).foldr xor false) =
    ∑ l ∈ Finset.range t, bz (f l)
  | 0 => by simp [bz]
  | t+1 => by
    rw [List.range_succ, List.map_append, List.foldr_append, foldr_xor_init, bz_xor,
      bz_foldr_range f t, Finset.sum_range_succ]
    simp [bz_xor, bz]

lemma pair_sum (f : ℕ → ZMod 2) : ∀ m, ∑ l ∈ Finset.range m, (f (2*l) + f (2*l+1)) =
    ∑ v ∈ Finset.range (2*m), f v
  | 0 => by simp
  | m+1 => by
    rw [Finset.sum_range_succ, pair_sum f m, show 2*(m+1) = 2*m+1+1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma natCast_zmod2 (t : ℕ) : (t : ZMod 2) = if t % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod t 2]
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]

theorem key_identity (t α β : ℕ) (hα : α < 2*t+2) (hβ : β < 2*t+2) :
    decide (α = β) = xor (xor (fl t α) (gl t β)) (xor true (((List.range t).map
      (fun l => xor (fa t l α) (ga t l β) && xor (fb t l α) (gb t l β))).foldr xor false)) := by
  apply bz_inj
  rw [bz_xor, bz_xor, bz_xor, bz_foldr_range]
  have hper : ∀ l ∈ Finset.range t,
      bz (xor (fa t l α) (ga t l β) && xor (fb t l α) (gb t l β)) =
      ((if α = 2*t then (1:ZMod 2) else 0) + (if β < 2*t+1 then 1 else 0)) +
      ((if β = 2*l then 1 else 0) + (if β = 2*l+1 then 1 else 0)) +
      ((if α = 2*l then 1 else 0) * ((if β < 2*t+1 then 1 else 0) + (if β = 2*l then 1 else 0)) +
       (if α = 2*l+1 then 1 else 0) *
         ((if β < 2*t+1 then 1 else 0) + (if β = 2*l+1 then 1 else 0))) +
      (if α = 2*t then 1 else 0) * ((if β = 2*l then 1 else 0) + (if β = 2*l+1 then 1 else 0)) := by
    intro l hl
    have hlt := Finset.mem_range.mp hl
    simp only [fa, ga, fb, gb, bz_and, bz_xor, bz_decide]
    split_ifs <;> first | decide | (exfalso; omega)
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hs1 : ∑ l ∈ Finset.range t, ((if α = 2*t then (1:ZMod 2) else 0) +
      (if β < 2*t+1 then 1 else 0)) = (t : ZMod 2) * ((if α = 2*t then (1:ZMod 2) else 0) +
      (if β < 2*t+1 then 1 else 0)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hs2 : ∑ l ∈ Finset.range t, ((if β = 2*l then (1:ZMod 2) else 0) +
      (if β = 2*l+1 then 1 else 0)) = if β < 2*t then 1 else 0 := by
    rw [pair_sum (fun v => if β = v then (1:ZMod 2) else 0) t, Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hs3 : ∑ l ∈ Finset.range t,
      ((if α = 2*l then (1:ZMod 2) else 0) * ((if β < 2*t+1 then 1 else 0) +
        (if β = 2*l then 1 else 0)) +
       (if α = 2*l+1 then 1 else 0) *
         ((if β < 2*t+1 then 1 else 0) + (if β = 2*l+1 then 1 else 0))) =
      if α < 2*t then ((if β < 2*t+1 then 1 else 0) + (if β = α then 1 else 0)) else 0 := by
    rw [pair_sum (fun v => (if α = v then (1:ZMod 2) else 0) *
      ((if β < 2*t+1 then 1 else 0) + (if β = v then 1 else 0))) t]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hs4 : ∑ l ∈ Finset.range t, (if α = 2*t then (1:ZMod 2) else 0) *
      ((if β = 2*l then 1 else 0) + (if β = 2*l+1 then 1 else 0)) =
      (if α = 2*t then (1:ZMod 2) else 0) * (if β < 2*t then 1 else 0) := by
    rw [← Finset.mul_sum, hs2]
  rw [hs1, hs2, hs3, hs4, natCast_zmod2]
  simp only [fl, gl, bz_and, bz_xor, bz_decide]
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · simp only [ht]
    split_ifs <;> first | decide | (exfalso; omega)
  · simp only [ht]
    split_ifs <;> first | decide | (exfalso; omega)

end identity

lemma RB_append' (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (c c' : ℕ) (h1 : RB c gs1)
    (he : c + gs1.length = c') (h2 : RB c' gs2) : RB c (gs1 ++ gs2) :=
  RB_append gs1 gs2 c h1 (he ▸ h2)

lemma getD_zero_of_all : ∀ (l : List ℕ), (∀ x ∈ l, x = 0) → ∀ i, l.getD i 0 = 0
  | [], _, i => by simp
  | x :: l, h, 0 => by simp [h x (by simp)]
  | x :: l, h, i+1 => by
    simp only [List.getD_cons_succ]; exact getD_zero_of_all l (fun y hy => h y (by simp [hy])) i

lemma getD_app_right {α : Type} (w R : List α) (d : α) (i : ℕ) (h : w.length ≤ i) :
    (w ++ R).getD i d = R.getD (i - w.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem exists_circuit (n t : ℕ) (hn : 0 < n) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+n) C ∧
      (C.gates.foldl stepD (List.replicate (n+n) 0)).getD C.output 0 ≤ 1 ∧
      C.gates.countP (fun g => nonlin g) ≤ t ∧
      ∀ a b : Fin n, C.eval (PEqualNP.Represents.oneEach a b) =
        decide (a.val % min n (2*t+2) = b.val % min n (2*t+2)) := by
  have hs : 0 < min n (2*t+2) := lt_min hn (by omega)
  have hs2 : min n (2*t+2) ≤ 2*t+2 := min_le_right _ _
  set s := min n (2*t+2) with hs_def
  let LA : ℕ → List ℕ := fun l => idxs n (fun x => fa t l (x % s)) (fun y => ga t l (y % s))
  let LB : ℕ → List ℕ := fun l => idxs n (fun x => fb t l (x % s)) (fun y => gb t l (y % s))
  let Ll : List ℕ := idxs n (fun x => fl t (x % s)) (fun y => gl t (y % s))
  have hA : ∀ l, ∀ i ∈ LA l, i < n + n + 2 := fun l i hi => by
    have := idxs_lt _ _ _ i hi; omega
  have hB : ∀ l, ∀ i ∈ LB l, i < n + n + 2 := fun l i hi => by
    have := idxs_lt _ _ _ i hi; omega
  have hL : ∀ i ∈ Ll, i < n + n := fun i hi => idxs_lt _ _ _ i hi
  have hc01 : n + n + 2 ≤ bend LA LB (n + n + 2) 0 t := bend_ge LA LB t _ _
  have hbw : ∀ p ∈ bwires LA LB (n + n + 2) 0 t, p < bend LA LB (n + n + 2) 0 t :=
    bwires_lt LA LB t _ _
  have hblen : n + n + 2 + (blocks (n+n) LA LB (n + n + 2) 0 t).length =
      bend LA LB (n + n + 2) 0 t := blocks_length _ _ _ t _ _
  set c1 := bend LA LB (n + n + 2) 0 t with hc1
  set ol := chainOut (n+n) c1 Ll with hol
  set c2 := c1 + 2 * Ll.length with hc2
  set PL := (n + n + 1) :: bwires LA LB (n + n + 2) 0 t with hPL
  have hol_lt : ol < c2 := chainOut_lt Ll (n+n) c1 (by omega)
  have hPL_lt : ∀ i ∈ PL, i < c2 := by
    intro i hi; rw [hPL, List.mem_cons] at hi
    rcases hi with rfl | hi
    · omega
    · have := hbw i hi; omega
  set gs : List PEqualNP.CircuitLowerBounds.Gate :=
    [⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩] ++
    blocks (n+n) LA LB (n + n + 2) 0 t ++ chainG (n+n) c1 Ll ++ chainG ol c2 PL with hgs
  refine ⟨⟨gs, chainOut ol c2 PL⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- fan-in
    intro g hg
    simp only [hgs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (((rfl | rfl) | hg) | hg) | hg
    · simp
    · simp
    · exact blocks_fan _ _ _ t _ _ g hg
    · exact chain_fan _ _ _ g hg
    · exact chain_fan _ _ _ g hg
  · -- reads back
    intro j hj i hi
    have hRB : RB (n + n) gs := by
      rw [hgs]
      refine RB_append' _ _ (n+n) c2 ?_ (by simp [chainG_length]; omega)
        (chain_RB _ _ _ hol_lt hPL_lt)
      refine RB_append' _ _ (n+n) c1 ?_ (by simp; omega)
        (chain_RB _ _ _ (by omega) (fun i hi => by have := hL i hi; omega))
      refine RB_append' _ _ (n+n) (n+n+2) ?_ (by simp)
        (blocks_RB (n+n) (n+n+2) LA LB (by omega) hA hB t _ _ le_rfl)
      exact ⟨by simp, by simp, trivial⟩
    exact RB_reads gs (n+n) hRB j hj i hi
  · -- depth
    show (gs.foldl stepD (List.replicate (n+n) 0)).getD (chainOut ol c2 PL) 0 ≤ 1
    rw [hgs, List.foldl_append, List.foldl_append, List.foldl_append]
    have h0 : ([⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩] : List PEqualNP.CircuitLowerBounds.Gate).foldl
        stepD (List.replicate (n+n) 0) = List.replicate (n+n) 0 ++ [0, 0] := by
      simp [stepD, nonlin]
    rw [h0]
    have hz : ∀ i, (List.replicate (n+n) 0 ++ [0, 0]).getD i 0 = 0 := by
      apply getD_zero_of_all
      intro x hx
      simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      omega
    obtain ⟨R1, h11, h12, h13⟩ := blocks_dep (n+n) (n+n+2) LA LB (by omega) hA hB t (n+n+2) 0
      (List.replicate (n+n) 0 ++ [0, 0]) (by simp) le_rfl (fun i _ => hz i)
    rw [h11]
    obtain ⟨R2, h21, h22, h23⟩ := chain_dep Ll (n+n) c1
      (List.replicate (n+n) 0 ++ [0, 0] ++ R1) 0 h12 (by omega)
      (fun i hi => by have := hL i hi; omega)
      (by rw [getD_app_left _ _ _ _ (by simp), hz])
      (fun i hi => by rw [getD_app_left _ _ _ _ (by simp; have := hL i hi; omega), hz])
    rw [h21]
    obtain ⟨R3, h31, h32, h33⟩ := chain_dep PL ol c2
      (List.replicate (n+n) 0 ++ [0, 0] ++ R1 ++ R2) 1 (by simp only [List.length_append] at h12 ⊢; omega)
      hol_lt hPL_lt (by rw [hol]; have := h23; omega)
      (by
        intro i hi
        rw [hPL, List.mem_cons] at hi
        rcases hi with rfl | hi
        · rw [getD_app_left _ _ _ _ (by simp only [List.length_append] at h12 ⊢; omega),
            getD_app_left _ _ _ _ (by simp), hz]; omega
        · have := hbw i hi
          rw [getD_app_left _ _ _ _ (by simp only [List.length_append] at h12 ⊢; omega)]
          exact h13 i hi)
    rw [h31]; exact h33
  · -- count
    show gs.countP (fun g => nonlin g) ≤ t
    rw [hgs]
    simp only [List.countP_append, blocks_countP, chain_countP]
    simp [nonlin]
  · -- value
    intro a b
    show (gs.foldl stepW (PEqualNP.Represents.oneEach a b)).getD (chainOut ol c2 PL) false = _
    rw [hgs, List.foldl_append, List.foldl_append, List.foldl_append]
    have hoe : (PEqualNP.Represents.oneEach a b).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : ([⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩] : List PEqualNP.CircuitLowerBounds.Gate).foldl
        stepW (PEqualNP.Represents.oneEach a b) =
        PEqualNP.Represents.oneEach a b ++ [false, true] := by
      simp [stepW, PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [h0]
    have hw0len : (PEqualNP.Represents.oneEach a b ++ [false, true]).length = n + n + 2 := by
      simp [hoe]
    have hw0Z : (PEqualNP.Represents.oneEach a b ++ [false, true]).getD (n+n) false = false := by
      rw [getD_app_right _ _ _ _ (by omega), hoe]; simp
    have hw0T : (PEqualNP.Represents.oneEach a b ++ [false, true]).getD (n+n+1) false = true := by
      rw [getD_app_right _ _ _ _ (by omega), hoe]; simp
    have hw0in : ∀ i < n + n, (PEqualNP.Represents.oneEach a b ++ [false, true]).getD i false =
        (PEqualNP.Represents.oneEach a b).getD i false :=
      fun i hi => getD_app_left _ _ _ _ (by omega)
    obtain ⟨R1, h11, h12, h13⟩ := blocks_val (n+n) (n+n+2) LA LB
      (PEqualNP.Represents.oneEach a b ++ [false, true]) (by omega) hA hB hw0Z t (n+n+2) 0
      (PEqualNP.Represents.oneEach a b ++ [false, true]) hw0len le_rfl (fun i _ => rfl)
    rw [h11]
    obtain ⟨R2, h21, h22, h23⟩ := chain_val Ll (n+n) c1
      (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1) h12 (by omega)
      (fun i hi => by have := hL i hi; omega)
    rw [h21]
    obtain ⟨R3, h31, h32, h33⟩ := chain_val PL ol c2
      (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1 ++ R2)
      (by simp only [List.length_append] at h12 ⊢; omega) hol_lt hPL_lt
    rw [h31, h33, h23]
    have e1 : (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1).getD (n+n) false = false := by
      rw [getD_app_left _ _ _ _ (by simp [hoe])]; exact hw0Z
    have e2 : par (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1) Ll =
        par (PEqualNP.Represents.oneEach a b ++ [false, true]) Ll :=
      par_congr _ _ _ (fun i hi => getD_app_left _ _ _ _ (by have := hL i hi; simp [hoe]; omega))
    have e3 : par (PEqualNP.Represents.oneEach a b ++ [false, true]) Ll =
        xor (fl t (a.val % s)) (gl t (b.val % s)) := par_idxs a b _ hw0in _ _
    have e4 : par (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1 ++ R2) PL =
        xor true (((List.range t).map (fun l =>
          par (PEqualNP.Represents.oneEach a b ++ [false, true]) (LA (0+l)) &&
          par (PEqualNP.Represents.oneEach a b ++ [false, true]) (LB (0+l)))).foldr xor false) := by
      rw [hPL]
      unfold par
      simp only [List.map_cons, List.foldr_cons]
      congr 1
      · rw [getD_app_left _ _ _ _ (by simp only [List.length_append] at h12 ⊢; omega),
          getD_app_left _ _ _ _ (by simp [hoe])]
        exact hw0T
      · have : (bwires LA LB (n + n + 2) 0 t).map (fun i =>
            (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1 ++ R2).getD i false) =
            (bwires LA LB (n + n + 2) 0 t).map (fun p =>
              (PEqualNP.Represents.oneEach a b ++ [false, true] ++ R1).getD p false) :=
          List.map_congr_left (fun p hp => getD_app_left _ _ _ _
            (by have := hbw p hp; simp only [List.length_append] at h12 ⊢; omega))
        rw [this, h13]
        rfl
    rw [e1, e2, e3, e4]
    have e5 : ∀ l, par (PEqualNP.Represents.oneEach a b ++ [false, true]) (LA (0 + l)) =
        xor (fa t l (a.val % s)) (ga t l (b.val % s)) := fun l => by
      rw [Nat.zero_add]; exact par_idxs a b _ hw0in _ _
    have e6 : ∀ l, par (PEqualNP.Represents.oneEach a b ++ [false, true]) (LB (0 + l)) =
        xor (fb t l (a.val % s)) (gb t l (b.val % s)) := fun l => by
      rw [Nat.zero_add]; exact par_idxs a b _ hw0in _ _
    simp only [e5, e6]
    rw [key_identity t (a.val % s) (b.val % s) (by have := Nat.mod_lt a.val hs; omega)
      (by have := Nat.mod_lt b.val hs; omega)]
    simp

theorem main :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n t : ℕ), 0 < n →
  let s := min n (2*t+2)
  let q := n / s
  let r := n % s
  let best := (s-r)*q*(q-1) + r*(q+1)*q
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n) =>
    C.eval (PEqualNP.Represents.oneEach a b)
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+n) C ∧
    depth (n+n) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t ∧ ∀ i, value C i i = true
  let errors := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∑ i : Fin n, (((Finset.univ : Finset (Fin n)).erase i).filter
      (fun j => value C i j = true)).card
  (∀ C, valid C → best ≤ errors C ∧ (errors C = best ↔
    ∃ h : Fin n → Fin s,
      (∀ i j, value C i j = decide (h i = h j)) ∧
      ∀ v, let c := ((Finset.univ : Finset (Fin n)).filter (fun u => h u = v)).card
           c = q ∨ c = q+1)) ∧
  ∃ C, valid C ∧ errors C = best := by
  intro nonlinear depth n t hn s q r best value valid errors
  have hs : 0 < s := lt_min hn (by omega)
  have hsn : s ≤ n := min_le_left _ _
  -- errors from a hash
  have herr_hash : ∀ C (h : Fin n → Fin s), (∀ i j, value C i j = decide (h i = h j)) →
      (∀ v, ((Finset.univ : Finset (Fin n)).filter (fun u => h u = v)).card = q ∨
        ((Finset.univ : Finset (Fin n)).filter (fun u => h u = v)).card = q + 1) →
      errors C = best := by
    intro C h hv hsz
    have : errors C = ∑ i, ((univ.erase i).filter (fun j => h i = h j)).card := by
      apply Finset.sum_congr rfl; intro i _
      congr 1; apply Finset.filter_congr; intro j _; rw [hv i j]; simp
    rw [this]
    exact count_from_hash s hs h hsz
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨hfan, _, hdep, hcnt, hdiag⟩ := hC
    set M : Fin n → Fin n → ZMod 2 := fun a b => bz (value C a b) with hM
    have hdiagM : ∀ i, M i i = 1 := fun i => (bz_eq_one _).mpr (hdiag i)
    have hrank : rho M univ ≤ s := by
      apply le_min (rho_le_n M univ)
      exact circuit_rank t C hfan hdep hcnt
    have hdeg : ∀ i, deg M univ i =
        ((univ.erase i).filter (fun j => value C i j = true)).card + 1 := by
      intro i
      have e1 : univ.filter (fun j => M i j = 1) = univ.filter (fun j => value C i j = true) := by
        apply Finset.filter_congr; intro j _; exact bz_eq_one _
      have hmem : i ∈ univ.filter (fun j => value C i j = true) := by simp [hdiag i]
      show (univ.filter (fun j => M i j = 1)).card = _
      rw [e1, Finset.filter_erase, Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    have hsumdeg : ∑ i, deg M univ i = errors C + n := by
      rw [Finset.sum_congr rfl (fun i _ => hdeg i), Finset.sum_add_distrib]
      simp [errors]
    obtain ⟨hlow, heq⟩ := matrix_main s hs hsn M hdiagM hrank
    refine ⟨?_, ?_, ?_⟩
    · have : best + n ≤ errors C + n := by rw [← hsumdeg]; exact hlow
      omega
    · intro hE
      obtain ⟨hD, hrow, hS⟩ := heq (by rw [hsumdeg, hE])
      obtain ⟨h, hh, hsurj⟩ := mk_hash M s hdiagM hrow hS
      refine ⟨h, ?_, ?_⟩
      · intro i j
        apply bool_eq_decide
        rw [← hh i j, hM, bz_eq_one]
      · intro v
        obtain ⟨u0, rfl⟩ := hsurj v
        have : (univ.filter (fun u => h u = h u0)) = univ.filter (fun j => M u0 j = 1) := by
          apply Finset.filter_congr; intro j _; rw [hh u0 j]; exact eq_comm
        show (univ.filter (fun u => h u = h u0)).card = q ∨ (univ.filter (fun u => h u = h u0)).card = q + 1
        rw [this]
        exact hD u0
    · rintro ⟨h, hv, hsz⟩
      exact herr_hash C h hv hsz
  · obtain ⟨C, hfan, hrb, hdep, hcnt, hval⟩ := exists_circuit n t hn
    have hvalid : valid C := ⟨hfan, hrb, hdep, hcnt, fun i => by
      show C.eval (PEqualNP.Represents.oneEach i i) = true
      rw [hval]; simp⟩
    refine ⟨C, hvalid, ?_⟩
    apply herr_hash C (fun u => ⟨u.val % s, Nat.mod_lt _ hs⟩)
    · intro i j
      show C.eval (PEqualNP.Represents.oneEach i j) = _
      rw [hval]; simp [Fin.ext_iff]; rfl
    · intro v
      exact mod_sizes s hs v

end PEqualNP.Outside.L_meta_25721_aux

theorem PEqualNP.Outside.L_meta_25721 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n t : ℕ), 0 < n →
  let s := min n (2*t+2)
  let q := n / s
  let r := n % s
  let best := (s-r)*q*(q-1) + r*(q+1)*q
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n) =>
    C.eval (PEqualNP.Represents.oneEach a b)
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+n) C ∧
    depth (n+n) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t ∧ ∀ i, value C i i = true
  let errors := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∑ i : Fin n, (((Finset.univ : Finset (Fin n)).erase i).filter
      (fun j => value C i j = true)).card
  (∀ C, valid C → best ≤ errors C ∧ (errors C = best ↔
    ∃ h : Fin n → Fin s,
      (∀ i j, value C i j = decide (h i = h j)) ∧
      ∀ v, let c := ((Finset.univ : Finset (Fin n)).filter (fun u => h u = v)).card
           c = q ∨ c = q+1)) ∧
  ∃ C, valid C ∧ errors C = best :=
  PEqualNP.Outside.L_meta_25721_aux.main
