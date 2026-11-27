import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_811

open Finset

theorem between {ι : Type} [DecidableEq ι] (s : Finset ι) (l u : ι → ℕ)
    (hlu : ∀ i, l i ≤ u i) (N : ℕ) (h1 : ∑ i ∈ s, l i ≤ N) (h2 : N ≤ ∑ i ∈ s, u i) :
    ∃ v : ι → ℕ, (∀ i, l i ≤ v i ∧ v i ≤ u i) ∧ ∑ i ∈ s, v i = N := by
  induction s using Finset.induction_on generalizing N with
  | empty =>
    simp only [sum_empty] at h1 h2
    exact ⟨l, fun i => ⟨le_rfl, hlu i⟩, by simp; omega⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h1 h2
    have hsl : ∑ i ∈ s, l i ≤ ∑ i ∈ s, u i := Finset.sum_le_sum (fun i _ => hlu i)
    obtain ⟨v, hv, hsum⟩ := ih (min (∑ i ∈ s, u i) (N - l a)) (by omega) (min_le_left _ _)
    refine ⟨Function.update v a (N - min (∑ i ∈ s, u i) (N - l a)), fun i => ?_, ?_⟩
    · by_cases hi : i = a
      · subst hi; rw [Function.update_self]; have := hlu i; omega
      · rw [Function.update_of_ne hi]; exact hv i
    · rw [Finset.sum_insert ha, Function.update_self, Finset.sum_update_of_notMem ha, hsum]
      omega

theorem split (q E : ℕ) : ∀ (m : ℕ) (d : Fin q → ℕ), ∑ j, d j = E * m →
    ∃ G : ℕ → Fin q → ℕ, (∀ t < m, ∑ j, G t j = E) ∧ ∀ j, ∑ t ∈ range m, G t j = d j := by
  intro m
  induction m with
  | zero =>
    intro d hd
    refine ⟨fun _ => 0, fun t ht => absurd ht (Nat.not_lt_zero _), fun j => ?_⟩
    simp only [range_zero, sum_empty]
    have := (Finset.sum_eq_zero_iff.mp (by rw [hd, mul_zero])) j (mem_univ j)
    omega
  | succ m ih =>
    intro d hd
    obtain ⟨u, hu, hsu⟩ := between univ (fun _ => 0) d (fun _ => Nat.zero_le _) E (by simp)
      (by rw [hd]; exact Nat.le_mul_of_pos_right E (Nat.succ_pos m))
    have hd' : ∑ j, (d j - u j) = E * m := by
      have h : ∑ j, (d j - u j) + ∑ j, u j = ∑ j, d j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have := (hu j).2
        omega
      rw [hsu, hd, mul_add, mul_one] at h
      omega
    obtain ⟨G, hG1, hG2⟩ := ih (fun j => d j - u j) hd'
    refine ⟨fun t => if t = m then u else G t, fun t ht => ?_, fun j => ?_⟩
    · by_cases htm : t = m
      · simp only [htm, if_true]; exact hsu
      · simp only [htm, if_false]; exact hG1 t (by omega)
    · rw [Finset.sum_range_succ]
      have h : ∑ t ∈ range m, (if t = m then u else G t) j = ∑ t ∈ range m, G t j :=
        Finset.sum_congr rfl (fun t ht => by rw [if_neg (Finset.mem_range.mp ht).ne])
      rw [h, hG2 j]
      simp only [ite_true]
      have := (hu j).2
      omega

theorem sum_double (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

theorem sum_half (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range (2 * n), f (i / 2) = 2 * ∑ i ∈ range n, f i := by
  rw [sum_double, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega]
  ring

variable {q : ℕ}

noncomputable def Fl (μ : Fin q → ℝ) (b : ℕ) (j : Fin q) : ℕ := ⌊(2 : ℝ) ^ b * μ j⌋₊

noncomputable def nn (E : ℕ) (μ : Fin q → ℝ) (b : ℕ) : ℕ := (∑ j, Fl μ b j) / E

noncomputable def pick (l u : Fin q → ℕ) (N : ℕ) : Fin q → ℕ :=
  if h : (∀ i, l i ≤ u i) ∧ ∑ i, l i ≤ N ∧ N ≤ ∑ i, u i then
    Classical.choose (between univ l u h.1 N h.2.1 h.2.2) else l

theorem pick_spec (l u : Fin q → ℕ) (N : ℕ)
    (h : (∀ i, l i ≤ u i) ∧ ∑ i, l i ≤ N ∧ N ≤ ∑ i, u i) :
    (∀ i, l i ≤ pick l u N i ∧ pick l u N i ≤ u i) ∧ ∑ i, pick l u N i = N := by
  unfold pick
  rw [dif_pos h]
  exact Classical.choose_spec (between univ l u h.1 N h.2.1 h.2.2)

noncomputable def ss (E : ℕ) (μ : Fin q → ℝ) : ℕ → Fin q → ℕ
  | 0 => pick (fun _ => 0) (Fl μ 0) (E * nn E μ 0)
  | b + 1 => pick (fun j => 2 * ss E μ b j) (Fl μ (b + 1)) (E * nn E μ (b + 1))

noncomputable def dd (E : ℕ) (μ : Fin q → ℝ) : ℕ → Fin q → ℕ
  | 0 => ss E μ 0
  | b + 1 => fun j => ss E μ (b + 1) j - 2 * ss E μ b j

noncomputable def mm (E : ℕ) (μ : Fin q → ℝ) : ℕ → ℕ
  | 0 => nn E μ 0
  | b + 1 => nn E μ (b + 1) - 2 * nn E μ b

noncomputable def GG (E : ℕ) (μ : Fin q → ℝ) (b : ℕ) : ℕ → Fin q → ℕ :=
  if h : ∑ j, dd E μ b j = E * mm E μ b then
    Classical.choose (split q E (mm E μ b) (dd E μ b) h) else fun _ => 0

theorem GG_spec (E : ℕ) (μ : Fin q → ℝ) (b : ℕ) (h : ∑ j, dd E μ b j = E * mm E μ b) :
    (∀ t < mm E μ b, ∑ j, GG E μ b t j = E) ∧
      ∀ j, ∑ t ∈ range (mm E μ b), GG E μ b t j = dd E μ b j := by
  unfold GG
  rw [dif_pos h]
  exact Classical.choose_spec (split q E (mm E μ b) (dd E μ b) h)

noncomputable def Tr (E : ℕ) (μ : Fin q → ℝ) : ℕ → ℕ → Option (Fin q → ℕ)
  | 0, i => if i < nn E μ 0 then some (GG E μ 0 i) else none
  | b + 1, i => if i < 2 * nn E μ b then Tr E μ b (i / 2)
      else if i < nn E μ (b + 1) then some (GG E μ (b + 1) (i - 2 * nn E μ b)) else none

section facts

variable (E : ℕ) (μ : Fin q → ℝ) (hE : 0 < E) (hq : 0 < q) (hμ : ∀ j, 0 ≤ μ j)
  (hs : ∑ j, μ j = E)
include hμ

theorem Fl_le (b : ℕ) (j : Fin q) : (Fl μ b j : ℝ) ≤ 2 ^ b * μ j :=
  Nat.floor_le (by have := hμ j; positivity)

theorem Fl_two (b : ℕ) (j : Fin q) : 2 * Fl μ b j ≤ Fl μ (b + 1) j := by
  unfold Fl
  apply Nat.le_floor
  have := Nat.floor_le (show (0 : ℝ) ≤ 2 ^ b * μ j by have := hμ j; positivity)
  push_cast
  rw [pow_succ]
  nlinarith

include hs in
theorem sumFl_le (b : ℕ) : ∑ j, Fl μ b j ≤ 2 ^ b * E := by
  have h : ((∑ j, Fl μ b j : ℕ) : ℝ) ≤ 2 ^ b * E := by
    push_cast
    calc ∑ j, (Fl μ b j : ℝ) ≤ ∑ j, 2 ^ b * μ j := Finset.sum_le_sum (fun j _ => Fl_le μ hμ b j)
      _ = 2 ^ b * E := by rw [← Finset.mul_sum, hs]
  exact_mod_cast h

include hs hq in
theorem sumFl_gt (b : ℕ) : 2 ^ b * E < ∑ j, Fl μ b j + q := by
  have h : (2 : ℝ) ^ b * E < ((∑ j, Fl μ b j + q : ℕ) : ℝ) := by
    push_cast
    have hne : (univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, mem_univ _⟩
    calc (2 : ℝ) ^ b * E = ∑ j, 2 ^ b * μ j := by rw [← Finset.mul_sum, hs]
      _ < ∑ j, ((Fl μ b j : ℝ) + 1) :=
          Finset.sum_lt_sum_of_nonempty hne (fun j _ => Nat.lt_floor_add_one _)
      _ = ∑ j, (Fl μ b j : ℝ) + q := by simp [Finset.sum_add_distrib]
  exact_mod_cast h

include hs hE in
theorem nn_le (b : ℕ) : nn E μ b ≤ 2 ^ b := by
  unfold nn
  apply Nat.div_le_of_le_mul
  have := sumFl_le E μ hμ hs b
  linarith

include hE in
theorem nn_two (b : ℕ) : 2 * nn E μ b ≤ nn E μ (b + 1) := by
  unfold nn
  rw [Nat.le_div_iff_mul_le hE]
  have h1 := Nat.div_mul_le_self (∑ j, Fl μ b j) E
  have h2 : 2 * ∑ j, Fl μ b j ≤ ∑ j, Fl μ (b + 1) j := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun j _ => Fl_two μ hμ b j)
  calc 2 * ((∑ j, Fl μ b j) / E) * E = 2 * ((∑ j, Fl μ b j) / E * E) := by ring
    _ ≤ _ := by omega

theorem Enn_le (b : ℕ) : E * nn E μ b ≤ ∑ j, Fl μ b j := Nat.mul_div_le _ _

include hE in
theorem Enn_gt (b : ℕ) : ∑ j, Fl μ b j < E * nn E μ b + E := by
  unfold nn
  have h1 := Nat.div_add_mod (∑ j, Fl μ b j) E
  have h2 := Nat.mod_lt (∑ j, Fl μ b j) hE
  omega

include hE in
theorem ss_spec (b : ℕ) : (∀ j, ss E μ b j ≤ Fl μ b j) ∧ ∑ j, ss E μ b j = E * nn E μ b := by
  induction b with
  | zero =>
    have := pick_spec (fun _ => 0) (Fl μ 0) (E * nn E μ 0)
      ⟨fun _ => Nat.zero_le _, by simp, Enn_le E μ hμ 0⟩
    exact ⟨fun j => (this.1 j).2, this.2⟩
  | succ b ih =>
    have hl : ∀ j, 2 * ss E μ b j ≤ Fl μ (b + 1) j := fun j => by
      have := ih.1 j; have := Fl_two μ hμ b j; omega
    have hsl : ∑ j, 2 * ss E μ b j ≤ E * nn E μ (b + 1) := by
      rw [← Finset.mul_sum, ih.2]
      have := nn_two E μ hE hμ b
      nlinarith
    have := pick_spec (fun j => 2 * ss E μ b j) (Fl μ (b + 1)) (E * nn E μ (b + 1))
      ⟨hl, hsl, Enn_le E μ hμ (b + 1)⟩
    exact ⟨fun j => (this.1 j).2, this.2⟩

include hE in
theorem ss_two (b : ℕ) (j : Fin q) : 2 * ss E μ b j ≤ ss E μ (b + 1) j := by
  have ih := ss_spec E μ hE hμ b
  have hl : ∀ j, 2 * ss E μ b j ≤ Fl μ (b + 1) j := fun j => by
    have := ih.1 j; have := Fl_two μ hμ b j; omega
  have hsl : ∑ j, 2 * ss E μ b j ≤ E * nn E μ (b + 1) := by
    rw [← Finset.mul_sum, ih.2]
    have := nn_two E μ hE hμ b
    nlinarith
  have := pick_spec (fun j => 2 * ss E μ b j) (Fl μ (b + 1)) (E * nn E μ (b + 1))
    ⟨hl, hsl, Enn_le E μ hμ (b + 1)⟩
  exact (this.1 j).1

include hE in
theorem dd_sum (b : ℕ) : ∑ j, dd E μ b j = E * mm E μ b := by
  cases b with
  | zero => exact (ss_spec E μ hE hμ 0).2
  | succ b =>
    show ∑ j, (ss E μ (b + 1) j - 2 * ss E μ b j) = E * (nn E μ (b + 1) - 2 * nn E μ b)
    have h : ∑ j, (ss E μ (b + 1) j - 2 * ss E μ b j) + ∑ j, 2 * ss E μ b j =
        ∑ j, ss E μ (b + 1) j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have := ss_two E μ hE hμ b j
      omega
    rw [← Finset.mul_sum, (ss_spec E μ hE hμ b).2, (ss_spec E μ hE hμ (b + 1)).2] at h
    rw [Nat.mul_sub, ← mul_assoc, mul_comm E 2, mul_assoc]
    omega

include hE in
theorem Tr_none (b i : ℕ) (h : nn E μ b ≤ i) : Tr E μ b i = none := by
  cases b with
  | zero => simp only [Tr]; rw [if_neg (by omega)]
  | succ b =>
    have := nn_two E μ hE hμ b
    simp only [Tr]
    rw [if_neg (by omega), if_neg (by omega)]

include hE in
theorem Tr_some (b : ℕ) : ∀ i, i < nn E μ b → Tr E μ b i ≠ none := by
  induction b with
  | zero => intro i hi; simp only [Tr]; rw [if_pos hi]; simp
  | succ b ih =>
    intro i hi
    simp only [Tr]
    by_cases h1 : i < 2 * nn E μ b
    · rw [if_pos h1]; exact ih (i / 2) (by omega)
    · rw [if_neg h1, if_pos hi]; simp

include hE in
theorem Tr_sumE (b : ℕ) : ∀ i v, Tr E μ b i = some v → ∑ j, v j = E := by
  induction b with
  | zero =>
    intro i v h
    simp only [Tr] at h
    by_cases hi : i < nn E μ 0
    · rw [if_pos hi] at h
      cases h
      exact (GG_spec E μ 0 (dd_sum E μ hE hμ 0)).1 i hi
    · rw [if_neg hi] at h; cases h
  | succ b ih =>
    intro i v h
    simp only [Tr] at h
    by_cases h1 : i < 2 * nn E μ b
    · rw [if_pos h1] at h; exact ih _ _ h
    · rw [if_neg h1] at h
      by_cases h2 : i < nn E μ (b + 1)
      · rw [if_pos h2] at h
        cases h
        exact (GG_spec E μ (b + 1) (dd_sum E μ hE hμ (b + 1))).1 _
          (show i - 2 * nn E μ b < nn E μ (b + 1) - 2 * nn E μ b by omega)
      · rw [if_neg h2] at h; cases h

include hE in
theorem Tr_child (b i : ℕ) (v : Fin q → ℕ) (h : Tr E μ b i = some v) :
    Tr E μ (b + 1) (2 * i) = some v ∧ Tr E μ (b + 1) (2 * i + 1) = some v := by
  have hi : i < nn E μ b := by
    by_contra hc
    rw [Tr_none E μ hE hμ b i (by omega)] at h
    cases h
  constructor
  · simp only [Tr]
    rw [if_pos (by omega), show 2 * i / 2 = i by omega, h]
  · simp only [Tr]
    rw [if_pos (by omega), show (2 * i + 1) / 2 = i by omega, h]

include hE in
theorem Tr_sumj (b : ℕ) (j : Fin q) :
    ∑ i ∈ range (nn E μ b), (Tr E μ b i).getD 0 j = ss E μ b j := by
  induction b with
  | zero =>
    have h : ∀ i ∈ range (nn E μ 0), (Tr E μ 0 i).getD 0 j = GG E μ 0 i j := by
      intro i hi
      simp only [Tr]
      rw [if_pos (Finset.mem_range.mp hi)]
      rfl
    rw [Finset.sum_congr rfl h]
    exact (GG_spec E μ 0 (dd_sum E μ hE hμ 0)).2 j
  | succ b ih =>
    have h2 := nn_two E μ hE hμ b
    rw [← Finset.sum_range_add_sum_Ico _ h2]
    have hA : ∀ i ∈ range (2 * nn E μ b), (Tr E μ (b + 1) i).getD 0 j =
        (Tr E μ b (i / 2)).getD 0 j := by
      intro i hi
      simp only [Tr]
      rw [if_pos (Finset.mem_range.mp hi)]
    have hB : ∀ i ∈ Ico (2 * nn E μ b) (nn E μ (b + 1)), (Tr E μ (b + 1) i).getD 0 j =
        GG E μ (b + 1) (i - 2 * nn E μ b) j := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp only [Tr]
      rw [if_neg (by omega), if_pos hi.2]
      rfl
    rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB,
      sum_half (fun i => (Tr E μ b i).getD 0 j), ih, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    have := (GG_spec E μ (b + 1) (dd_sum E μ hE hμ (b + 1))).2 j
    simp only [mm] at this
    rw [this]
    have := ss_two E μ hE hμ b j
    show 2 * ss E μ b j + (ss E μ (b + 1) j - 2 * ss E μ b j) = ss E μ (b + 1) j
    omega

include hE hs in
theorem Tr_sum2 (b : ℕ) (j : Fin q) :
    ∑ i ∈ range (2 ^ b), (Tr E μ b i).getD 0 j = ss E μ b j := by
  rw [← Finset.sum_range_add_sum_Ico _ (nn_le E μ hE hμ hs b), Tr_sumj E μ hE hμ b j]
  have : ∑ i ∈ Ico (nn E μ b) (2 ^ b), (Tr E μ b i).getD 0 j = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Tr_none E μ hE hμ b i hi.1]
    rfl
  rw [this, add_zero]

include hE hs in
theorem Tr_pending (b : ℕ) :
    ((range (2 ^ b)).filter (fun i => (Tr E μ b i).isNone)).card = 2 ^ b - nn E μ b := by
  have : (range (2 ^ b)).filter (fun i => (Tr E μ b i).isNone) = Ico (nn E μ b) (2 ^ b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Option.isNone_iff_eq_none]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      by_contra hc
      exact Tr_some E μ hE hμ b i (by omega) h2
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Tr_none E μ hE hμ b i h1⟩
  rw [this, Nat.card_Ico]

include hE hs hq in
theorem gap_le (b : ℕ) : 2 ^ b - nn E μ b ≤ q + E := by
  have h1 := sumFl_gt E μ hq hμ hs b
  have h2 := Enn_gt E μ hE hμ b
  rcases le_or_gt (2 ^ b) (nn E μ b) with h | h
  · omega
  · obtain ⟨t, ht⟩ : ∃ t, 2 ^ b = nn E μ b + t := ⟨2 ^ b - nn E μ b, by omega⟩
    rw [ht] at h1 ⊢
    have ht1 : t ≤ E * t := Nat.le_mul_of_pos_left t hE
    have ht2 : (nn E μ b + t) * E = E * nn E μ b + E * t := by ring
    rw [ht2] at h1
    rw [Nat.add_sub_cancel_left]
    generalize E * nn E μ b = X at *
    generalize E * t = Y at *
    omega

include hE in
theorem ss_lower (b : ℕ) (j : Fin q) : Fl μ b j < ss E μ b j + E := by
  have hsp := ss_spec E μ hE hμ b
  have h2 := Enn_gt E μ hE hμ b
  have h : ∑ j, (Fl μ b j - ss E μ b j) + ∑ j, ss E μ b j = ∑ j, Fl μ b j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have := hsp.1 j
    omega
  have h3 : Fl μ b j - ss E μ b j ≤ ∑ j, (Fl μ b j - ss E μ b j) :=
    Finset.single_le_sum (f := fun j => Fl μ b j - ss E μ b j) (fun j _ => Nat.zero_le _)
      (mem_univ j)
  rw [hsp.2] at h
  omega

end facts

theorem inv_two_pow : Filter.Tendsto (fun b : ℕ => ((2 : ℝ) ^ b)⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

theorem lower_bound (E : ℕ) (hE : 0 < E) (μ : Fin q → ℝ) (T : ℕ → ℕ → Option (Fin q → ℕ))
    (h1 : ∀ b i v, i < 2 ^ b → T b i = some v →
      (∑ j : Fin q, v j) = E ∧ T (b + 1) (2 * i) = some v ∧ T (b + 1) (2 * i + 1) = some v)
    (h3 : ∀ j : Fin q, Filter.Tendsto
      (fun b => ((∑ i ∈ Finset.range (2 ^ b), ((T b i).getD 0) j : ℕ) : ℝ) / (2 : ℝ) ^ b)
      Filter.atTop (nhds (μ j))) (b : ℕ) :
    2 ^ b - (∑ j : Fin q, ⌊(2 : ℝ) ^ b * μ j⌋₊) / E ≤
      ((Finset.range (2 ^ b)).filter (fun i => (T b i).isNone)).card := by
  have hS2 : ∀ b j, 2 * ∑ i ∈ range (2 ^ b), (T b i).getD 0 j ≤
      ∑ i ∈ range (2 ^ (b + 1)), (T (b + 1) i).getD 0 j := by
    intro b j
    rw [pow_succ, mul_comm (2 ^ b) 2, sum_double, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rcases hT : T b i with _ | v
    · simp
    · obtain ⟨_, hc1, hc2⟩ := h1 b i v (Finset.mem_range.mp hi) hT
      rw [hc1, hc2]
      simp only [Option.getD_some]
      omega
  have hle : ∀ j, ∑ i ∈ range (2 ^ b), (T b i).getD 0 j ≤ ⌊(2 : ℝ) ^ b * μ j⌋₊ := by
    intro j
    apply Nat.le_floor
    have hmono : Monotone (fun b => ((∑ i ∈ Finset.range (2 ^ b), ((T b i).getD 0) j : ℕ) : ℝ)
        / (2 : ℝ) ^ b) := by
      apply monotone_nat_of_le_succ
      intro n
      have := hS2 n j
      have h' : (2 : ℝ) * (∑ i ∈ range (2 ^ n), (T n i).getD 0 j : ℕ) ≤
          (∑ i ∈ range (2 ^ (n + 1)), (T (n + 1) i).getD 0 j : ℕ) := by exact_mod_cast this
      rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
      nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
    have := hmono.ge_of_tendsto (h3 j) b
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hstop : ∑ j, ∑ i ∈ range (2 ^ b), (T b i).getD 0 j =
      E * ((range (2 ^ b)).filter (fun i => ¬ (T b i).isNone)).card := by
    rw [Finset.sum_comm, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rcases hT : T b i with _ | v
    · simp
    · simp only [Option.getD_some, Option.isNone_some, Bool.false_eq_true, not_false_eq_true,
        if_true, mul_one]
      exact (h1 b i v (Finset.mem_range.mp hi) hT).1
  have hsum : ∑ j, ∑ i ∈ range (2 ^ b), (T b i).getD 0 j ≤ ∑ j : Fin q, ⌊(2 : ℝ) ^ b * μ j⌋₊ :=
    Finset.sum_le_sum (fun j _ => hle j)
  rw [hstop] at hsum
  have hdiv : ((range (2 ^ b)).filter (fun i => ¬ (T b i).isNone)).card ≤
      (∑ j : Fin q, ⌊(2 : ℝ) ^ b * μ j⌋₊) / E := by
    rw [Nat.le_div_iff_mul_le hE, mul_comm]; exact hsum
  have hcard := Finset.card_filter_add_card_filter_not
    (s := range (2 ^ b)) (fun i => (T b i).isNone)
  rw [Finset.card_range] at hcard
  omega

end PEqualNP.Outside.L_lib_811

open PEqualNP.Outside.L_lib_811 in
theorem PEqualNP.Outside.L_lib_811 : ∀ (q E : ℕ), 0 < q → 0 < E → ∀ μ : Fin q → ℝ, (∀ j, 0 ≤ μ j) → (∑ j, μ j) = E →
  let A := Fin q → ℕ
  let Tree := ℕ → ℕ → Option A
  let pending := fun (T : Tree) (b : ℕ) =>
    ((Finset.range (2^b)).filter (fun i => (T b i).isNone)).card
  let valid := fun T : Tree =>
    (∀ b i v, i < 2^b → T b i = some v →
      (∑ j : Fin q, v j) = E ∧ T (b+1) (2*i) = some v ∧ T (b+1) (2*i+1) = some v) ∧
    Filter.Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) Filter.atTop (nhds 0) ∧
    ∀ j : Fin q, Filter.Tendsto
      (fun b => ((∑ i ∈ Finset.range (2^b), ((T b i).getD 0) j : ℕ) : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds (μ j))
  let bound := fun b : ℕ => 2^b-(∑ j : Fin q, ⌊(2 : ℝ)^b*μ j⌋₊)/E
  (∀ T : Tree, valid T → ∀ b : ℕ, bound b ≤ pending T b) ∧
  (∃ T : Tree, valid T ∧ ∀ b : ℕ, pending T b = bound b) ∧
  Summable (fun b : ℕ => (bound b : ℝ)/(2 : ℝ)^b) := by
  intro q E hq hE μ hμ hs A Tree pending valid bound
  have hgap : ∀ b, bound b ≤ q + E := fun b => by
    show 2 ^ b - nn E μ b ≤ q + E
    exact gap_le E μ hE hq hμ hs b
  refine ⟨?_, ?_, ?_⟩
  · intro T hT b
    exact lower_bound E hE μ T hT.1 hT.2.2 b
  · refine ⟨Tr E μ, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro b i v _ h
      exact ⟨Tr_sumE E μ hE hμ b i v h, Tr_child E μ hE hμ b i v h⟩
    · have hp : ∀ b, (pending (Tr E μ) b : ℝ) / (2 : ℝ) ^ b ≤ (q + E : ℝ) * ((2 : ℝ) ^ b)⁻¹ := by
        intro b
        have : pending (Tr E μ) b = 2 ^ b - nn E μ b := Tr_pending E μ hE hμ hs b
        rw [this, ← div_eq_mul_inv]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast gap_le E μ hE hq hμ hs b
      apply squeeze_zero (fun b => by positivity) hp
      simpa using inv_two_pow.const_mul ((q : ℝ) + E)
    · intro j
      have hfun : (fun b => ((∑ i ∈ Finset.range (2 ^ b), ((Tr E μ b i).getD 0) j : ℕ) : ℝ)
          / (2 : ℝ) ^ b) = fun b => (ss E μ b j : ℝ) / (2 : ℝ) ^ b := by
        funext b; rw [Tr_sum2 E μ hE hμ hs b j]
      rw [hfun]
      have hlow : Filter.Tendsto (fun b : ℕ => μ j - (1 + E) * ((2 : ℝ) ^ b)⁻¹) Filter.atTop
          (nhds (μ j)) := by
        simpa using (tendsto_const_nhds (x := μ j)).sub (inv_two_pow.const_mul ((1 : ℝ) + E))
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      · intro b
        have h1 := ss_lower E μ hE hμ b j
        have h2 : ((2 : ℝ) ^ b * μ j) < (Fl μ b j : ℝ) + 1 := Nat.lt_floor_add_one _
        have h1' : (Fl μ b j : ℝ) < (ss E μ b j : ℝ) + E := by exact_mod_cast h1
        have hpos : (0 : ℝ) < 2 ^ b := by positivity
        show μ j - (1 + E) * ((2 : ℝ) ^ b)⁻¹ ≤ (ss E μ b j : ℝ) / 2 ^ b
        rw [le_div_iff₀ hpos, sub_mul, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
        linarith
      · intro b
        have h1 := (ss_spec E μ hE hμ b).1 j
        have h2 := Fl_le μ hμ b j
        have h1' : (ss E μ b j : ℝ) ≤ Fl μ b j := by exact_mod_cast h1
        have hpos : (0 : ℝ) < 2 ^ b := by positivity
        show (ss E μ b j : ℝ) / 2 ^ b ≤ μ j
        rw [div_le_iff₀ hpos]
        linarith
    · intro b
      exact Tr_pending E μ hE hμ hs b
  · apply Summable.of_nonneg_of_le (fun b => by positivity) _ (summable_geometric_two.mul_left ((q : ℝ) + E))
    intro b
    rw [one_div_pow, mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hgap b
