import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_883

open Finset

def Wd {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ :=
  ((univ : Finset (Fin q)).filter (fun i => l < cap i)).card

def Us {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : ℕ := ∑ i : Fin q, min (cap i) l

noncomputable def tt {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ) : ℝ :=
  ((min (Wd cap l) (E - Us cap l) * (Wd cap l - 2 * k) : ℕ) : ℝ) / (Wd cap l : ℝ)

lemma Us_zero {q : ℕ} (cap : Fin q → ℕ) : Us cap 0 = 0 := by simp [Us]

lemma Us_succ {q : ℕ} (cap : Fin q → ℕ) (l : ℕ) : Us cap (l + 1) = Us cap l + Wd cap l := by
  unfold Us Wd
  rw [card_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  split_ifs with h <;> omega

lemma Us_mono {q : ℕ} (cap : Fin q → ℕ) {l l' : ℕ} (h : l ≤ l') : Us cap l ≤ Us cap l' := by
  unfold Us
  exact sum_le_sum (fun i _ => by omega)

lemma Wd_anti {q : ℕ} (cap : Fin q → ℕ) {l l' : ℕ} (h : l ≤ l') : Wd cap l' ≤ Wd cap l := by
  unfold Wd
  exact card_le_card (fun i hi => by simp only [mem_filter] at hi ⊢; exact ⟨hi.1, by omega⟩)

lemma tt_nonneg {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ) : 0 ≤ tt k E cap l :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma tt_eq_zero_of {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ)
    (h : min (Wd cap l) (E - Us cap l) = 0) : tt k E cap l = 0 := by
  unfold tt
  rw [h]
  simp

lemma tt_zero_sub {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ) (h : Wd cap l ≤ 2 * k) :
    tt k E cap l = 0 := by
  unfold tt
  rw [Nat.sub_eq_zero_of_le h]
  simp

lemma tt_zero_ge {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ) (hl : E ≤ l) :
    tt k E cap l = 0 := by
  apply tt_eq_zero_of
  by_cases hw : Wd cap l = 0
  · rw [hw]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, l < cap i := by
      by_contra hc
      push Not at hc
      apply hw
      unfold Wd
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      exact not_lt.mpr (hc j)
    have : l ≤ Us cap l := by
      unfold Us
      calc l = min (cap i) l := by omega
        _ ≤ _ := single_le_sum (f := fun j => min (cap j) l) (fun j _ => Nat.zero_le _)
            (mem_univ i)
    omega

lemma layer {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (l : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ)) - min (E : ℝ) (Us cap l : ℝ)
      - 2 * k * θ ≤ tt k E cap l := by
  have hW0 : (0 : ℝ) ≤ (Wd cap l : ℝ) := Nat.cast_nonneg _
  have hD0 : min (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ)) - min (E : ℝ) (Us cap l : ℝ)
      ≤ θ * (Wd cap l : ℝ) := by
    rcases le_total (Us cap l : ℝ) (E : ℝ) with h | h
    · rw [min_eq_right h]
      have := min_le_right (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ))
      linarith
    · rw [min_eq_left h]
      have := min_le_left (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ))
      nlinarith
  have hDM : min (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ)) - min (E : ℝ) (Us cap l : ℝ)
      ≤ ((min (Wd cap l) (E - Us cap l) : ℕ) : ℝ) := by
    by_cases hu : Us cap l ≤ E
    · have hu' : (Us cap l : ℝ) ≤ E := by exact_mod_cast hu
      rw [min_eq_right hu', Nat.cast_min, Nat.cast_sub hu]
      apply le_min
      · have := mul_le_mul_of_nonneg_right h1 hW0
        rw [min_eq_right hu'] at hD0
        linarith
      · have := min_le_left (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ))
        linarith
    · have hu' : (E : ℝ) ≤ (Us cap l : ℝ) := by exact_mod_cast (le_of_not_ge hu)
      rw [min_eq_left hu']
      have := min_le_left (E : ℝ) ((Us cap l : ℝ) + θ * (Wd cap l : ℝ))
      have : (0 : ℝ) ≤ ((min (Wd cap l) (E - Us cap l) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  by_cases hw : Wd cap l ≤ 2 * k
  · rw [tt_zero_sub k E cap l hw]
    have : (Wd cap l : ℝ) ≤ 2 * k := by exact_mod_cast hw
    nlinarith
  · push Not at hw
    have hWpos : (0 : ℝ) < (Wd cap l : ℝ) := by
      have : 0 < Wd cap l := by omega
      exact_mod_cast this
    have hk2 : (2 * k : ℝ) < (Wd cap l : ℝ) := by exact_mod_cast hw
    unfold tt
    rw [le_div_iff₀ hWpos, Nat.cast_mul, Nat.cast_sub hw.le]
    push_cast
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have e1 := mul_le_mul_of_nonneg_right hDM (by linarith : (0 : ℝ) ≤ (Wd cap l : ℝ) - 2 * k)
    have e2 := mul_le_mul_of_nonneg_left hD0 (by linarith : (0 : ℝ) ≤ 2 * k)
    push_cast at e1
    nlinarith

lemma sum_lower {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (n : ℕ) :
    min (E : ℝ) (Us cap n : ℝ) - 2 * k * n ≤ ∑ l ∈ range n, tt k E cap l := by
  induction n with
  | zero => simp [Us_zero]
  | succ n ih =>
    rw [sum_range_succ]
    have h := layer k E cap n 1 zero_le_one le_rfl
    simp only [one_mul, mul_one] at h
    rw [Us_succ]
    push_cast
    linarith

lemma sum_ext {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (N : ℕ) (hN : E ≤ N) :
    ∑ l ∈ range E, tt k E cap l = ∑ l ∈ range N, tt k E cap l := by
  apply sum_subset (range_mono hN)
  intro x _ hx
  simp only [mem_range, not_lt] at hx
  exact tt_zero_ge k E cap x hx

lemma Cformula {q : ℕ} (cap : Fin q → ℕ) (n : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ i, min (cap i : ℝ) ((n : ℝ) + θ) = (Us cap n : ℝ) + θ * (Wd cap n : ℝ) := by
  unfold Us Wd
  rw [card_filter]
  push_cast
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · have : (n : ℝ) + 1 ≤ cap i := by exact_mod_cast h
    have h2 : (n : ℝ) ≤ cap i := by linarith
    rw [min_eq_right (by linarith), min_eq_right h2]
    ring
  · push Not at h
    have : (cap i : ℝ) ≤ n := by exact_mod_cast h
    rw [min_eq_left (by linarith), min_eq_left this]
    ring

lemma one_dim {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (m : ℝ) (hm : 0 ≤ m) :
    min (E : ℝ) (∑ i, min (cap i : ℝ) m) - 2 * k * m ≤ ∑ l ∈ range E, tt k E cap l := by
  set n := ⌊m⌋₊ with hn
  have hn1 : (n : ℝ) ≤ m := Nat.floor_le hm
  have hn2 : m < (n : ℝ) + 1 := Nat.lt_floor_add_one m
  have hθ : m = (n : ℝ) + (m - n) := by ring
  rw [hθ, Cformula cap n (m - n) (by linarith) (by linarith)]
  have h1 := sum_lower k E cap n
  have h2 := layer k E cap n (m - n) (by linarith) (by linarith)
  have h3 : ∑ l ∈ range (n + 1), tt k E cap l ≤ ∑ l ∈ range E, tt k E cap l := by
    rw [sum_ext k E cap (max E (n + 1)) (le_max_left _ _)]
    apply sum_le_sum_of_subset_of_nonneg (range_mono (le_max_right _ _))
    intro x _ _
    exact tt_nonneg k E cap x
  rw [sum_range_succ] at h3
  linarith

lemma part1 {q : ℕ} (k E : ℕ) (hk : k ≤ q) (cap : Fin q → ℕ) (w : Fin q → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ (cap i : ℝ)) (hs : (∑ i, w i) ≤ (E : ℝ)) :
    ∃ U : Finset (Fin q), U.card = k ∧
      (∑ i, w i) - 2 * ∑ i ∈ U, w i ≤ ∑ l ∈ range E, tt k E cap l := by
  obtain ⟨T, hT, hmax⟩ := (powersetCard k (univ : Finset (Fin q))).exists_max_image
    (fun U => ∑ i ∈ U, w i) (powersetCard_nonempty.mpr (by simpa using hk))
  rw [mem_powersetCard] at hT
  have hex : ∀ i ∈ T, ∀ j ∉ T, w j ≤ w i := by
    intro i hi j hj
    have hmem : insert j (T.erase i) ∈ powersetCard k (univ : Finset (Fin q)) := by
      rw [mem_powersetCard]
      refine ⟨subset_univ _, ?_⟩
      rw [card_insert_of_notMem (fun h => hj (mem_of_mem_erase h)), card_erase_of_mem hi]
      have : 0 < T.card := card_pos.mpr ⟨i, hi⟩
      omega
    have := hmax _ hmem
    rw [sum_insert (fun h => hj (mem_of_mem_erase h)), sum_erase_eq_sub hi] at this
    linarith
  obtain ⟨m, hm0, hmT, hmN⟩ : ∃ m : ℝ, 0 ≤ m ∧ (∀ i ∈ T, m ≤ w i) ∧ (∀ i ∉ T, w i ≤ m) := by
    by_cases hTn : T.Nonempty
    · refine ⟨T.inf' hTn w, ?_, fun i hi => inf'_le w hi, ?_⟩
      · exact (le_inf'_iff hTn w).mpr (fun i _ => (hw i).1)
      · intro j hj
        obtain ⟨i, hi, heq⟩ := exists_mem_eq_inf' hTn w
        rw [heq]
        exact hex i hi j hj
    · refine ⟨∑ i, w i, sum_nonneg (fun i _ => (hw i).1), ?_, ?_⟩
      · intro i hi
        exact absurd ⟨i, hi⟩ hTn
      · intro i _
        exact single_le_sum (f := w) (fun j _ => (hw j).1) (mem_univ i)
  refine ⟨T, hT.2, ?_⟩
  have hsplit := sum_sdiff (f := w) (subset_univ T)
  have hsplitC := sum_sdiff (f := fun i => min (cap i : ℝ) m) (subset_univ T)
  have hTC : ∑ i ∈ T, min (cap i : ℝ) m = ∑ i ∈ T, m := by
    refine sum_congr rfl (fun i hi => ?_)
    exact min_eq_right ((hmT i hi).trans (hw i).2)
  have hTw : ∑ i ∈ T, m ≤ ∑ i ∈ T, w i := sum_le_sum (fun i hi => hmT i hi)
  have hR : ∑ i ∈ univ \ T, w i ≤ ∑ i ∈ univ \ T, min (cap i : ℝ) m := by
    refine sum_le_sum (fun i hi => ?_)
    have : i ∉ T := (mem_sdiff.mp hi).2
    exact le_min (hw i).2 (hmN i this)
  rw [sum_const, hT.2, nsmul_eq_mul] at hTC hTw
  have h1 := one_dim k E cap m hm0
  rcases min_cases (E : ℝ) (∑ i, min (cap i : ℝ) m) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at h1 <;>
    linarith

lemma count_lt (a ρ : ℕ) (h : ρ ≤ a) :
    ∑ x : Fin a, (if (x : ℕ) < ρ then 1 else 0 : ℕ) = ρ := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < ρ then 1 else 0) a, sum_boole]
  have : (range a).filter (fun x => x < ρ) = range ρ := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  simp [this]

lemma count_shift (a ρ : ℕ) [NeZero a] (h : ρ ≤ a) (j : Fin a) :
    ∑ z : Fin a, (if ((j + z : Fin a) : ℕ) < ρ then 1 else 0 : ℕ) = ρ := by
  exact (Fintype.sum_equiv (Equiv.addLeft j) _ (fun x : Fin a => if (x : ℕ) < ρ then 1 else 0)
    (fun z => rfl)).trans (count_lt a ρ h)

lemma count_shift' (a ρ : ℕ) [NeZero a] (h : ρ ≤ a) (z : Fin a) :
    ∑ j : Fin a, (if ((j + z : Fin a) : ℕ) < ρ then 1 else 0 : ℕ) = ρ := by
  exact (Fintype.sum_equiv (Equiv.addRight z) _ (fun x : Fin a => if (x : ℕ) < ρ then 1 else 0)
    (fun z => rfl)).trans (count_lt a ρ h)

lemma finish {q : ℕ} (k : ℕ) (G : ℝ) (p : ℕ) (hp : 0 < p) (H : Fin p → Fin q → ℕ) (B : ℕ)
    (τ : ℝ) (hB : ∀ z, ∑ i, H z i = B) (hτ : ∀ i, ((∑ z, H z i : ℕ) : ℝ) ≤ p * τ)
    (hG : G ≤ B - 2 * k * τ) (U : Finset (Fin q)) (hU : U.card = k) :
    G ≤ (∑ i, ((∑ z, H z i : ℕ) : ℝ) / p) - 2 * ∑ i ∈ U, ((∑ z, H z i : ℕ) : ℝ) / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hsum : (∑ i, ((∑ z, H z i : ℕ) : ℝ) / p) = B := by
    rw [← sum_div, div_eq_iff hp'.ne']
    have : (∑ i, ((∑ z, H z i : ℕ) : ℝ)) = ((∑ z, ∑ i, H z i : ℕ) : ℝ) := by
      push_cast
      exact sum_comm
    rw [this]
    simp only [hB, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have hU' : ∑ i ∈ U, ((∑ z, H z i : ℕ) : ℝ) / p ≤ k * τ := by
    calc ∑ i ∈ U, ((∑ z, H z i : ℕ) : ℝ) / p ≤ ∑ i ∈ U, τ := by
          refine sum_le_sum (fun i _ => ?_)
          rw [div_le_iff₀ hp']
          linarith [hτ i]
      _ = k * τ := by rw [sum_const, hU, nsmul_eq_mul]
  rw [hsum]
  linarith

lemma mean_sum {q : ℕ} (p : ℕ) (hp : 0 < p) (H : Fin p → Fin q → ℕ) (B : ℕ)
    (hB : ∀ z, ∑ i, H z i = B) : (∑ i, ((∑ z, H z i : ℕ) : ℝ) / p) = B := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← sum_div, div_eq_iff hp'.ne']
  have : (∑ i, ((∑ z, H z i : ℕ) : ℝ)) = ((∑ z, ∑ i, H z i : ℕ) : ℝ) := by
    push_cast
    exact sum_comm
  rw [this]
  simp only [hB, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

lemma gain_upper {q : ℕ} (k E : ℕ) (cap : Fin q → ℕ) (L : ℕ)
    (hlt : ∀ l < L, 2 * k < Wd cap l ∧ Us cap (l + 1) ≤ E)
    (hL : Wd cap L ≤ 2 * k ∨ E < Us cap (L + 1)) (ρ : ℕ)
    (hρ : ρ = if 2 * k < Wd cap L then E - Us cap L else 0) :
    ∑ l ∈ range E, tt k E cap l
      ≤ (Us cap L : ℝ) + ρ - 2 * k * ((L : ℝ) + ρ / (Wd cap L : ℝ)) := by
  have hpre : ∀ n ≤ L, ∑ l ∈ range n, tt k E cap l = (Us cap n : ℝ) - 2 * k * n := by
    intro n
    induction n with
    | zero => intro _; simp [Us_zero]
    | succ n ih =>
      intro hn
      rw [sum_range_succ, ih (by omega), Us_succ]
      obtain ⟨h1, h2⟩ := hlt n (by omega)
      rw [Us_succ] at h2
      have hW : (0 : ℝ) < Wd cap n := by exact_mod_cast (show 0 < Wd cap n by omega)
      unfold tt
      rw [show min (Wd cap n) (E - Us cap n) = Wd cap n by omega, Nat.cast_mul,
        Nat.cast_sub h1.le, mul_div_right_comm, div_self hW.ne', one_mul]
      push_cast
      ring
  have hUsL : Us cap L ≤ E := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Us_zero]
      exact Nat.zero_le _
    · obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
      exact (hlt l (by omega)).2
  have hzero : ∀ l, L < l → tt k E cap l = 0 := by
    intro l hl
    rcases hL with h | h
    · exact tt_zero_sub k E cap l ((Wd_anti cap hl.le).trans h)
    · apply tt_eq_zero_of
      have := Us_mono cap (show L + 1 ≤ l by omega)
      omega
  have hsplit : ∑ l ∈ range E, tt k E cap l = ∑ l ∈ range (L + 1), tt k E cap l := by
    rw [sum_ext k E cap (max E (L + 1)) (le_max_left _ _)]
    symm
    apply sum_subset (range_mono (le_max_right _ _))
    intro x _ hx
    simp only [mem_range, not_lt] at hx
    exact hzero x (by omega)
  rw [hsplit, sum_range_succ, hpre L le_rfl]
  by_cases hw : 2 * k < Wd cap L
  · rw [if_pos hw] at hρ
    have hsu := Us_succ cap L
    have hlt2 : E < Us cap L + Wd cap L := by rcases hL with h | h <;> omega
    have hW : (0 : ℝ) < Wd cap L := by exact_mod_cast (show 0 < Wd cap L by omega)
    unfold tt
    rw [show min (Wd cap L) (E - Us cap L) = ρ by omega, Nat.cast_mul, Nat.cast_sub hw.le]
    have : (ρ : ℝ) * ((Wd cap L : ℝ) - ((2 * k : ℕ) : ℝ)) / (Wd cap L : ℝ)
        = ρ - 2 * k * (ρ / (Wd cap L : ℝ)) := by
      field_simp
      push_cast
      ring
    rw [this]
    linarith
  · rw [if_neg hw] at hρ
    subst hρ
    rw [tt_zero_sub k E cap L (by omega)]
    simp

lemma part2 {q : ℕ} (k E : ℕ) (hq : 0 < q) (cap : Fin q → ℕ) (L : ℕ) (hUsL : Us cap L ≤ E)
    (ρ : ℕ) (hρ0 : ρ ≠ 0 → ρ < Wd cap L ∧ ρ = E - Us cap L) :
    ∃ (p : ℕ) (H : Fin p → Fin q → ℕ), 0 < p ∧ p ≤ q ∧
      (∀ z, (∀ i, H z i ≤ cap i) ∧ (∑ i, H z i) ≤ E) ∧
      (∀ z, ∑ i, H z i = Us cap L + ρ) ∧
      ∀ i, ((∑ z, H z i : ℕ) : ℝ) ≤ p * ((L : ℝ) + ρ / (Wd cap L : ℝ)) := by
  by_cases h0 : ρ = 0
  · subst h0
    refine ⟨1, fun _ i => min (cap i) L, Nat.one_pos, hq, fun z => ⟨fun i => min_le_left _ _, hUsL⟩,
      fun z => by simp [Us], fun i => ?_⟩
    simp only [univ_unique, sum_singleton, Nat.cast_one, one_mul, CharP.cast_eq_zero, zero_div,
      add_zero]
    exact_mod_cast min_le_right _ _
  obtain ⟨hρa, hρE⟩ := hρ0 h0
  have hapos : 0 < Wd cap L := by omega
  have : NeZero (Wd cap L) := ⟨by omega⟩
  let e : Fin (Wd cap L) ≃ {x // x ∈ (univ : Finset (Fin q)).filter (fun i => L < cap i)} :=
    (Finset.equivFin _).symm
  have sumE : ∀ (v : ℕ) (i : Fin q),
      ∑ j : Fin (Wd cap L), (if ((e j : Fin q) = i) then v else 0) = if L < cap i then v else 0 := by
    intro v i
    by_cases hi : L < cap i
    · have hmem : i ∈ (univ : Finset (Fin q)).filter (fun i => L < cap i) := by simp [hi]
      rw [if_pos hi]
      have : ∀ j, ((e j : Fin q) = i ↔ j = e.symm ⟨i, hmem⟩) := by
        intro j
        rw [Equiv.eq_symm_apply, Subtype.ext_iff]
      simp_rw [this]
      simp
    · rw [if_neg hi]
      apply sum_eq_zero
      intro j _
      have := (e j).2
      simp only [mem_filter] at this
      rw [if_neg]
      intro h
      rw [← h] at hi
      exact hi this.2
  have ex_le : ∀ (z : Fin (Wd cap L)) (i : Fin q),
      ∑ j : Fin (Wd cap L), (if ((e j : Fin q) = i ∧ ((j + z : Fin (Wd cap L)) : ℕ) < ρ)
        then 1 else 0) ≤ if L < cap i then 1 else 0 := by
    intro z i
    rw [← sumE 1 i]
    refine sum_le_sum (fun j _ => ?_)
    by_cases hP : (e j : Fin q) = i <;>
      by_cases hQ : ((j + z : Fin (Wd cap L)) : ℕ) < ρ <;> simp [hP, hQ]
  have hex_i : ∀ z : Fin (Wd cap L), ∑ i : Fin q, ∑ j : Fin (Wd cap L),
      (if ((e j : Fin q) = i ∧ ((j + z : Fin (Wd cap L)) : ℕ) < ρ) then 1 else 0) = ρ := by
    intro z
    rw [sum_comm]
    refine (sum_congr rfl (fun j _ => ?_)).trans (count_shift' (Wd cap L) ρ hρa.le z)
    simp [ite_and]
  have hex_z : ∀ i : Fin q, ∑ z : Fin (Wd cap L), ∑ j : Fin (Wd cap L),
      (if ((e j : Fin q) = i ∧ ((j + z : Fin (Wd cap L)) : ℕ) < ρ) then 1 else 0)
        = if L < cap i then ρ else 0 := by
    intro i
    rw [sum_comm, ← sumE ρ i]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases h : (e j : Fin q) = i
    · rw [if_pos h]
      refine (sum_congr rfl (fun z _ => ?_)).trans (count_shift _ ρ hρa.le j)
      simp [h]
    · rw [if_neg h]
      apply sum_eq_zero
      intro z _
      simp [h]
  have hpq : Wd cap L ≤ q := by
    unfold Wd
    exact (card_filter_le _ _).trans (by simp)
  refine ⟨Wd cap L, fun z i => min (cap i) L + ∑ j : Fin (Wd cap L),
      (if ((e j : Fin q) = i ∧ ((j + z : Fin (Wd cap L)) : ℕ) < ρ) then 1 else 0),
    hapos, hpq, fun z => ⟨fun i => ?_, ?_⟩, fun z => ?_, fun i => ?_⟩
  · have := ex_le z i
    dsimp only
    split_ifs at this with h <;> omega
  · rw [sum_add_distrib, hex_i]
    change Us cap L + ρ ≤ E
    omega
  · rw [sum_add_distrib, hex_i]
    rfl
  · have hn : (∑ z : Fin (Wd cap L), (min (cap i) L + ∑ j : Fin (Wd cap L),
        (if ((e j : Fin q) = i ∧ ((j + z : Fin (Wd cap L)) : ℕ) < ρ) then 1 else 0)))
          ≤ Wd cap L * L + ρ := by
      rw [sum_add_distrib, hex_z, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have := Nat.mul_le_mul_left (Wd cap L) (min_le_right (cap i) L)
      split_ifs <;> omega
    have hW : (0 : ℝ) < Wd cap L := by exact_mod_cast hapos
    calc _ ≤ ((Wd cap L * L + ρ : ℕ) : ℝ) := by exact_mod_cast hn
      _ = _ := by
        push_cast
        field_simp

end PEqualNP.Outside.L_lib_883

open PEqualNP.Outside.L_lib_883 in
theorem PEqualNP.Outside.L_lib_883 : ∀ (q k E : ℕ), 0 < q → k ≤ q → ∀ cap : Fin q → ℕ,
  let I := Fin q
  let width := fun l : ℕ => ((Finset.univ : Finset I).filter (fun i => l < cap i)).card
  let used := fun l : ℕ => ∑ i : I, min (cap i) l
  let gain := ∑ l ∈ Finset.range E,
    ((min (width l) (E-used l) * (width l-2*k) : ℕ) : ℝ)/(width l : ℝ)
  let score := fun (w : I → ℝ) (U : Finset I) => (∑ i, w i) - 2 * ∑ i ∈ U, w i
  (∀ w : I → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ (cap i : ℝ)) → (∑ i, w i) ≤ (E : ℝ) →
    ∃ U : Finset I, U.card = k ∧ score w U ≤ gain) ∧
  ∃ (p : ℕ) (H : Fin p → I → ℕ), 0 < p ∧ p ≤ q ∧
    (∀ z, (∀ i, H z i ≤ cap i) ∧ (∑ i, H z i) ≤ E) ∧
    let mean := fun i : I => ((∑ z : Fin p, H z i : ℕ) : ℝ)/(p : ℝ)
    (∀ U : Finset I, U.card = k → gain ≤ score mean U) ∧
    ∃ U : Finset I, U.card = k ∧ score mean U = gain := by
  intro q k E hq hk cap I width used gain score
  have hg : gain = ∑ l ∈ Finset.range E, tt k E cap l := rfl
  refine ⟨fun w hw hs => ?_, ?_⟩
  · obtain ⟨U, hU, h⟩ := part1 k E hk cap w hw hs
    exact ⟨U, hU, by rw [hg]; exact h⟩
  · classical
    have hex : ∃ l, Wd cap l ≤ 2 * k ∨ E < Us cap (l + 1) := by
      refine ⟨∑ i, cap i, Or.inl ?_⟩
      have : Wd cap (∑ i, cap i) = 0 := by
        unfold Wd
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        exact not_lt.mpr
          (Finset.single_le_sum (f := cap) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      omega
    obtain ⟨L, hL, hlt⟩ : ∃ L, (Wd cap L ≤ 2 * k ∨ E < Us cap (L + 1)) ∧
        ∀ l < L, 2 * k < Wd cap l ∧ Us cap (l + 1) ≤ E := by
      refine ⟨Nat.find hex, Nat.find_spec hex, fun l hl => ?_⟩
      have := Nat.find_min hex hl
      push Not at this
      exact this
    have hUsL : Us cap L ≤ E := by
      rcases Nat.eq_zero_or_pos L with h | h
      · rw [h, Us_zero]
        exact Nat.zero_le _
      · obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
        exact (hlt l (by omega)).2
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, ρ = if 2 * k < Wd cap L then E - Us cap L else 0 := ⟨_, rfl⟩
    have hρ0 : ρ ≠ 0 → ρ < Wd cap L ∧ ρ = E - Us cap L := by
      intro h
      by_cases hw : 2 * k < Wd cap L
      · rw [if_pos hw] at hρ
        have := Us_succ cap L
        rcases hL with h' | h' <;> omega
      · rw [if_neg hw] at hρ
        exact absurd hρ h
    have hgu := gain_upper k E cap L hlt hL ρ hρ
    obtain ⟨p, H, hp, hpq, hH, hB, hτ⟩ := part2 k E hq cap L hUsL ρ hρ0
    refine ⟨p, H, hp, hpq, hH, ?_⟩
    intro mean
    have hall : ∀ U : Finset I, U.card = k → gain ≤ score mean U := fun U hU =>
      finish k gain p hp H (Us cap L + ρ) _ hB hτ (by rw [hg]; push_cast; linarith) U hU
    refine ⟨hall, ?_⟩
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hw' : ∀ i, 0 ≤ mean i ∧ mean i ≤ (cap i : ℝ) := by
      intro i
      refine ⟨div_nonneg (Nat.cast_nonneg _) hp'.le, ?_⟩
      show ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ) ≤ (cap i : ℝ)
      rw [div_le_iff₀ hp']
      have : ∑ z : Fin p, H z i ≤ ∑ z : Fin p, cap i :=
        Finset.sum_le_sum (fun z _ => (hH z).1 i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
      rw [mul_comm]
      exact_mod_cast this
    have hs' : (∑ i, mean i) ≤ (E : ℝ) := by
      show (∑ i, ((∑ z : Fin p, H z i : ℕ) : ℝ) / (p : ℝ)) ≤ (E : ℝ)
      rw [mean_sum p hp H _ hB]
      have := (hH ⟨0, hp⟩).2
      rw [hB] at this
      exact_mod_cast this
    obtain ⟨U, hU, h⟩ := part1 k E hk cap mean hw' hs'
    exact ⟨U, hU, le_antisymm (by rw [hg]; exact h) (hall U hU)⟩
