import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_695

open Finset

theorem key {ι : Type*} [DecidableEq ι] (n : ℕ) : ∀ (S : Finset ι) (f : ι → ℕ) (k : ℕ),
    S.card = n → 2 ^ k ∣ ∑ i ∈ S, 2 ^ f i → ∀ j ∈ S, k + 1 ≤ f j + S.card := by
  induction n with
  | zero =>
    intro S f k hS _ j hj
    simp [Finset.card_eq_zero.mp hS] at hj
  | succ n ih =>
    intro S f k hS hdiv j hj
    obtain ⟨j0, hj0, hmin⟩ := S.exists_min_image f ⟨j, hj⟩
    have hjj := hmin j hj
    suffices k + 1 ≤ f j0 + S.card by omega
    by_cases hk : k ≤ f j0
    · omega
    push_neg at hk
    have hsplit := (Finset.add_sum_erase S (fun i => 2 ^ f i) hj0).symm
    obtain ⟨j1, hj1, hf1⟩ : ∃ j1 ∈ S.erase j0, f j1 = f j0 := by
      by_contra hne
      push_neg at hne
      have h1 : 2 ^ (f j0 + 1) ∣ ∑ i ∈ S.erase j0, 2 ^ f i :=
        Finset.dvd_sum (fun i hi => pow_dvd_pow 2 (by
          have := hmin i (Finset.mem_of_mem_erase hi)
          have := hne i hi
          omega))
      have h2 : 2 ^ (f j0 + 1) ∣ ∑ i ∈ S, 2 ^ f i := (pow_dvd_pow 2 (by omega)).trans hdiv
      rw [hsplit] at h2
      have h3 : 2 ^ (f j0 + 1) ∣ 2 ^ f j0 := (Nat.dvd_add_left h1).mp h2
      have h4 := Nat.le_of_dvd (by positivity) h3
      have h5 : 2 ^ f j0 < 2 ^ (f j0 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hj1S : j1 ∈ S := Finset.mem_of_mem_erase hj1
    have hne : j1 ≠ j0 := Finset.ne_of_mem_erase hj1
    have hj0' : j0 ∈ S.erase j1 := Finset.mem_erase.mpr ⟨hne.symm, hj0⟩
    let f' := Function.update f j0 (f j0 + 1)
    have hf'0 : f' j0 = f j0 + 1 := Function.update_self _ _ _
    have hsum : ∑ i ∈ S.erase j1, 2 ^ f' i = ∑ i ∈ S, 2 ^ f i := by
      have e1 := Finset.add_sum_erase (S.erase j1) (fun i => 2 ^ f' i) hj0'
      have e2 := Finset.add_sum_erase (S.erase j1) (fun i => 2 ^ f i) hj0'
      have e3 := Finset.add_sum_erase S (fun i => 2 ^ f i) hj1S
      have e4 : ∑ i ∈ (S.erase j1).erase j0, 2 ^ f' i = ∑ i ∈ (S.erase j1).erase j0, 2 ^ f i :=
        Finset.sum_congr rfl (fun i hi => by
          simp only [f', Function.update_of_ne (Finset.ne_of_mem_erase hi)])
      rw [hf'0, e4, pow_succ] at e1
      rw [hf1] at e3
      linarith
    have := ih (S.erase j1) f' k (by rw [Finset.card_erase_of_mem hj1S]; omega)
      (hsum ▸ hdiv) j0 hj0'
    rw [hf'0, Finset.card_erase_of_mem hj1S] at this
    omega

variable {σ ω : Type*} [Fintype σ] [Fintype ω]

def fib (P : ω → Prop) [DecidablePred P] (ch : σ → ω → ℕ) (h : σ → ℕ) (w : ω) : ℕ :=
  if P w then ∏ t, ch t w ^ h t else 0

def sw (ch : σ → ω → ℕ) (h : σ → ℕ) (w : ω) : ℕ :=
  ∑ t ∈ univ.filter (fun u => ch u w = 1), h t

theorem pow_form (P : ω → Prop) [DecidablePred P] (ch : σ → ω → ℕ)
    (hch : ∀ t w, ch t w ≤ 2) (h : σ → ℕ) (w : ω) (hw : 0 < fib P ch h w) :
    fib P ch h w = 2 ^ (∑ t, h t - sw ch h w) ∧ sw ch h w ≤ ∑ t, h t := by
  have hP : P w := by
    by_contra hP
    simp [fib, hP] at hw
  have hf : fib P ch h w = ∏ t, ch t w ^ h t := if_pos hP
  have hle : sw ch h w ≤ ∑ t, h t := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine ⟨?_, hle⟩
  have hne : ∀ t, ch t w ^ h t ≠ 0 := by
    rw [hf] at hw
    exact fun t => Finset.prod_ne_zero_iff.mp hw.ne' t (Finset.mem_univ _)
  have hmul : fib P ch h w * 2 ^ sw ch h w = 2 ^ ∑ t, h t := by
    rw [hf, sw, Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    have h2 := hch t w
    have h0 := hne t
    rcases (show ch t w = 0 ∨ ch t w = 1 ∨ ch t w = 2 by omega) with e | e | e
    · rw [e] at h0
      have ht : h t = 0 := by
        by_contra hh
        exact h0 (zero_pow hh)
      simp [e, ht]
    · simp [e]
    · simp [e]
  have h3 : 2 ^ (∑ t, h t - sw ch h w) * 2 ^ sw ch h w = 2 ^ ∑ t, h t := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (hmul.trans h3.symm)

theorem part1 (P : ω → Prop) [DecidablePred P] (ch : σ → ω → ℕ)
    (hch : ∀ t w, ch t w ≤ 2) (h : σ → ℕ) (c d : ℕ)
    (hdiv : 2 ^ (c + ∑ t, h t) ∣ (∑ w, fib P ch h w) * 2 ^ d) (w : ω)
    (hw : 0 < fib P ch h w) :
    c + sw ch h w ≤ d + (univ.filter (fun w => 0 < fib P ch h w)).card - 1 := by
  classical
  set L := univ.filter (fun w => 0 < fib P ch h w) with hLdef
  have hL : ∑ w, fib P ch h w = ∑ w ∈ L, fib P ch h w := by
    rw [hLdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs with hh
    · rfl
    · omega
  have hS : (∑ w ∈ L, fib P ch h w) * 2 ^ d = ∑ w ∈ L, 2 ^ (∑ t, h t - sw ch h w + d) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [(pow_form P ch hch h w (Finset.mem_filter.mp hw).2).1, pow_add]
  have := key L.card L (fun w => ∑ t, h t - sw ch h w + d) (c + ∑ t, h t) rfl
    (by rw [← hS, ← hL]; exact hdiv) w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
  have := (pow_form P ch hch h w hw).2
  omega

theorem part2 (P : ω → Prop) [DecidablePred P] (ch : σ → ω → ℕ)
    (hch : ∀ t w, ch t w ≤ 2) (h : σ → ℕ) (B : ℕ) (hB : 0 < B) (c : ℕ) (w : ω)
    (hcap : 0 < fib P ch h w → ∀ t, ch t w = 1 → h t < B) :
    fib P ch (fun t => min (h t) B) w * 2 ^ (c + ∑ t, h t) =
      fib P ch h w * 2 ^ (c + ∑ t, min (h t) B) := by
  by_cases hP : P w
  swap
  · simp [fib, hP]
  by_cases h0 : fib P ch h w = 0
  · have : fib P ch (fun t => min (h t) B) w = 0 := by
      simp only [fib, if_pos hP] at h0 ⊢
      obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h0
      obtain ⟨e, hh⟩ := pow_eq_zero_iff'.mp ht
      exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [e]; exact zero_pow (by omega))
    rw [this, h0]
    simp
  have hcap' := hcap (Nat.pos_of_ne_zero h0)
  have hne : ∀ t, ch t w ^ h t ≠ 0 := by
    simp only [fib, if_pos hP] at h0
    exact fun t => Finset.prod_ne_zero_iff.mp h0 t (Finset.mem_univ _)
  simp only [fib, if_pos hP]
  rw [pow_add, pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  have key2 : ∏ t, (ch t w ^ min (h t) B * 2 ^ h t) = ∏ t, (ch t w ^ h t * 2 ^ min (h t) B) := by
    refine Finset.prod_congr rfl (fun t _ => ?_)
    by_cases hle : h t ≤ B
    · rw [min_eq_left hle]
    push_neg at hle
    rw [min_eq_right hle.le]
    have h2 := hch t w
    have h0t := hne t
    rcases (show ch t w = 0 ∨ ch t w = 1 ∨ ch t w = 2 by omega) with e | e | e
    · rw [e] at h0t
      exact absurd (zero_pow (by omega)) h0t
    · exact absurd (hcap' t e) (by omega)
    · rw [e, mul_comm]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at key2
  calc _ = 2 ^ c * ((∏ t, ch t w ^ min (h t) B) * ∏ t, 2 ^ h t) := by ring
    _ = 2 ^ c * ((∏ t, ch t w ^ h t) * ∏ t, 2 ^ min (h t) B) := by rw [key2]
    _ = _ := by ring

end PEqualNP.Outside.L_lib_695

open PEqualNP.Outside.L_lib_695 in
theorem PEqualNP.Outside.L_lib_695 :
let W := fun k : ℕ => Fin k → Bool
let Lit := fun k : ℕ => Fin k × Bool
let F := fun k : ℕ => Finset (Lit k × Lit k)
∀ c d : ℕ,
  let T := Finset (Lit c × Bool)
  let choices := fun (t : T) (w : W c) =>
    (Finset.univ.filter (fun b : Bool => ∀ edge ∈ t,
      w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2)).card
  let width := fun h : T → ℕ => c + ∑ t, h t
  let fiber := fun (D : F c) (h : T → ℕ) (w : W c) =>
    if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then
      ∏ t, (choices t w) ^ (h t)
    else 0
  let score := fun (D : F c) (h : T → ℕ) => ∑ w, fiber D h w
  ∀ (D : F c) (h : T → ℕ), 2 ^ (width h) ∣ score D h * 2 ^ d →
    let B := d + 2 ^ c
    let cropped := fun t : T => min (h t) B
    let live := (Finset.univ.filter (fun w : W c => 0 < fiber D h w)).card
    (∀ w : W c, 0 < fiber D h w →
      c + ∑ t ∈ (Finset.univ.filter (fun u : T => choices u w = 1)), h t ≤ d + live - 1) ∧
    ∀ w : W c, fiber D cropped w * 2 ^ (width h) = fiber D h w * 2 ^ (width cropped) := by
  intro W Lit F c d T choices width fiber score D h hdiv B cropped live
  have hch : ∀ t w, choices t w ≤ 2 := fun t w => (Finset.card_le_univ _).trans (by simp)
  have p1 : ∀ w : W c, 0 < fiber D h w →
      c + ∑ t ∈ (Finset.univ.filter (fun u : T => choices u w = 1)), h t ≤ d + live - 1 :=
    fun w hw => part1 (fun w : W c => ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2)
      choices hch h c d hdiv w hw
  refine ⟨p1, fun w => ?_⟩
  have hlive : live ≤ 2 ^ c := (Finset.card_le_univ _).trans (by simp [W])
  have hB : B = d + 2 ^ c := rfl
  exact part2 (fun w : W c => ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2) choices hch h B
    (by rw [hB]; positivity) c w (fun hw t ht => by
      have h1 := p1 w hw
      have h2 : h t ≤ ∑ t ∈ (Finset.univ.filter (fun u : T => choices u w = 1)), h t :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
      have h3 : 0 < live := Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
      rw [hB]
      generalize 2 ^ c = N at hlive h1 h3 ⊢
      omega)
