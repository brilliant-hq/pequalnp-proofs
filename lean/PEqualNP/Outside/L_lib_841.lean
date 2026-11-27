import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_841

open Finset

def cnt {t e : ℕ} (p : Fin t → Fin e) (l : Fin e) : ℕ :=
  (Finset.univ.filter (fun k => p k = l)).card

def marg {s e : ℕ} (src : Fin e → Fin s) (c : Fin e → ℕ) (i : Fin s) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l => src l = i), c l

def NN {s e t : ℕ} (src : Fin e → Fin s) (v : Fin t → Fin s) (c : Fin e → ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin t → Fin e => src ∘ p = v ∧ cnt p = c)).card

theorem cnt_cons {t e : ℕ} (a : Fin e) (q : Fin t → Fin e) (l : Fin e) :
    cnt (Fin.cons a q : Fin (t+1) → Fin e) l = cnt q l + if a = l then 1 else 0 := by
  simp only [cnt, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem sum_marg {s e : ℕ} (src : Fin e → Fin s) (c : Fin e → ℕ) :
    ∑ i, marg src c i = ∑ l, c l := Finset.sum_fiberwise univ src c

theorem marg_update {s e : ℕ} (src : Fin e → Fin s) (c : Fin e → ℕ) (a : Fin e)
    (h : 1 ≤ c a) (i : Fin s) :
    marg src (Function.update c a (c a - 1)) i + (if src a = i then 1 else 0) = marg src c i := by
  by_cases hi : src a = i
  · have ha : a ∈ Finset.univ.filter (fun l => src l = i) := by simp [hi]
    simp only [marg, if_pos hi]
    rw [Finset.sum_update_of_mem ha, Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ c ha]
    omega
  · simp only [marg, if_neg hi, add_zero]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have : l ≠ a := by
      rintro rfl
      simp at hl
      exact hi hl
    simp [Function.update_of_ne this]

theorem fact_prod_succ {n : ℕ} (f g : Fin n → ℕ) (a : Fin n)
    (h : ∀ i, f i = g i + if a = i then 1 else 0) :
    ∏ i, (f i).factorial = f a * ∏ i, (g i).factorial := by
  rw [Fintype.prod_eq_mul_prod_compl a, Fintype.prod_eq_mul_prod_compl a (fun i => (g i).factorial)]
  have ha : f a = g a + 1 := by simpa using h a
  rw [ha, Nat.factorial_succ]
  have : ∏ i ∈ ({a}ᶜ : Finset (Fin n)), (f i).factorial = ∏ i ∈ ({a}ᶜ : Finset (Fin n)), (g i).factorial := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have : a ≠ i := by
      intro hh
      simp [hh] at hi
    rw [h i, if_neg this, add_zero]
  rw [this]
  ring

theorem NN_succ {s e t : ℕ} (src : Fin e → Fin s) (v : Fin (t+1) → Fin s) (c : Fin e → ℕ) :
    NN src v c = ∑ a, if src a = v 0 ∧ 1 ≤ c a then
      NN src (Fin.tail v) (Function.update c a (c a - 1)) else 0 := by
  unfold NN
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Fin e).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Fin.consEquiv_apply]
  have h1 : ∀ q : Fin t → Fin e, (src ∘ (Fin.cons a q : Fin (t+1) → Fin e) = v) ↔
      (src a = v 0 ∧ src ∘ q = Fin.tail v) := by
    intro q
    simp [funext_iff, Fin.forall_fin_succ, Fin.tail]
  have h2 : ∀ q : Fin t → Fin e, (cnt (Fin.cons a q : Fin (t+1) → Fin e) = c) ↔
      (1 ≤ c a ∧ cnt q = Function.update c a (c a - 1)) := by
    intro q
    simp only [funext_iff, cnt_cons]
    constructor
    · intro h
      have ha := h a
      simp only [if_true] at ha
      refine ⟨by omega, fun l => ?_⟩
      by_cases hl : l = a
      · subst hl; simp; omega
      · have := h l
        rw [if_neg (Ne.symm hl)] at this
        simp [Function.update_of_ne hl]; omega
    · rintro ⟨h0, h⟩ l
      have := h l
      by_cases hl : l = a
      · subst hl; simp at this ⊢; omega
      · rw [if_neg (Ne.symm hl)]; simp [Function.update_of_ne hl] at this; omega
  by_cases hc : src a = v 0 ∧ 1 ≤ c a
  · rw [if_pos hc]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [h1, h2, hc, true_and]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    simp only [h1, h2]
    exact if_neg (by tauto)

theorem key {s e : ℕ} (src : Fin e → Fin s) : ∀ (t : ℕ) (v : Fin t → Fin s) (c : Fin e → ℕ),
    (∏ l, (c l).factorial) * NN src v c =
      if cnt v = marg src c then ∏ i, (cnt v i).factorial else 0 := by
  intro t
  induction t with
  | zero =>
    intro v c
    have hc0 : ∀ {n : ℕ} (p : Fin 0 → Fin n), cnt p = fun _ => 0 := fun p => by
      funext l; simp [cnt]
    have hN : NN src v c = if (fun _ => 0) = c then 1 else 0 := by
      unfold NN
      rw [Finset.card_filter, Fintype.sum_unique]
      have hv : src ∘ (default : Fin 0 → Fin e) = v := funext (fun k => k.elim0)
      simp only [hv, hc0, true_and]
    rw [hN, hc0 v]
    by_cases h : (fun _ => 0) = c
    · subst h
      have : (fun _ => 0) = marg src (fun _ : Fin e => 0) := by funext i; simp [marg]
      rw [if_pos rfl, if_pos this]
      simp
    · have hm : ¬ ((fun _ => 0) = marg src c) := by
        intro hm
        apply h
        have hs : ∑ l, c l = 0 := by rw [← sum_marg, ← hm]; simp
        funext l
        exact ((Finset.sum_eq_zero_iff.mp hs) l (mem_univ _)).symm
      rw [if_neg h, if_neg hm, mul_zero]
  | succ t ih =>
    intro v c
    rw [NN_succ, Finset.mul_sum]
    have hv : ∀ i, cnt v i = cnt (Fin.tail v) i + if v 0 = i then 1 else 0 := by
      intro i
      conv_lhs => rw [← Fin.cons_self_tail v]
      exact cnt_cons _ _ _
    have hterm : ∀ a, (∏ l, (c l).factorial) * (if src a = v 0 ∧ 1 ≤ c a then
        NN src (Fin.tail v) (Function.update c a (c a - 1)) else 0) =
        if src a = v 0 ∧ 1 ≤ c a then c a * (if cnt v = marg src c then
          ∏ i, (cnt (Fin.tail v) i).factorial else 0) else 0 := by
      intro a
      by_cases hc : src a = v 0 ∧ 1 ≤ c a
      · rw [if_pos hc, if_pos hc]
        have hf : ∏ l, (c l).factorial = c a * ∏ l, (Function.update c a (c a - 1) l).factorial := by
          refine fact_prod_succ _ _ a (fun l => ?_)
          by_cases hl : l = a
          · subst hl; simp; omega
          · simp [Function.update_of_ne hl, Ne.symm hl]
        rw [hf, mul_assoc, ih]
        congr 1
        have hiff : cnt (Fin.tail v) = marg src (Function.update c a (c a - 1)) ↔
            cnt v = marg src c := by
          simp only [funext_iff]
          have hmu := marg_update src c a hc.2
          rw [hc.1] at hmu
          constructor
          · intro h i
            have h1 := hmu i
            have h2 := h i
            have h3 := hv i
            split_ifs at h1 h3 <;> omega
          · intro h i
            have h1 := hmu i
            have h2 := h i
            have h3 := hv i
            split_ifs at h1 h3 <;> omega
        by_cases h : cnt v = marg src c
        · rw [if_pos h, if_pos (hiff.mpr h)]
        · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    by_cases h : cnt v = marg src c
    · simp only [if_pos h]
      rw [fact_prod_succ (cnt v) (cnt (Fin.tail v)) (v 0) hv]
      have hx : ∀ a, (if src a = v 0 ∧ 1 ≤ c a then c a * ∏ i, (cnt (Fin.tail v) i).factorial
          else 0) = (if src a = v 0 then c a else 0) * ∏ i, (cnt (Fin.tail v) i).factorial := by
        intro a
        by_cases h1 : src a = v 0 <;> by_cases h2 : 1 ≤ c a
        · simp [h1, h2]
        · have : c a = 0 := by omega
          simp [h1, this]
        · simp [h1]
        · simp [h1]
      rw [Finset.sum_congr rfl (fun a _ => hx a), ← Finset.sum_mul]
      congr 1
      rw [h, marg, Finset.sum_filter]
    · simp only [if_neg h, mul_zero, ite_self, Finset.sum_const_zero]

theorem NN_eq {s e t : ℕ} (src : Fin e → Fin s) (v : Fin t → Fin s) (c : Fin e → ℕ) :
    NN src v c = if cnt v = marg src c then ∏ i : Fin s, (marg src c i).factorial /
      (∏ j ∈ Finset.univ.filter (fun l => src l = i), (c j).factorial) else 0 := by
  have k := key src t v c
  have hB : ∏ l, (c l).factorial =
      ∏ i : Fin s, ∏ j ∈ Finset.univ.filter (fun l => src l = i), (c j).factorial :=
    (Finset.prod_fiberwise univ src _).symm
  have hpos : 0 < ∏ l, (c l).factorial :=
    Finset.prod_pos (fun l _ => Nat.factorial_pos _)
  split_ifs with h
  · rw [if_pos h, h] at k
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [k, hB, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (Nat.mul_div_cancel' (Nat.prod_factorial_dvd_factorial_sum _ _)).symm
  · rw [if_neg h] at k
    rcases Nat.mul_eq_zero.mp k with h0 | h0
    · omega
    · exact h0

theorem cnt_comp {s e t : ℕ} (f : Fin e → Fin s) (p : Fin t → Fin e) :
    cnt (f ∘ p) = marg f (cnt p) := by
  funext i
  simp only [marg, cnt]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext k
  simp

theorem prod_pow_cnt {e t : ℕ} (w : Fin e → ℕ) (p : Fin t → Fin e) :
    ∏ j, w (p j) = ∏ l, w l ^ cnt p l := by
  rw [← Finset.prod_fiberwise' univ p w]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [Finset.prod_const]
  rfl

theorem part1 (e t : ℕ) :
    Nat.card {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t} = Nat.choose (t+e-1) t := by
  have eqv : {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t} ≃ Sym (Fin e) t :=
    { toFun := fun m => ⟨∑ j, Multiset.replicate (m.1 j).1 j, by
        rw [Multiset.card_sum]; simpa using m.2⟩
      invFun := fun x => ⟨fun j => ⟨Multiset.count j x.1,
          (by have := Multiset.count_le_card j x.1; rw [x.2] at this; omega)⟩, by
        simp⟩
      left_inv := by
        intro m
        apply Subtype.ext
        funext j
        apply Fin.ext
        simp [Multiset.count_sum', Multiset.count_replicate]
      right_inv := by
        intro x
        apply Subtype.ext
        ext a
        simp [Multiset.count_sum', Multiset.count_replicate] }
  rw [Nat.card_congr eqv, Sym.natCard_sym_eq_choose, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.add_comm e t]

def cE {e t : ℕ} (p : Fin t → Fin e) : {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t} :=
  ⟨fun l => ⟨cnt p l, Nat.lt_succ_of_le (by
      unfold cnt; exact (Finset.card_le_univ _).trans (by simp))⟩, by
    simp only [cnt]
    rw [Finset.sum_card_fiberwise_eq_card_filter]; simp⟩

theorem cE_iff {e t : ℕ} (p : Fin t → Fin e) (m : {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t}) :
    cE p = m ↔ cnt p = fun l => (m.1 l).1 := by
  constructor
  · rintro rfl; rfl
  · intro h; apply Subtype.ext; funext l; apply Fin.ext; exact congrFun h l

theorem part2 (s e t : ℕ) (src dst : Fin e → Fin s) (w : Fin e → ℕ)
    (initial : (Fin t → Fin s) → ℕ) (wanted : Fin s → ℕ) :
    (∑ p : Fin t → Fin e, if cnt (dst ∘ p) = wanted then initial (src ∘ p) * ∏ j, w (p j) else 0) =
    ∑ m : {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t},
      if marg dst (fun l => (m.1 l).1) = wanted then
        (∑ v : Fin t → Fin s, if cnt v = marg src (fun l => (m.1 l).1) then initial v else 0) *
        (∏ i : Fin s, (marg src (fun l => (m.1 l).1) i).factorial /
          (∏ j ∈ Finset.univ.filter (fun l => src l = i), ((m.1 j).1).factorial)) *
        ∏ j, (w j)^((m.1 j).1) else 0 := by
  conv_lhs => rw [← Finset.sum_fiberwise univ cE]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hF : ∀ p ∈ univ.filter (fun p => cE p = m),
      (if cnt (dst ∘ p) = wanted then initial (src ∘ p) * ∏ j, w (p j) else 0) =
      if marg dst (fun l => (m.1 l).1) = wanted then
        initial (src ∘ p) * ∏ j, (w j)^((m.1 j).1) else 0 := by
    intro p hp
    have hp' : cnt p = fun l => (m.1 l).1 := (cE_iff p m).mp (by simpa using hp)
    rw [cnt_comp, prod_pow_cnt, hp']
  rw [Finset.sum_congr rfl hF]
  split_ifs with hw
  · rw [← Finset.sum_mul]
    congr 1
    rw [← Finset.sum_fiberwise _ (fun p => src ∘ p), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hcard : ∀ p ∈ (univ.filter (fun p => cE p = m)).filter (fun p => src ∘ p = v),
        initial (src ∘ p) = initial v := by
      intro p hp; simp at hp; rw [hp.2]
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
    have hN : ((univ.filter (fun p => cE p = m)).filter (fun p => src ∘ p = v)).card =
        NN src v (fun l => (m.1 l).1) := by
      unfold NN; rw [Finset.filter_filter]; congr 1; ext p; simp [cE_iff]; tauto
    rw [hN, NN_eq]
    split_ifs <;> ring
  · simp

end PEqualNP.Outside.L_lib_841

theorem PEqualNP.Outside.L_lib_841 : (∀ (s e t : ℕ), 0 < e →
  ∀ (src dst : Fin e → Fin s) (w : Fin e → ℕ)
    (initial : (Fin t → Fin s) → ℕ) (wanted : Fin s → ℕ),
  let multiplicity := fun (v : Fin t → Fin s) (i : Fin s) =>
    (Finset.univ.filter (fun j => v j = i)).card
  let edgeCounts := {m : Fin e → Fin (t+1) // ∑ j, (m j).val = t}
  let marginal := fun (endpoint : Fin e → Fin s) (m : edgeCounts) (i : Fin s) =>
    ∑ j ∈ Finset.univ.filter (fun l => endpoint l = i), (m.val j).val
  let prior := fun (a : Fin s → ℕ) =>
    ∑ v : Fin t → Fin s, if multiplicity v = a then initial v else 0
  let ways := fun (m : edgeCounts) =>
    ∏ i : Fin s, (marginal src m i).factorial /
      (∏ j ∈ Finset.univ.filter (fun l => src l = i), ((m.val j).val).factorial)
  Nat.card edgeCounts = Nat.choose (t+e-1) t ∧
    (∑ p : Fin t → Fin e,
      if multiplicity (dst ∘ p) = wanted
      then initial (src ∘ p) * ∏ j, w (p j) else 0) =
    ∑ m : edgeCounts, if marginal dst m = wanted
      then prior (marginal src m) * ways m * ∏ j, (w j)^((m.val j).val) else 0) := by
  intro s e t _ src dst w initial wanted multiplicity edgeCounts marginal prior ways
  exact ⟨PEqualNP.Outside.L_lib_841.part1 e t,
    PEqualNP.Outside.L_lib_841.part2 s e t src dst w initial wanted⟩
