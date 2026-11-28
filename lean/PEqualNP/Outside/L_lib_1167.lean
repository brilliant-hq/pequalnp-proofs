import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1167

open scoped BigOperators

private instance instFactPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

private def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, by revert a b; decide⟩

private lemma xor16_comm (a b : Fin 16) : xor16 a b = xor16 b a := by
  revert a b; decide

private lemma xor16_invol (a b : Fin 16) : xor16 (xor16 a b) b = a := by
  revert a b; decide

private def parity4 (n : ℕ) : Bool :=
  xor (xor (n.testBit 0) (n.testBit 1)) (xor (n.testBit 2) (n.testBit 3))

private def chi1 (a b : Fin 16) : ZMod 11 :=
  if parity4 (a.val &&& b.val) then -1 else 1

private lemma chi1_comm (a b : Fin 16) : chi1 a b = chi1 b a := by
  revert a b; decide

private lemma chi1_xor (a x y : Fin 16) : chi1 a (xor16 x y) = chi1 a x * chi1 a y := by
  revert a x y; decide

private lemma chi1_orth (a b : Fin 16) :
    ∑ x : Fin 16, chi1 a x * chi1 b x = if a = b then (16 : ZMod 11) else 0 := by
  revert a b; decide

private def pass1 (b : Bool) (w : Fin 16) : Bool :=
  (w.val &&& 3) != 0 && (w.val &&& 13) != (if b then 1 else 0)

private def ghat1 (b : Bool) (a : Fin 16) : ZMod 11 :=
  ∑ w : Fin 16, (if pass1 b w then (1 : ZMod 11) else 0) * chi1 a w

private def cat1 (a : Fin 16) : Fin 3 :=
  if a.val = 0 then 0
  else if a.val = 6 ∨ a.val = 7 ∨ a.val = 10 ∨ a.val = 11 ∨ a.val = 14 ∨ a.val = 15 then 1
  else 2

private lemma ghat1_false_ne (a : Fin 16) : ghat1 false a ≠ 0 ↔ cat1 a ≠ 0 := by
  revert a; decide

private lemma ghat1_true_ne (a : Fin 16) : ghat1 true a ≠ 0 ↔ cat1 a ≠ 1 := by
  revert a; decide

private lemma card_cat1_0 : (Finset.univ.filter fun a : Fin 16 => cat1 a = 0).card = 1 := by
  decide

private lemma card_cat1_1 : (Finset.univ.filter fun a : Fin 16 => cat1 a = 1).card = 6 := by
  decide

private lemma card_cat1_2 : (Finset.univ.filter fun a : Fin 16 => cat1 a = 2).card = 9 := by
  decide

private def chi {r : ℕ} (ξ x : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, chi1 (ξ j) (x j)

private lemma chi_comm {r : ℕ} (ξ x : Fin r → Fin 16) : chi ξ x = chi x ξ := by
  unfold chi; exact Finset.prod_congr rfl fun j _ => chi1_comm _ _

private lemma chi_xor {r : ℕ} (ξ z x : Fin r → Fin 16) :
    chi ξ (fun j => xor16 (z j) (x j)) = chi ξ z * chi ξ x := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => chi1_xor _ _ _

private lemma chi_orth {r : ℕ} (ξ η : Fin r → Fin 16) :
    ∑ x : Fin r → Fin 16, chi ξ x * chi η x = if ξ = η then (16 : ZMod 11) ^ r else 0 := by
  have h1 : ∀ x : Fin r → Fin 16, chi ξ x * chi η x = ∏ j : Fin r, (chi1 (ξ j) (x j) * chi1 (η j) (x j)) := by
    intro x; unfold chi; rw [Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [(Fintype.prod_sum (fun j a => chi1 (ξ j) a * chi1 (η j) a)).symm]
  simp_rw [chi1_orth]
  by_cases h : ξ = η
  · subst h
    simp
  · rw [if_neg h]
    have hex : ∃ j : Fin r, ξ j ≠ η j := by
      by_contra hall; push_neg at hall; exact h (funext hall)
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private def walsh {r : ℕ} (f : (Fin r → Fin 16) → ZMod 11) (ξ : Fin r → Fin 16) : ZMod 11 :=
  ∑ x : Fin r → Fin 16, f x * chi ξ x

private lemma walsh_invol {r : ℕ} (f : (Fin r → Fin 16) → ZMod 11) (x : Fin r → Fin 16) :
    walsh (walsh f) x = (16 : ZMod 11) ^ r * f x := by
  unfold walsh
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ y : Fin r → Fin 16,
      ∑ ξ : Fin r → Fin 16, f y * chi ξ y * chi x ξ =
      f y * ∑ ξ : Fin r → Fin 16, chi y ξ * chi x ξ := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [chi_comm ξ y, mul_assoc]
  simp_rw [hterm, chi_orth]
  simp [mul_comm]

private lemma sixteen_ne_zero : (16 : ZMod 11) ≠ 0 := by decide

private lemma walsh_bijective (r : ℕ) : Function.Bijective (@walsh r) := by
  refine (Finite.injective_iff_bijective).mp ?_
  intro f g hfg
  ext x
  have h := congrFun (congrArg walsh hfg) x
  rw [walsh_invol, walsh_invol] at h
  exact mul_left_cancel₀ (pow_ne_zero r sixteen_ne_zero) h

private noncomputable def passFn {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0)

private lemma passFn_iff {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    passFn e z x = true ↔ ∀ j : Fin r, pass1 (decide (j ∈ e)) (xor16 (z j) (x j)) = true := by
  unfold passFn pass1 xor16
  simp only [List.all_eq_true, Finset.mem_toList, Finset.mem_univ, forall_true_left]
  refine forall_congr' fun j => ?_
  by_cases hj : j ∈ e <;> simp [hj]

private lemma passFn_ind {r : ℕ} (e : Finset (Fin r)) (z x : Fin r → Fin 16) :
    (if passFn e z x then (1 : ZMod 11) else 0) =
    ∏ j : Fin r, (if pass1 (decide (j ∈ e)) (xor16 (z j) (x j)) then (1 : ZMod 11) else 0) := by
  by_cases hp : passFn e z x = true
  · rw [if_pos hp]
    have hall := (passFn_iff e z x).mp hp
    symm
    exact Finset.prod_eq_one fun j _ => if_pos (hall j)
  · rw [if_neg hp]
    have hnot : ¬ ∀ j : Fin r, pass1 (decide (j ∈ e)) (xor16 (z j) (x j)) = true :=
      fun h => hp ((passFn_iff e z x).mpr h)
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private noncomputable def conv {r : ℕ} (e : Finset (Fin r)) (f : (Fin r → Fin 16) → ZMod 11)
    (z : Fin r → Fin 16) : ZMod 11 :=
  ∑ x : Fin r → Fin 16, (if passFn e z x then (1 : ZMod 11) else 0) * f x

private def ghat {r : ℕ} (e : Finset (Fin r)) (ξ : Fin r → Fin 16) : ZMod 11 :=
  ∏ j : Fin r, ghat1 (decide (j ∈ e)) (ξ j)

private lemma walsh_conv {r : ℕ} (e : Finset (Fin r)) (f : (Fin r → Fin 16) → ZMod 11)
    (ξ : Fin r → Fin 16) :
    walsh (conv e f) ξ = ghat e ξ * walsh f ξ := by
  unfold walsh conv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ x : Fin r → Fin 16,
      ∑ z : Fin r → Fin 16, (if passFn e z x then (1 : ZMod 11) else 0) * f x * chi ξ z =
      ghat e ξ * (f x * chi ξ x) := by
    intro x
    let bij : (Fin r → Fin 16) ≃ (Fin r → Fin 16) :=
      { toFun := fun z j => xor16 (z j) (x j)
        invFun := fun w j => xor16 (w j) (x j)
        left_inv := fun z => funext fun j => xor16_invol _ _
        right_inv := fun w => funext fun j => xor16_invol _ _ }
    have hsum := Fintype.sum_equiv bij
      (fun z => (if passFn e z x then (1 : ZMod 11) else 0) * f x * chi ξ z)
      (fun w => (∏ j : Fin r, (if pass1 (decide (j ∈ e)) (w j) then (1 : ZMod 11) else 0) * chi1 (ξ j) (w j)) * (f x * chi ξ x))
      (fun z => by
        rw [passFn_ind]
        have hz : chi ξ z = chi ξ (bij z) * chi ξ x := by
          have : z = fun j => xor16 (bij z j) (x j) := funext fun j => (xor16_invol (z j) (x j)).symm
          conv_lhs => rw [this]
          exact chi_xor ξ (bij z) x
        rw [hz]
        have hp : (∏ j : Fin r, (if pass1 (decide (j ∈ e)) (bij z j) then (1 : ZMod 11) else 0)) * chi ξ (bij z) =
            ∏ j : Fin r, ((if pass1 (decide (j ∈ e)) (bij z j) then (1 : ZMod 11) else 0) * chi1 (ξ j) (bij z j)) := by
          unfold chi; rw [Finset.prod_mul_distrib]
        calc
          (∏ j : Fin r, if pass1 (decide (j ∈ e)) (xor16 (z j) (x j)) = true then (1 : ZMod 11) else 0) * f x * (chi ξ (bij z) * chi ξ x)
            = ((∏ j : Fin r, if pass1 (decide (j ∈ e)) (bij z j) = true then (1 : ZMod 11) else 0) * chi ξ (bij z)) * (f x * chi ξ x) := by
              change ((∏ j : Fin r, if pass1 (decide (j ∈ e)) (bij z j) = true then (1 : ZMod 11) else 0) * f x * (chi ξ (bij z) * chi ξ x)) = _
              ring
          _ = (∏ j : Fin r, (if pass1 (decide (j ∈ e)) (bij z j) = true then (1 : ZMod 11) else 0) * chi1 (ξ j) (bij z j)) * (f x * chi ξ x) := by rw [hp])
    rw [hsum, ← Finset.sum_mul, (Fintype.prod_sum (fun j a => (if pass1 (decide (j ∈ e)) a = true then (1 : ZMod 11) else 0) * chi1 (ξ j) a)).symm]
    rfl
  simp_rw [hinner, ← Finset.mul_sum]

private lemma ghat_ne_zero_iff {r : ℕ} (e : Finset (Fin r)) (ξ : Fin r → Fin 16) :
    ghat e ξ ≠ 0 ↔ ∀ j : Fin r, (cat1 (ξ j) = 0 → j ∈ e) ∧ (cat1 (ξ j) = 1 → j ∉ e) := by
  unfold ghat
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h j
    have hj := h j (Finset.mem_univ j)
    by_cases hje : j ∈ e
    · simp only [hje, decide_true] at hj
      have hc := (ghat1_true_ne (ξ j)).mp hj
      exact ⟨fun _ => hje, fun h1 => absurd h1 hc⟩
    · simp only [hje, decide_false] at hj
      have hc := (ghat1_false_ne (ξ j)).mp hj
      exact ⟨fun h0 => absurd h0 hc, fun _ => hje⟩
  · intro h j _
    obtain ⟨h0, h1⟩ := h j
    by_cases hje : j ∈ e
    · simp only [hje, decide_true]
      exact (ghat1_true_ne (ξ j)).mpr fun hc => h1 hc hje
    · simp only [hje, decide_false]
      exact (ghat1_false_ne (ξ j)).mpr fun hc => hje (h0 hc)

private def setB {r : ℕ} (ξ : Fin r → Fin 16) : Finset (Fin r) :=
  Finset.univ.filter fun j => cat1 (ξ j) = 1

private def setF {r : ℕ} (ξ : Fin r → Fin 16) : Finset (Fin r) :=
  Finset.univ.filter fun j => cat1 (ξ j) = 2

private lemma disjoint_setB_setF {r : ℕ} (ξ : Fin r → Fin 16) : Disjoint (setB ξ) (setF ξ) := by
  rw [Finset.disjoint_left]
  intro j hB hF
  simp only [setB, setF, Finset.mem_filter, Finset.mem_univ, true_and] at hB hF
  rw [hB] at hF
  exact absurd hF (by decide)

private def isFace {r : ℕ} (U : Finset (Finset (Fin r))) (B F : Finset (Fin r)) : Prop :=
  Disjoint B F ∧ ∀ S ⊆ F, (Finset.univ : Finset (Fin r)) \ (B ∪ S) ∈ U

private instance {r : ℕ} (U : Finset (Finset (Fin r))) (B F : Finset (Fin r)) :
    Decidable (isFace U B F) := by
  unfold isFace; infer_instance

private lemma lost_iff_isFace {r : ℕ} (U : Finset (Finset (Fin r))) (ξ : Fin r → Fin 16) :
    (∀ e ∈ (Finset.univ : Finset (Finset (Fin r))) \ U, ghat e ξ = 0) ↔
    isFace U (setB ξ) (setF ξ) := by
  constructor
  · intro h
    refine ⟨disjoint_setB_setF ξ, fun S hS => ?_⟩
    by_contra hnot
    have he : (Finset.univ : Finset (Fin r)) \ (setB ξ ∪ S) ∈ (Finset.univ : Finset (Finset (Fin r))) \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
    have h0 := h _ he
    have hnz : ghat ((Finset.univ : Finset (Fin r)) \ (setB ξ ∪ S)) ξ ≠ 0 := by
      rw [ghat_ne_zero_iff]
      intro j
      constructor
      · intro hc0
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hmem
        rcases Finset.mem_union.mp hmem with hB | hS'
        · simp only [setB, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          rw [hc0] at hB; exact absurd hB (by decide)
        · have hF := hS hS'
          simp only [setF, Finset.mem_filter, Finset.mem_univ, true_and] at hF
          rw [hc0] at hF; exact absurd hF (by decide)
      · intro hc1 hmem
        rw [Finset.mem_sdiff] at hmem
        exact hmem.2 (Finset.mem_union_left S (by simp [setB, hc1]))
    exact hnz h0
  · rintro ⟨_, hface⟩ e he
    rw [Finset.mem_sdiff] at he
    by_contra hnz
    have hcompat := (ghat_ne_zero_iff e ξ).mp hnz
    let X := (Finset.univ : Finset (Fin r)) \ e
    have hBX : setB ξ ⊆ X := by
      intro j hj
      simp only [setB, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hcompat j).2 hj⟩
    let S := X \ setB ξ
    have hSF : S ⊆ setF ξ := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      have hne : j ∉ e := (Finset.mem_sdiff.mp hj.1).2
      have hne0 : cat1 (ξ j) ≠ 0 := fun hc0 => hne ((hcompat j).1 hc0)
      have hne1 : cat1 (ξ j) ≠ 1 := fun hc1 => hj.2 (by simp [setB, hc1])
      simp only [setF, Finset.mem_filter, Finset.mem_univ, true_and]
      have hfin := (cat1 (ξ j)).isLt
      omega
    have hBSX : setB ξ ∪ S = X := Finset.union_sdiff_of_subset hBX
    have heq : (Finset.univ : Finset (Fin r)) \ (setB ξ ∪ S) = e := by
      rw [hBSX]; ext j; simp [X]
    have hin := hface S hSF
    rw [heq] at hin
    exact he.2 hin

private def lostSet {r : ℕ} (U : Finset (Finset (Fin r))) : Finset (Fin r → Fin 16) :=
  Finset.univ.filter fun ξ => isFace U (setB ξ) (setF ξ)

private lemma kernelSize_eq_pow_lost {r : ℕ} (U : Finset (Finset (Fin r))) :
    ((Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
      ∀ q ∈ ((Finset.univ : Finset (Finset (Fin r))) \ U).product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0)).card =
    11 ^ (lostSet U).card := by
  let toZ : ((Fin r → Fin 16) → Fin 11) ≃ ((Fin r → Fin 16) → ZMod 11) :=
    { toFun := fun d x => ((d x).val : ZMod 11)
      invFun := fun f x => ⟨(f x).val, ZMod.val_lt _⟩
      left_inv := fun d => funext fun x => Fin.ext (by
        change ((d x).val : ZMod 11).val = (d x).val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (d x).isLt])
      right_inv := fun f => funext fun x => by
        change (((f x).val : ℕ) : ZMod 11) = f x
        exact ZMod.natCast_zmod_val (f x) }
  let W : ((Fin r → Fin 16) → Fin 11) ≃ ((Fin r → Fin 16) → ZMod 11) :=
    toZ.trans (Equiv.ofBijective (@walsh r) (walsh_bijective r))
  have hcond : ∀ d : (Fin r → Fin 16) → Fin 11,
      (∀ q ∈ ((Finset.univ : Finset (Finset (Fin r))) \ U).product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0) ↔
      (∀ ξ : Fin r → Fin 16, ξ ∉ lostSet U → W d ξ = 0) := by
    intro d
    have h1 : (∀ q ∈ ((Finset.univ : Finset (Finset (Fin r))) \ U).product (Finset.univ : Finset (Fin r → Fin 16)),
        (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0) ↔
        (∀ e ∈ (Finset.univ : Finset (Finset (Fin r))) \ U, conv e (toZ d) = 0) := by
      constructor
      · intro h e he
        ext z
        have hq := h (e, z) (Finset.mem_product.mpr ⟨he, Finset.mem_univ z⟩)
        change conv e (toZ d) z = 0
        unfold conv
        have hsum : ∑ x : Fin r → Fin 16, (if passFn e z x = true then (1 : ZMod 11) else 0) * toZ d x =
            ((((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn e z x)).sum (fun x => (d x).val) : ℕ) : ZMod 11) := by
          rw [Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hp : passFn e z x = true <;> simp [hp, toZ]
        rw [hsum, ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero hq
      · intro h q hq
        rw [Finset.product_eq_sprod, Finset.mem_product] at hq
        have hz := congrFun (h q.1 hq.1) q.2
        change conv q.1 (toZ d) q.2 = 0 at hz
        unfold conv at hz
        have hsum : ∑ x : Fin r → Fin 16, (if passFn q.1 q.2 x = true then (1 : ZMod 11) else 0) * toZ d x =
            ((((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn q.1 q.2 x)).sum (fun x => (d x).val) : ℕ) : ZMod 11) := by
          rw [Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hp : passFn q.1 q.2 x = true <;> simp [hp, toZ]
        rw [hsum, ZMod.natCast_eq_zero_iff] at hz
        exact Nat.mod_eq_zero_of_dvd hz
    rw [h1]
    have h2 : (∀ e ∈ (Finset.univ : Finset (Finset (Fin r))) \ U, conv e (toZ d) = 0) ↔
        (∀ e ∈ (Finset.univ : Finset (Finset (Fin r))) \ U, ∀ ξ, ghat e ξ * W d ξ = 0) := by
      refine forall₂_congr fun e _ => ?_
      constructor
      · intro hc ξ
        have hw := congrFun (congrArg walsh hc) ξ
        rw [walsh_conv] at hw
        have hw0 : walsh (0 : (Fin r → Fin 16) → ZMod 11) ξ = 0 := by simp [walsh]
        rw [hw0] at hw
        exact hw
      · intro hw
        apply (walsh_bijective r).1
        ext ξ
        rw [walsh_conv]
        have hw0 : walsh (0 : (Fin r → Fin 16) → ZMod 11) ξ = 0 := by simp [walsh]
        rw [hw0]
        exact hw ξ
    rw [h2]
    constructor
    · intro h ξ hnot
      simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      rw [← lost_iff_isFace] at hnot
      push_neg at hnot
      obtain ⟨e, he, hnz⟩ := hnot
      exact (mul_eq_zero.mp (h e he ξ)).resolve_left hnz
    · intro h e he ξ
      by_cases hξ : ξ ∈ lostSet U
      · simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
        rw [← lost_iff_isFace] at hξ
        rw [hξ e he, zero_mul]
      · rw [h ξ hξ, mul_zero]
  let S := (Finset.univ : Finset ((Fin r → Fin 16) → Fin 11)).filter (fun d =>
    ∀ q ∈ ((Finset.univ : Finset (Finset (Fin r))) \ U).product (Finset.univ : Finset (Fin r → Fin 16)),
      (((Finset.univ : Finset (Fin r → Fin 16)).filter (fun x => passFn q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0)
  have hcard : S.card = Fintype.card {g : (Fin r → Fin 16) → ZMod 11 // ∀ ξ, ξ ∉ lostSet U → g ξ = 0} := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨d, hd⟩ => ⟨W d, (hcond d).mp (Finset.mem_filter.mp hd).2⟩
        invFun := fun ⟨g, hg⟩ => ⟨W.symm g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcond (W.symm g)).mpr (by simpa using hg)⟩⟩
        left_inv := fun ⟨d, _⟩ => Subtype.ext (W.symm_apply_apply d)
        right_inv := fun ⟨g, _⟩ => Subtype.ext (W.apply_symm_apply g) }
  rw [hcard]
  have hsub : Fintype.card {g : (Fin r → Fin 16) → ZMod 11 // ∀ ξ, ξ ∉ lostSet U → g ξ = 0} =
      Fintype.card (lostSet U → ZMod 11) := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨g, _⟩ ξ => g ξ.1
        invFun := fun h => ⟨fun ξ => if hξ : ξ ∈ lostSet U then h ⟨ξ, hξ⟩ else 0, fun ξ hnot => dif_neg hnot⟩
        left_inv := fun ⟨g, hg⟩ => Subtype.ext (funext fun ξ => by
          by_cases hξ : ξ ∈ lostSet U
          · simp [hξ]
          · simp [hξ, hg ξ hξ])
        right_inv := fun h => funext fun ⟨ξ, hξ⟩ => by simp [hξ] }
  rw [hsub, Fintype.card_fun, ZMod.card, Fintype.card_coe]

private lemma card_fiber_BF {r : ℕ} (B F : Finset (Fin r)) (hdisj : Disjoint B F) :
    ((Finset.univ : Finset (Fin r → Fin 16)).filter fun ξ => setB ξ = B ∧ setF ξ = F).card =
    6 ^ B.card * 9 ^ F.card := by
  let target : Fin r → Fin 3 := fun j => if j ∈ B then 1 else if j ∈ F then 2 else 0
  have hmem : ∀ ξ : Fin r → Fin 16, (setB ξ = B ∧ setF ξ = F) ↔ ∀ j : Fin r, cat1 (ξ j) = target j := by
    intro ξ
    constructor
    · rintro ⟨hB, hF⟩ j
      by_cases hjB : j ∈ B
      · simp only [target, hjB, ite_true]
        rw [← hB] at hjB
        exact (Finset.mem_filter.mp hjB).2
      · by_cases hjF : j ∈ F
        · simp only [target, hjB, hjF, ite_false, ite_true]
          rw [← hF] at hjF
          exact (Finset.mem_filter.mp hjF).2
        · simp only [target, hjB, hjF, ite_false]
          have hne1 : cat1 (ξ j) ≠ 1 := fun hc => hjB (hB ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
          have hne2 : cat1 (ξ j) ≠ 2 := fun hc => hjF (hF ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
          have hlt := (cat1 (ξ j)).isLt
          omega
    · intro hall
      constructor
      · ext j
        simp only [setB, Finset.mem_filter, Finset.mem_univ, true_and, hall j]
        by_cases hjB : j ∈ B
        · simp [target, hjB]
        · by_cases hjF : j ∈ F
          · simp [target, hjB, hjF]
          · simp [target, hjB, hjF]
      · ext j
        simp only [setF, Finset.mem_filter, Finset.mem_univ, true_and, hall j]
        by_cases hjB : j ∈ B
        · have hjF : j ∉ F := Finset.disjoint_left.mp hdisj hjB
          simp [target, hjB, hjF]
        · by_cases hjF : j ∈ F
          · simp [target, hjB, hjF]
          · simp [target, hjB, hjF]
  have heq : ((Finset.univ : Finset (Fin r → Fin 16)).filter fun ξ => setB ξ = B ∧ setF ξ = F).card =
      Fintype.card (∀ j : Fin r, {a : Fin 16 // cat1 a = target j}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨ξ, hξ⟩ j => ⟨ξ j, (hmem ξ).mp (Finset.mem_filter.mp hξ).2 j⟩
        invFun := fun f => ⟨fun j => (f j).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem _).mpr fun j => (f j).2⟩⟩
        left_inv := fun ⟨ξ, _⟩ => Subtype.ext rfl
        right_inv := fun f => funext fun j => Subtype.ext rfl }
  rw [heq, Fintype.card_pi]
  have hfac : ∀ j : Fin r, Fintype.card {a : Fin 16 // cat1 a = target j} =
      if j ∈ B then 6 else if j ∈ F then 9 else 1 := by
    intro j
    rw [Fintype.card_subtype]
    by_cases hjB : j ∈ B
    · simp [target, hjB, card_cat1_1]
    · by_cases hjF : j ∈ F
      · simp [target, hjB, hjF, card_cat1_2]
      · simp [target, hjB, hjF, card_cat1_0]
  simp_rw [hfac]
  have hsplit : (Finset.univ : Finset (Fin r)) = B ∪ (F ∪ ((Finset.univ : Finset (Fin r)) \ (B ∪ F))) := by
    ext j; simp; tauto
  have hd1 : Disjoint B (F ∪ ((Finset.univ : Finset (Fin r)) \ (B ∪ F))) := by
    rw [Finset.disjoint_left]
    intro j hj h2
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or] at h2
    rcases h2 with hF | ⟨h1, _⟩
    · exact Finset.disjoint_left.mp hdisj hj hF
    · exact h1 hj
  have hd2 : Disjoint F ((Finset.univ : Finset (Fin r)) \ (B ∪ F)) := by
    rw [Finset.disjoint_left]
    intro j hj h2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at h2
    exact h2.2 hj
  conv_lhs => rw [hsplit]
  rw [Finset.prod_union hd1, Finset.prod_union hd2]
  have p1 : ∏ j ∈ B, (if j ∈ B then 6 else if j ∈ F then 9 else 1) = 6 ^ B.card := by
    rw [Finset.prod_congr rfl fun j hj => if_pos hj, Finset.prod_const]
  have p2 : ∏ j ∈ F, (if j ∈ B then 6 else if j ∈ F then 9 else 1) = 9 ^ F.card := by
    rw [Finset.prod_congr rfl fun j hj => by rw [if_neg (Finset.disjoint_right.mp hdisj hj), if_pos hj], Finset.prod_const]
  have p3 : ∏ j ∈ (Finset.univ : Finset (Fin r)) \ (B ∪ F), (if j ∈ B then 6 else if j ∈ F then 9 else 1) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hj
    rw [if_neg hj.2.1, if_neg hj.2.2]
  rw [p1, p2, p3, mul_one]

private lemma card_lostSet_eq_sum_faces {r : ℕ} (U : Finset (Finset (Fin r))) :
    (lostSet U).card =
    ∑ p ∈ ((Finset.univ : Finset (Finset (Fin r) × Finset (Fin r))).filter fun p => isFace U p.1 p.2),
      6 ^ p.1.card * 9 ^ p.2.card := by
  have hmaps : ∀ ξ ∈ lostSet U, (setB ξ, setF ξ) ∈
      (Finset.univ : Finset (Finset (Fin r) × Finset (Fin r))).filter fun p => isFace U p.1 p.2 := by
    intro ξ hξ
    simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
    exact hξ
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hface := (Finset.mem_filter.mp hp).2
  have hflt : (lostSet U).filter (fun ξ => (setB ξ, setF ξ) = p) =
      Finset.univ.filter (fun ξ => setB ξ = p.1 ∧ setF ξ = p.2) := by
    ext ξ
    simp only [lostSet, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm ▸ h2.symm ▸ hface, h1, h2⟩
  rw [hflt, card_fiber_BF p.1 p.2 hface.1]

private lemma face_card_le_two {r : ℕ} {U : Finset (Finset (Fin r))}
    (hU : ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card ≤ 2)
    {B F : Finset (Fin r)} (hf : isFace U B F) : (B ∪ F).card ≤ 2 := by
  have hin := hf.2 F Finset.Subset.rfl
  have hle := hU _ hin
  have heq : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ (B ∪ F)) = B ∪ F := by
    ext j; simp
  rwa [heq] at hle

private lemma card_lostSet_formula {r : ℕ} (U : Finset (Finset (Fin r))) (center : Bool)
    (hcen : decide ((Finset.univ : Finset (Fin r)) ∈ U) = center)
    (hle2 : ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card ≤ 2) :
    let U1 := (Finset.univ : Finset (Fin r)).filter fun v => (Finset.univ : Finset (Fin r)) \ {v} ∈ U
    let U2 := ((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (Finset.univ : Finset (Fin r)) \ P ∈ U
    (lostSet U).card =
      center.toNat + (6 + 9 * center.toNat) * U1.card +
      ∑ P ∈ U2, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) := by
  intro U1 U2
  rw [card_lostSet_eq_sum_faces]
  let faces := (Finset.univ : Finset (Finset (Fin r) × Finset (Fin r))).filter fun p => isFace U p.1 p.2
  have hmaps : ∀ p ∈ faces, p.1 ∪ p.2 ∈ (Finset.univ : Finset (Finset (Fin r))).filter fun P => P.card ≤ 2 := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, face_card_le_two hle2 (Finset.mem_filter.mp hp).2⟩
  change ∑ p ∈ faces, 6 ^ p.1.card * 9 ^ p.2.card = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  let S0 := (Finset.univ : Finset (Finset (Fin r))).filter fun P => P.card = 0
  let S1 := (Finset.univ : Finset (Finset (Fin r))).filter fun P => P.card = 1
  let S2 := (Finset.univ : Finset (Finset (Fin r))).filter fun P => P.card = 2
  have hpart : (Finset.univ : Finset (Finset (Fin r))).filter (fun P => P.card ≤ 2) = S0 ∪ (S1 ∪ S2) := by
    ext P; simp only [S0, S1, S2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; omega
  have hd0 : Disjoint S0 (S1 ∪ S2) := by
    rw [Finset.disjoint_left]; intro P h0 h12
    simp only [S0, S1, S2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at h0 h12; omega
  have hd12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro P h1 h2
    simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
  rw [hpart, Finset.sum_union hd0, Finset.sum_union hd12]
  have hsum0 : ∑ P ∈ S0, ∑ p ∈ faces.filter (fun p => p.1 ∪ p.2 = P), 6 ^ p.1.card * 9 ^ p.2.card = center.toNat := by
    have hS0 : S0 = {∅} := by ext P; simp [S0]
    rw [hS0, Finset.sum_singleton]
    have hflt : faces.filter (fun p => p.1 ∪ p.2 = ∅) = if (Finset.univ : Finset (Fin r)) ∈ U then {(∅, ∅)} else ∅ := by
      ext ⟨B, F⟩
      by_cases hc : (Finset.univ : Finset (Fin r)) ∈ U
      · simp only [hc, ite_true, faces, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq, Finset.union_eq_empty]
        constructor
        · rintro ⟨_, hB, hF⟩; exact ⟨hB, hF⟩
        · rintro ⟨rfl, rfl⟩
          refine ⟨⟨by simp, fun S hS => ?_⟩, rfl, rfl⟩
          have : S = ∅ := Finset.subset_empty.mp hS
          subst this; simpa using hc
      · simp only [hc, ite_false, faces, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Finset.union_eq_empty]
        rintro ⟨⟨_, hf⟩, rfl, rfl⟩
        have hin := hf ∅ Finset.Subset.rfl
        simp at hin
        exact hc hin
    rw [hflt]
    by_cases hc : (Finset.univ : Finset (Fin r)) ∈ U
    · have : center = true := by rw [← hcen]; exact decide_eq_true hc
      subst this; simp [hc]
    · have : center = false := by rw [← hcen]; exact decide_eq_false hc
      subst this; simp [hc]
  have hsum1 : ∑ P ∈ S1, ∑ p ∈ faces.filter (fun p => p.1 ∪ p.2 = P), 6 ^ p.1.card * 9 ^ p.2.card =
      (6 + 9 * center.toNat) * U1.card := by
    have hS1 : S1 = (Finset.univ : Finset (Fin r)).image (fun v => ({v} : Finset (Fin r))) := by
      ext P
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.card_eq_one]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
      · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
    rw [hS1, Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
    have hterm1 : ∀ v : Fin r,
        ∑ p ∈ faces.filter (fun p => p.1 ∪ p.2 = {v}), 6 ^ p.1.card * 9 ^ p.2.card =
        if v ∈ U1 then 6 + 9 * center.toNat else 0 := by
      intro v
      have hmem1 : ∀ B F : Finset (Fin r),
          (B, F) ∈ faces.filter (fun p => p.1 ∪ p.2 = {v}) ↔
          ((B = {v} ∧ F = ∅ ∧ v ∈ U1) ∨ (B = ∅ ∧ F = {v} ∧ v ∈ U1 ∧ (Finset.univ : Finset (Fin r)) ∈ U)) := by
        intro B F
        rw [Finset.mem_filter]
        dsimp only [faces]
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, U1, isFace]
        constructor
        · rintro ⟨⟨hd, hf⟩, hun⟩
          have hsubB : B ⊆ {v} := hun ▸ Finset.subset_union_left
          rcases Finset.subset_singleton_iff.mp hsubB with rfl | rfl
          · right
            have hF : F = {v} := by simpa using hun
            subst hF
            refine ⟨rfl, rfl, ?_, ?_⟩
            · simpa using hf {v} Finset.Subset.rfl
            · simpa using hf ∅ (Finset.empty_subset _)
          · left
            have hF : F = ∅ := by
              ext x; simp only [Finset.notMem_empty, iff_false]
              intro hx
              have hxv : x = v := Finset.mem_singleton.mp (hun ▸ Finset.mem_union_right _ hx)
              subst hxv
              exact Finset.disjoint_left.mp hd (Finset.mem_singleton_self _) hx
            subst hF
            refine ⟨rfl, rfl, ?_⟩
            simpa using hf ∅ Finset.Subset.rfl
        · rintro (⟨rfl, rfl, hv⟩ | ⟨rfl, rfl, hv, hc⟩)
          · refine ⟨⟨by simp, fun S hS => ?_⟩, by simp⟩
            have : S = ∅ := Finset.subset_empty.mp hS
            subst this; simpa using hv
          · refine ⟨⟨by simp, fun S hS => ?_⟩, by simp⟩
            rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
            · simpa using hc
            · simpa using hv
      by_cases hv : v ∈ U1
      · rw [if_pos hv]
        by_cases hc : (Finset.univ : Finset (Fin r)) ∈ U
        · have hct : center = true := by rw [← hcen]; exact decide_eq_true hc
          have hset : faces.filter (fun p => p.1 ∪ p.2 = {v}) = {({v}, ∅), (∅, {v})} := by
            ext ⟨B, F⟩; rw [hmem1]; simp [hv, hc]
          rw [hset, Finset.sum_pair (by intro h; simp at h), hct]
          norm_num
        · have hcf : center = false := by rw [← hcen]; exact decide_eq_false hc
          have hset : faces.filter (fun p => p.1 ∪ p.2 = {v}) = {({v}, ∅)} := by
            ext ⟨B, F⟩; rw [hmem1]; simp [hv, hc]
          rw [hset, Finset.sum_singleton, hcf]
          norm_num
      · rw [if_neg hv]
        have hset : faces.filter (fun p => p.1 ∪ p.2 = {v}) = ∅ := by
          ext ⟨B, F⟩; rw [hmem1]; simp [hv]
        rw [hset, Finset.sum_empty]
    simp_rw [hterm1, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hsum2 : ∑ P ∈ S2, ∑ p ∈ faces.filter (fun p => p.1 ∪ p.2 = P), 6 ^ p.1.card * 9 ^ p.2.card =
      ∑ P ∈ U2, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) := by
    have hS2 : S2 = (Finset.univ : Finset (Fin r)).powersetCard 2 := by
      ext P; simp [S2, Finset.mem_powersetCard]
    rw [hS2]
    have hterm2 : ∀ P ∈ (Finset.univ : Finset (Fin r)).powersetCard 2,
        ∑ p ∈ faces.filter (fun p => p.1 ∪ p.2 = P), 6 ^ p.1.card * 9 ^ p.2.card =
        if (Finset.univ : Finset (Fin r)) \ P ∈ U then
          (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0)
        else 0 := by
      intro P hP
      have hcardP : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcardP
      let all4 : Finset (Finset (Fin r) × Finset (Fin r)) :=
        {({a, b}, ∅), ({a}, {b}), ({b}, {a}), (∅, {a, b})}
      have hsub4 : faces.filter (fun p => p.1 ∪ p.2 = {a, b}) ⊆ all4 := by
        intro ⟨B, F⟩ hBF
        obtain ⟨hBF1, hun⟩ := Finset.mem_filter.mp hBF
        have ⟨hd, _⟩ := (Finset.mem_filter.mp hBF1).2
        have hF : F = {a, b} \ B := by
          rw [← hun, Finset.union_sdiff_cancel_left hd]
        have hBsub : B ⊆ {a, b} := hun ▸ Finset.subset_union_left
        have hcases : B = ∅ ∨ B = {a} ∨ B = {b} ∨ B = {a, b} := by
          by_cases ha : a ∈ B <;> by_cases hb : b ∈ B
          · right; right; right; ext x; constructor
            · exact fun hx => hBsub hx
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          · right; left; ext x; constructor
            · intro hx; have := hBsub hx; simp at this; rcases this with rfl | rfl; simp; exact absurd hx hb
            · intro hx; simp at hx; subst hx; exact ha
          · right; right; left; ext x; constructor
            · intro hx; have := hBsub hx; simp at this; rcases this with rfl | rfl; exact absurd hx ha; simp
            · intro hx; simp at hx; subst hx; exact hb
          · left; ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
            have := hBsub hx; simp at this; rcases this with rfl | rfl <;> contradiction
        rcases hcases with rfl | rfl | rfl | rfl
        · have : F = {a, b} := by simpa using hF
          subst this; simp [all4]
        · have : F = {b} := by
            rw [hF]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hne⟩; exact absurd rfl hne; rfl
            · rintro rfl; exact ⟨Or.inr rfl, hab.symm⟩
          subst this; simp [all4]
        · have : F = {a} := by
            rw [hF]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hne⟩; rfl; exact absurd rfl hne
            · rintro rfl; exact ⟨Or.inl rfl, hab⟩
          subst this; simp [all4]
        · have : F = ∅ := by rw [hF]; simp
          subst this; simp [all4]
      have heq_flt : faces.filter (fun p => p.1 ∪ p.2 = {a, b}) = all4.filter (fun p => isFace U p.1 p.2) := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_filter.mpr ⟨hsub4 hp, (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2⟩
        · intro hp
          obtain ⟨hp4, hfc⟩ := Finset.mem_filter.mp hp
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc⟩, ?_⟩
          simp only [all4, Finset.mem_insert, Finset.mem_singleton] at hp4
          rcases hp4 with rfl | rfl | rfl | rfl
          · simp
          · ext x; simp
          · ext x; simp [or_comm]
          · simp
      rw [heq_flt, Finset.sum_filter]
      have hne1 : (({a, b} : Finset (Fin r)), (∅ : Finset (Fin r))) ∉ ({({a}, {b}), ({b}, {a}), (∅, {a, b})} : Finset _) := by
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Finset.singleton_ne_empty b h2.symm
        · exact Finset.singleton_ne_empty a h2.symm
        · exact Finset.insert_ne_empty a {b} h2.symm
      have hne2 : (({a} : Finset (Fin r)), ({b} : Finset (Fin r))) ∉ ({({b}, {a}), (∅, {a, b})} : Finset _) := by
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hab (Finset.singleton_injective h1)
        · exact Finset.singleton_ne_empty a h1
      have hne3 : (({b} : Finset (Fin r)), ({a} : Finset (Fin r))) ∉ ({(∅, {a, b})} : Finset _) := by
        intro h
        simp only [Finset.mem_singleton, Prod.mk.injEq] at h
        exact Finset.singleton_ne_empty b h.1
      dsimp only [all4]
      rw [Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_insert hne3, Finset.sum_singleton]
      have hc_ab : ({a, b} : Finset (Fin r)).card = 2 := Finset.card_pair hab
      have hf1 : isFace U {a, b} ∅ ↔ (Finset.univ : Finset (Fin r)) \ {a, b} ∈ U := by
        constructor
        · intro hf; simpa using hf.2 ∅ Finset.Subset.rfl
        · intro h; refine ⟨by simp, fun S hS => ?_⟩
          have : S = ∅ := Finset.subset_empty.mp hS
          subst this; simpa using h
      have hf2 : isFace U {a} {b} ↔ (Finset.univ : Finset (Fin r)) \ {a, b} ∈ U ∧ a ∈ U1 := by
        constructor
        · intro hf
          refine ⟨?_, ?_⟩
          · have := hf.2 {b} Finset.Subset.rfl
            have he : ({a} : Finset (Fin r)) ∪ {b} = {a, b} := by ext x; simp
            rwa [he] at this
          · simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa using hf.2 ∅ (Finset.empty_subset _)
        · rintro ⟨hP', ha⟩
          refine ⟨Finset.disjoint_singleton.mpr hab, fun S hS => ?_⟩
          rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
          · simpa using (Finset.mem_filter.mp ha).2
          · have he : ({a} : Finset (Fin r)) ∪ {b} = {a, b} := by ext x; simp
            rwa [he]
      have hf3 : isFace U {b} {a} ↔ (Finset.univ : Finset (Fin r)) \ {a, b} ∈ U ∧ b ∈ U1 := by
        constructor
        · intro hf
          refine ⟨?_, ?_⟩
          · have := hf.2 {a} Finset.Subset.rfl
            have he : ({b} : Finset (Fin r)) ∪ {a} = {a, b} := by ext x; simp [or_comm]
            rwa [he] at this
          · simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa using hf.2 ∅ (Finset.empty_subset _)
        · rintro ⟨hP', hb⟩
          refine ⟨Finset.disjoint_singleton.mpr hab.symm, fun S hS => ?_⟩
          rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
          · simpa using (Finset.mem_filter.mp hb).2
          · have he : ({b} : Finset (Fin r)) ∪ {a} = {a, b} := by ext x; simp [or_comm]
            rwa [he]
      have hf4 : isFace U ∅ {a, b} ↔
          (Finset.univ : Finset (Fin r)) \ {a, b} ∈ U ∧ a ∈ U1 ∧ b ∈ U1 ∧ (Finset.univ : Finset (Fin r)) ∈ U := by
        constructor
        · intro hf
          refine ⟨by simpa using hf.2 {a, b} Finset.Subset.rfl, ?_, ?_, by simpa using hf.2 ∅ (Finset.empty_subset _)⟩
          · simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa using hf.2 {a} (by simp)
          · simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa using hf.2 {b} (by simp)
        · rintro ⟨hP', ha, hb, hc⟩
          refine ⟨by simp, fun S hS => ?_⟩
          by_cases hsa : a ∈ S <;> by_cases hsb : b ∈ S
          · have hSeq : S = {a, b} := by
              ext x; constructor
              · exact fun hx => hS hx
              · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
            subst hSeq; simpa using hP'
          · have hSeq : S = {a} := by
              ext x; constructor
              · intro hx; have := hS hx; simp at this; rcases this with rfl | rfl; simp; exact absurd hx hsb
              · intro hx; simp at hx; subst hx; exact hsa
            subst hSeq; simpa using (Finset.mem_filter.mp ha).2
          · have hSeq : S = {b} := by
              ext x; constructor
              · intro hx; have := hS hx; simp at this; rcases this with rfl | rfl; exact absurd hx hsa; simp
              · intro hx; simp at hx; subst hx; exact hsb
            subst hSeq; simpa using (Finset.mem_filter.mp hb).2
          · have hSeq : S = ∅ := by
              ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
              have := hS hx; simp at this; rcases this with rfl | rfl <;> contradiction
            subst hSeq; simpa using hc
      simp only [hf1, hf2, hf3, hf4, hc_ab, Finset.card_empty, Finset.card_singleton]
      by_cases hP' : (Finset.univ : Finset (Fin r)) \ {a, b} ∈ U
      · rw [if_pos hP']
        by_cases ha : a ∈ U1 <;> by_cases hb : b ∈ U1
        · have hinter : ({a, b} ∩ U1).card = 2 := by
            have : ({a, b} : Finset (Fin r)) ∩ U1 = {a, b} := by ext x; simp; intro hx; rcases hx with rfl | rfl <;> assumption
            rw [this, hc_ab]
          by_cases hc : (Finset.univ : Finset (Fin r)) ∈ U
          · have hct : center = true := by rw [← hcen]; exact decide_eq_true hc
            simp [hP', ha, hb, hc, hct, hc_ab]
          · have hcf : center = false := by rw [← hcen]; exact decide_eq_false hc
            simp [hP', ha, hb, hc, hcf, hc_ab]
        · have hinter : ({a, b} ∩ U1).card = 1 := by
            have : ({a, b} : Finset (Fin r)) ∩ U1 = {a} := by
              ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, hx⟩; rfl; exact absurd hx hb
              · rintro rfl; exact ⟨Or.inl rfl, ha⟩
            rw [this, Finset.card_singleton]
          simp [hP', ha, hb, hinter]
        · have hinter : ({a, b} ∩ U1).card = 1 := by
            have : ({a, b} : Finset (Fin r)) ∩ U1 = {b} := by
              ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, hx⟩; exact absurd hx ha; rfl
              · rintro rfl; exact ⟨Or.inr rfl, hb⟩
            rw [this, Finset.card_singleton]
          simp [hP', ha, hb, hinter]
        · have hinter : ({a, b} ∩ U1).card = 0 := by
            have : ({a, b} : Finset (Fin r)) ∩ U1 = ∅ := by
              ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
              rintro ⟨rfl | rfl, hx⟩ <;> contradiction
            rw [this, Finset.card_empty]
          simp [hP', ha, hb, hinter]
      · simp [hP']
    rw [Finset.sum_congr rfl hterm2, ← Finset.sum_filter]
  rw [hsum0, hsum1, hsum2, add_assoc]

private lemma card_U1_eq {r : ℕ} (U : Finset (Finset (Fin r))) :
    ((Finset.univ : Finset (Fin r)).filter fun v => (Finset.univ : Finset (Fin r)) \ {v} ∈ U).card =
    (U.filter fun e => ((Finset.univ : Finset (Fin r)) \ e).card = 1).card := by
  refine Finset.card_bij (fun v _ => (Finset.univ : Finset (Fin r)) \ {v}) ?_ ?_ ?_
  · intro v hv
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, ?_⟩
    have : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ {v}) = {v} := by ext x; simp
    rw [this, Finset.card_singleton]
  · intro a _ b _ hab
    have h1 : a ∉ (Finset.univ : Finset (Fin r)) \ {a} := by simp
    rw [hab] at h1
    simpa using h1
  · intro e he
    obtain ⟨heU, hcard⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    have heq : (Finset.univ : Finset (Fin r)) \ {v} = e := by
      rw [← hv]; ext x; simp
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm ▸ heU⟩, heq⟩

private lemma card_U2_eq {r : ℕ} (U : Finset (Finset (Fin r))) :
    (((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (Finset.univ : Finset (Fin r)) \ P ∈ U).card =
    (U.filter fun e => ((Finset.univ : Finset (Fin r)) \ e).card = 2).card := by
  refine Finset.card_bij (fun P _ => (Finset.univ : Finset (Fin r)) \ P) ?_ ?_ ?_
  · intro P hP
    obtain ⟨hP2, hPU⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_filter.mpr ⟨hPU, ?_⟩
    have : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ P) = P := by ext x; simp
    rw [this]
    exact (Finset.mem_powersetCard.mp hP2).2
  · intro P1 _ P2 _ h12
    ext x
    have hx := Finset.ext_iff.mp h12 x
    simpa [not_iff_not] using hx
  · intro e he
    obtain ⟨heU, hcard⟩ := Finset.mem_filter.mp he
    let P := (Finset.univ : Finset (Fin r)) \ e
    have heq : (Finset.univ : Finset (Fin r)) \ P = e := by ext x; simp [P]
    exact ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, heq.symm ▸ heU⟩, heq⟩

private lemma card_mixed_pairs {r : ℕ} (U1 : Finset (Fin r)) :
    (((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (P ∩ U1).card = 1).card =
    ((Finset.univ : Finset (Fin r)) \ U1).card * U1.card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun ab _ => ({ab.1, ab.2} : Finset (Fin r))) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hna : a ∉ U1 := (Finset.mem_sdiff.mp ha).2
    have hne : a ≠ b := fun h => hna (h ▸ hb)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hne⟩, ?_⟩
    have : ({a, b} : Finset (Fin r)) ∩ U1 = {b} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩; exact absurd hx hna; rfl
      · rintro rfl; exact ⟨Or.inr rfl, hb⟩
    rw [this, Finset.card_singleton]
  · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
    obtain ⟨ha1, hb1⟩ := Finset.mem_product.mp h1
    obtain ⟨ha2, hb2⟩ := Finset.mem_product.mp h2
    have hna1 : a1 ∉ U1 := (Finset.mem_sdiff.mp ha1).2
    have hna2 : a2 ∉ U1 := (Finset.mem_sdiff.mp ha2).2
    have ha1_mem : a1 ∈ ({a2, b2} : Finset (Fin r)) := heq ▸ Finset.mem_insert_self a1 {b1}
    have hb1_mem : b1 ∈ ({a2, b2} : Finset (Fin r)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha1_mem hb1_mem
    have ha : a1 = a2 := ha1_mem.resolve_right fun h => hna1 (h ▸ hb2)
    have hb : b1 = b2 := hb1_mem.resolve_left fun h => hna2 (h ▸ hb1)
    exact Prod.ext ha hb
  · intro P hP
    obtain ⟨hP2, hcard1⟩ := Finset.mem_filter.mp hP
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
    have hbU1 : b ∈ U1 := (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b)).2
    have hbP : b ∈ P := (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b)).1
    have hcardP : P.card = 2 := (Finset.mem_powersetCard.mp hP2).2
    have hcard_er : (P.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbP, hcardP]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard_er
    have haP : a ∈ P := Finset.mem_of_mem_erase (ha ▸ Finset.mem_singleton_self a)
    have hab : a ≠ b := Finset.ne_of_mem_erase (ha ▸ Finset.mem_singleton_self a)
    have hna : a ∉ U1 := by
      intro haU1
      have : a ∈ P ∩ U1 := Finset.mem_inter.mpr ⟨haP, haU1⟩
      rw [hb, Finset.mem_singleton] at this
      exact hab this
    refine ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hna⟩, hbU1⟩, ?_⟩
    ext x
    constructor
    · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    · intro hx
      by_cases hxb : x = b
      · subst hxb; simp
      · have : x ∈ P.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
        rw [ha, Finset.mem_singleton] at this
        subst this; simp

private lemma sum_pairs_eq {r : ℕ} (U1 : Finset (Fin r)) (U2 : Finset (Finset (Fin r))) (center : Bool)
    (hsub : U2 ⊆ (Finset.univ : Finset (Fin r)).powersetCard 2) :
    let P0 := U2.filter fun P => (P ∩ U1).card = 0
    let P1 := U2.filter fun P => (P ∩ U1).card = 1
    let P2 := U2.filter fun P => (P ∩ U1).card = 2
    P0.card + P1.card + P2.card = U2.card ∧
    ∑ P ∈ U2, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) =
      36 * P0.card + 90 * P1.card + (144 + 81 * center.toNat) * P2.card := by
  intro P0 P1 P2
  have hle2 : ∀ P ∈ U2, (P ∩ U1).card ≤ 2 := fun P hP =>
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.mem_powersetCard.mp (hsub hP)).2
  have hpart : U2 = P0 ∪ (P1 ∪ P2) := by
    ext P; simp only [P0, P1, P2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hP
      have h := hle2 P hP
      by_cases h0 : (P ∩ U1).card = 0
      · exact Or.inl ⟨hP, h0⟩
      · by_cases h1 : (P ∩ U1).card = 1
        · exact Or.inr (Or.inl ⟨hP, h1⟩)
        · exact Or.inr (Or.inr ⟨hP, by omega⟩)
    · rintro (⟨hP, _⟩ | ⟨hP, _⟩ | ⟨hP, _⟩) <;> exact hP
  have hd0 : Disjoint P0 (P1 ∪ P2) := by
    rw [Finset.disjoint_left]; intro P h0 h12
    simp only [P0, P1, P2, Finset.mem_union, Finset.mem_filter] at h0 h12; omega
  have hd12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro P h1 h2
    simp only [P1, P2, Finset.mem_filter] at h1 h2; omega
  constructor
  · conv_rhs => rw [hpart]
    rw [Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12]; omega
  · conv_lhs => rw [hpart]
    rw [Finset.sum_union hd0, Finset.sum_union hd12]
    have s0 : ∑ P ∈ P0, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) = 36 * P0.card := by
      trans ∑ _P ∈ P0, 36
      · refine Finset.sum_congr rfl fun P hP => ?_; simp [(Finset.mem_filter.mp hP).2]
      · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have s1 : ∑ P ∈ P1, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) = 90 * P1.card := by
      trans ∑ _P ∈ P1, 90
      · refine Finset.sum_congr rfl fun P hP => ?_; simp [(Finset.mem_filter.mp hP).2]
      · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have s2 : ∑ P ∈ P2, (36 + 54 * (P ∩ U1).card + if (P ∩ U1).card = 2 then 81 * center.toNat else 0) =
        (144 + 81 * center.toNat) * P2.card := by
      trans ∑ _P ∈ P2, (144 + 81 * center.toNat)
      · refine Finset.sum_congr rfl fun P hP => ?_; simp [(Finset.mem_filter.mp hP).2]
      · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [s0, s1, s2, add_assoc]

private lemma choose_split (t u : ℕ) :
    Nat.choose (t + u) 2 = Nat.choose t 2 + t * u + Nat.choose u 2 := by
  have h1 : 2 * Nat.choose (t + u) 2 = (t + u) * (t + u - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self (t + u)).two_dvd
  have h2 : 2 * Nat.choose t 2 = t * (t - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self t).two_dvd
  have h3 : 2 * Nat.choose u 2 = u * (u - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self u).two_dvd
  have hmul : 2 * Nat.choose (t + u) 2 = 2 * (Nat.choose t 2 + t * u + Nat.choose u 2) := by
    rw [h1, mul_add, mul_add, h2, h3]
    rcases t with _ | t <;> rcases u with _ | u <;> simp <;> ring
  omega

theorem main : (∀ (r t pairs : Nat) (center : Bool), t ≤ r → pairs ≤ Nat.choose r 2 →
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let units := r - t
  let cheap := Nat.choose t 2
  let mixed := t * units
  let loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  let allowed := fun (U : Finset Kind) =>
    (decide (sites ∈ U) = center) ∧ (∀ e ∈ U, (sites \ e).card ≤ 2) ∧
    (U.filter (fun e => (sites \ e).card = 1)).card = units ∧
    (U.filter (fun e => (sites \ e).card = 2)).card = pairs
  (∀ U : Finset Kind, allowed U → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, allowed U ∧ kernelSize (kinds \ U) = 11 ^ loss) := by
  intro r t pairs center htr hpairs
  dsimp only
  set units := r - t
  set cheap := Nat.choose t 2
  set mixed := t * units
  set loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  constructor
  · intro U ⟨hcen, hle2, hu1, hu2⟩
    change 11 ^ loss ≤ _
    have hkeq := kernelSize_eq_pow_lost U
    unfold passFn at hkeq
    rw [hkeq]
    apply Nat.pow_le_pow_right (by decide : 0 < 11)
    rw [card_lostSet_formula U center hcen hle2]
    set U1 := (Finset.univ : Finset (Fin r)).filter fun v => (Finset.univ : Finset (Fin r)) \ {v} ∈ U
    set U2 := ((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (Finset.univ : Finset (Fin r)) \ P ∈ U
    have hU1_card : U1.card = units := (card_U1_eq U).trans hu1
    have hU2_card : U2.card = pairs := (card_U2_eq U).trans hu2
    obtain ⟨hsum_cnt, hsum_val⟩ := sum_pairs_eq U1 U2 center (Finset.filter_subset _ _)
    rw [hU1_card, hsum_val]
    set P0 := U2.filter fun P => (P ∩ U1).card = 0
    set P1 := U2.filter fun P => (P ∩ U1).card = 1
    set P2 := U2.filter fun P => (P ∩ U1).card = 2
    have hcomp_card : ((Finset.univ : Finset (Fin r)) \ U1).card = t := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hU1_card]
      omega
    have hP0_le : P0.card ≤ cheap := by
      have hsub0 : P0 ⊆ ((Finset.univ : Finset (Fin r)) \ U1).powersetCard 2 := by
        intro P hP
        obtain ⟨hPU2, h0⟩ := Finset.mem_filter.mp hP
        have hP2 := (Finset.mem_filter.mp hPU2).1
        refine Finset.mem_powersetCard.mpr ⟨?_, (Finset.mem_powersetCard.mp hP2).2⟩
        intro x hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxU1 => ?_⟩
        have hne : (P ∩ U1).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hx, hxU1⟩⟩
        exact absurd h0 (Finset.card_pos.mpr hne).ne'
      calc P0.card ≤ (((Finset.univ : Finset (Fin r)) \ U1).powersetCard 2).card := Finset.card_le_card hsub0
        _ = Nat.choose ((Finset.univ : Finset (Fin r)) \ U1).card 2 := Finset.card_powersetCard _ _
        _ = cheap := by rw [hcomp_card]
    have hP1_le : P1.card ≤ mixed := by
      have hsub1 : P1 ⊆ ((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (P ∩ U1).card = 1 := by
        intro P hP
        obtain ⟨hPU2, h1⟩ := Finset.mem_filter.mp hP
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hPU2).1, h1⟩
      calc P1.card ≤ (((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (P ∩ U1).card = 1).card :=
            Finset.card_le_card hsub1
        _ = ((Finset.univ : Finset (Fin r)) \ U1).card * U1.card := card_mixed_pairs U1
        _ = mixed := by rw [hcomp_card, hU1_card]
    have hcnt : P0.card + P1.card + P2.card = pairs := hsum_cnt.trans hU2_card
    cases center <;> simp [loss] at * <;> omega
  · obtain ⟨U1, -, hU1_card⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin r))) (n := units) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hcomp_card : ((Finset.univ : Finset (Fin r)) \ U1).card = t := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hU1_card]
      omega
    let C0 := ((Finset.univ : Finset (Fin r)) \ U1).powersetCard 2
    let C1 := ((Finset.univ : Finset (Fin r)).powersetCard 2).filter fun P => (P ∩ U1).card = 1
    let C2 := U1.powersetCard 2
    have hC0_card : C0.card = cheap := by rw [Finset.card_powersetCard, hcomp_card]
    have hC1_card : C1.card = mixed := by rw [card_mixed_pairs U1, hcomp_card, hU1_card]
    have hC2_card : C2.card = Nat.choose units 2 := by rw [Finset.card_powersetCard, hU1_card]
    have hr_choose : Nat.choose r 2 = cheap + mixed + Nat.choose units 2 := by
      have htu : t + units = r := by omega
      rw [← htu]; exact choose_split t units
    let p0 := min pairs cheap
    let p1 := min (pairs - p0) mixed
    let p2 := pairs - p0 - p1
    have hp0_le : p0 ≤ C0.card := by rw [hC0_card]; exact min_le_right _ _
    have hp1_le : p1 ≤ C1.card := by rw [hC1_card]; exact min_le_right _ _
    have hp2_le : p2 ≤ C2.card := by rw [hC2_card]; simp only [p0, p1, p2]; omega
    obtain ⟨P0, hP0_sub, hP0_card⟩ := Finset.exists_subset_card_eq hp0_le
    obtain ⟨P1, hP1_sub, hP1_card⟩ := Finset.exists_subset_card_eq hp1_le
    obtain ⟨P2, hP2_sub, hP2_card⟩ := Finset.exists_subset_card_eq hp2_le
    have hP0_inter : ∀ P ∈ P0, (P ∩ U1).card = 0 := by
      intro P hP
      have hsub := (Finset.mem_powersetCard.mp (hP0_sub hP)).1
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨hxP, hxU1⟩ := Finset.mem_inter.mp hx
      exact (Finset.mem_sdiff.mp (hsub hxP)).2 hxU1
    have hP1_inter : ∀ P ∈ P1, (P ∩ U1).card = 1 := fun P hP => (Finset.mem_filter.mp (hP1_sub hP)).2
    have hP2_inter : ∀ P ∈ P2, (P ∩ U1).card = 2 := by
      intro P hP
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp (hP2_sub hP)
      have : P ∩ U1 = P := Finset.inter_eq_left.mpr hsub
      rw [this, hcard]
    have hP0_c2 : ∀ P ∈ P0, P.card = 2 := fun P hP => (Finset.mem_powersetCard.mp (hP0_sub hP)).2
    have hP1_c2 : ∀ P ∈ P1, P.card = 2 := fun P hP => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hP1_sub hP)).1).2
    have hP2_c2 : ∀ P ∈ P2, P.card = 2 := fun P hP => (Finset.mem_powersetCard.mp (hP2_sub hP)).2
    have hd0 : Disjoint P0 (P1 ∪ P2) := by
      rw [Finset.disjoint_left]; intro P h0 h12
      have c0 := hP0_inter P h0
      rcases Finset.mem_union.mp h12 with h1 | h2
      · have c1 := hP1_inter P h1; omega
      · have c2 := hP2_inter P h2; omega
    have hd12 : Disjoint P1 P2 := by
      rw [Finset.disjoint_left]; intro P h1 h2
      have c1 := hP1_inter P h1
      have c2 := hP2_inter P h2; omega
    let U2 := P0 ∪ (P1 ∪ P2)
    have hU2_sub : U2 ⊆ (Finset.univ : Finset (Fin r)).powersetCard 2 := by
      intro P hP
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rcases Finset.mem_union.mp hP with h0 | h12
      · exact hP0_c2 P h0
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · exact hP1_c2 P h1
        · exact hP2_c2 P h2
    have hU2_card : U2.card = pairs := by
      simp only [U2]
      rw [Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12, hP0_card, hP1_card, hP2_card]
      simp only [p0, p1, p2]; omega
    let U0 : Finset (Finset (Fin r)) := if center then {Finset.univ} else ∅
    let U : Finset (Finset (Fin r)) :=
      U0 ∪ (U1.image (fun v => (Finset.univ : Finset (Fin r)) \ {v}) ∪
        U2.image (fun P => (Finset.univ : Finset (Fin r)) \ P))
    have hU_cen_iff : (Finset.univ : Finset (Fin r)) ∈ U ↔ center = true := by
      simp only [U, U0, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (h0 | ⟨v, _, hv⟩ | ⟨P, hP, hPeq⟩)
        · cases center <;> simp at h0 ⊢
        · have : v ∈ (Finset.univ : Finset (Fin r)) \ {v} := hv.symm ▸ Finset.mem_univ v
          simp at this
        · have hcard := (Finset.mem_powersetCard.mp (hU2_sub hP)).2
          have hne : P.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨v, hv⟩ := hne
          have : v ∈ (Finset.univ : Finset (Fin r)) \ P := hPeq.symm ▸ Finset.mem_univ v
          exact absurd hv (Finset.mem_sdiff.mp this).2
      · intro hc; left; simp [hc]
    have hcen : decide ((Finset.univ : Finset (Fin r)) ∈ U) = center := by
      cases center
      · exact decide_eq_false (by rw [hU_cen_iff]; decide)
      · exact decide_eq_true (by rw [hU_cen_iff])
    have hle2 : ∀ e ∈ U, ((Finset.univ : Finset (Fin r)) \ e).card ≤ 2 := by
      intro e he
      simp only [U, U0, Finset.mem_union, Finset.mem_image] at he
      rcases he with h0 | ⟨v, _, rfl⟩ | ⟨P, hP, rfl⟩
      · cases center <;> simp at h0
        subst h0; simp
      · have : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ {v}) = {v} := by ext x; simp
        rw [this, Finset.card_singleton]; omega
      · have : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ P) = P := by ext x; simp
        rw [this, (Finset.mem_powersetCard.mp (hU2_sub hP)).2]
    have hU1_eq : (Finset.univ : Finset (Fin r)).filter (fun v => (Finset.univ : Finset (Fin r)) \ {v} ∈ U) = U1 := by
      ext v
      simp only [U, U0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (h0 | ⟨w, hw, heq⟩ | ⟨P, hP, heq⟩)
        · cases center <;> simp at h0
        · have : v = w := by
            have h1 : v ∉ (Finset.univ : Finset (Fin r)) \ {v} := by simp
            rw [← heq] at h1; simpa using h1
          rwa [this]
        · have h1 : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ P) =
              (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ {v}) := by rw [heq]
          have h2 : P = {v} := by
            ext x; have hx := Finset.ext_iff.mp h1 x; simpa using hx
          have hc := (Finset.mem_powersetCard.mp (hU2_sub hP)).2
          rw [h2, Finset.card_singleton] at hc; omega
      · intro hv; right; left; exact ⟨v, hv, rfl⟩
    have hU2_eq : ((Finset.univ : Finset (Fin r)).powersetCard 2).filter
        (fun P => (Finset.univ : Finset (Fin r)) \ P ∈ U) = U2 := by
      ext P
      simp only [U, U0, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hP2, h0 | ⟨w, _, heq⟩ | ⟨Q, hQ, heq⟩⟩
        · cases center <;> simp at h0
          have hc := (Finset.mem_powersetCard.mp hP2).2
          obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
          exact False.elim (Finset.disjoint_left.mp h0 (Finset.mem_univ v) hv)
        · have h1 : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ {w}) =
              (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ P) := by rw [heq]
          have h2 : P = {w} := by
            ext x; have hx := Finset.ext_iff.mp h1 x; simpa [eq_comm] using hx.symm
          have hc := (Finset.mem_powersetCard.mp hP2).2
          rw [h2, Finset.card_singleton] at hc; omega
        · have h1 : (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ Q) =
              (Finset.univ : Finset (Fin r)) \ ((Finset.univ : Finset (Fin r)) \ P) := by rw [heq]
          have h2 : P = Q := by
            ext x; have hx := Finset.ext_iff.mp h1 x; simpa using hx.symm
          rwa [h2]
      · intro hP; exact ⟨hU2_sub hP, Or.inr (Or.inr ⟨P, hP, rfl⟩)⟩
    have hu1 : (U.filter fun e => ((Finset.univ : Finset (Fin r)) \ e).card = 1).card = units := by
      rw [← card_U1_eq U, hU1_eq, hU1_card]
    have hu2 : (U.filter fun e => ((Finset.univ : Finset (Fin r)) \ e).card = 2).card = pairs := by
      rw [← card_U2_eq U, hU2_eq, hU2_card]
    refine ⟨U, ⟨hcen, hle2, hu1, hu2⟩, ?_⟩
    change _ = 11 ^ loss
    have hkeq := kernelSize_eq_pow_lost U
    unfold passFn at hkeq
    rw [hkeq]
    congr 1
    rw [card_lostSet_formula U center hcen hle2, hU1_eq, hU2_eq, hU1_card]
    obtain ⟨_, hsum_val⟩ := sum_pairs_eq U1 U2 center hU2_sub
    rw [hsum_val]
    have hflt0 : U2.filter (fun P => (P ∩ U1).card = 0) = P0 := by
      ext P; simp only [U2, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h0 | h1 | h2, hc⟩
        · exact h0
        · have := hP1_inter P h1; omega
        · have := hP2_inter P h2; omega
      · intro h0; exact ⟨Or.inl h0, hP0_inter P h0⟩
    have hflt1 : U2.filter (fun P => (P ∩ U1).card = 1) = P1 := by
      ext P; simp only [U2, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h0 | h1 | h2, hc⟩
        · have := hP0_inter P h0; omega
        · exact h1
        · have := hP2_inter P h2; omega
      · intro h1; exact ⟨Or.inr (Or.inl h1), hP1_inter P h1⟩
    have hflt2 : U2.filter (fun P => (P ∩ U1).card = 2) = P2 := by
      ext P; simp only [U2, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h0 | h1 | h2, hc⟩
        · have := hP0_inter P h0; omega
        · have := hP1_inter P h1; omega
        · exact h2
      · intro h2; exact ⟨Or.inr (Or.inr h2), hP2_inter P h2⟩
    rw [hflt0, hflt1, hflt2, hP0_card, hP1_card, hP2_card]
    cases center <;> simp only [p0, p1, p2, loss, Bool.toNat_false, Bool.toNat_true] <;> omega

end PEqualNP.Outside.L_lib_1167

theorem PEqualNP.Outside.L_lib_1167 : (∀ (r t pairs : Nat) (center : Bool), t ≤ r → pairs ≤ Nat.choose r 2 →
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let units := r - t
  let cheap := Nat.choose t 2
  let mixed := t * units
  let loss := center.toNat + (6 + 9 * center.toNat) * units + 36 * pairs +
    54 * (pairs - cheap) + (54 + 81 * center.toNat) * (pairs - (cheap + mixed))
  let allowed := fun (U : Finset Kind) =>
    (decide (sites ∈ U) = center) ∧ (∀ e ∈ U, (sites \ e).card ≤ 2) ∧
    (U.filter (fun e => (sites \ e).card = 1)).card = units ∧
    (U.filter (fun e => (sites \ e).card = 2)).card = pairs
  (∀ U : Finset Kind, allowed U → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, allowed U ∧ kernelSize (kinds \ U) = 11 ^ loss) :=
  PEqualNP.Outside.L_lib_1167.main
