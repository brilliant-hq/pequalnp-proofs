import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25688_aux

private def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [zmod2_add_self, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact zmod2_add_self a

private lemma toZ2_xor (a b : Bool) : toZ2 (xor a b) = toZ2 a + toZ2 b := by
  cases a <;> cases b <;> decide

private lemma toZ2_and (a b : Bool) : toZ2 (a && b) = toZ2 a * toZ2 b := by
  cases a <;> cases b <;> decide

private lemma toZ2_not (a : Bool) : toZ2 (!a) = 1 + toZ2 a := by
  cases a <;> decide

private lemma toZ2_eq_zero_iff (b : Bool) : toZ2 b = 0 ↔ b = false := by
  cases b <;> decide

private lemma toZ2_eq_one_iff (b : Bool) : toZ2 b = 1 ↔ b = true := by
  cases b <;> decide

private lemma toZ2_injective : Function.Injective toZ2 := by
  intro a b h
  cases a <;> cases b <;> simp [toZ2] at h ⊢

private lemma toZ2_eq_iff (a b : Bool) : toZ2 a = toZ2 b ↔ a = b :=
  ⟨fun h => toZ2_injective h, congrArg toZ2⟩

private lemma toZ2_nat_parity (n : ℕ) : toZ2 (n % 2 == 1) = (n : ZMod 2) := by
  have hmod : (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  rw [hmod]
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  interval_cases (n % 2) <;> decide

private def monEval {ι : Type*} (mon : Finset ι) (x : ι → Bool) : ZMod 2 :=
  if ∀ a ∈ mon, x a = true then 1 else 0

private lemma monEval_empty {ι : Type*} (x : ι → Bool) : monEval (∅ : Finset ι) x = 1 := by
  simp [monEval]

private lemma monEval_singleton {ι : Type*} (a : ι) (x : ι → Bool) :
    monEval ({a} : Finset ι) x = toZ2 (x a) := by
  simp only [monEval, Finset.mem_singleton, forall_eq, toZ2]

private lemma monEval_union {ι : Type*} [DecidableEq ι] (s t : Finset ι) (x : ι → Bool) :
    monEval s x * monEval t x = monEval (s ∪ t) x := by
  unfold monEval
  by_cases hs : ∀ a ∈ s, x a = true <;> by_cases ht : ∀ a ∈ t, x a = true
  · have hst : ∀ a ∈ s ∪ t, x a = true := by
      intro a ha
      rcases Finset.mem_union.mp ha with h1 | h2
      · exact hs a h1
      · exact ht a h2
    have hp1 : (∀ a ∈ s, x a = true) ↔ True := iff_true_intro hs
    have hp2 : (∀ a ∈ t, x a = true) ↔ True := iff_true_intro ht
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ True := iff_true_intro hst
    simp only [hp1, hp2, hp3, ↓reduceIte, mul_one]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => ht (fun a ha => h a (Finset.mem_union_right s ha))
    have hp2 : (∀ a ∈ t, x a = true) ↔ False := iff_false_intro ht
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp2, hp3, ↓reduceIte, mul_zero]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => hs (fun a ha => h a (Finset.mem_union_left t ha))
    have hp1 : (∀ a ∈ s, x a = true) ↔ False := iff_false_intro hs
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp1, hp3, ↓reduceIte, zero_mul]
  · have hnst : ¬ ∀ a ∈ s ∪ t, x a = true := fun h => hs (fun a ha => h a (Finset.mem_union_left t ha))
    have hp1 : (∀ a ∈ s, x a = true) ↔ False := iff_false_intro hs
    have hp3 : (∀ a ∈ s ∪ t, x a = true) ↔ False := iff_false_intro hnst
    simp only [hp1, hp3, ↓reduceIte, zero_mul]

private lemma monEval_eq_prod {ι : Type*} [DecidableEq ι] (mon : Finset ι) (x : ι → Bool) :
    monEval mon x = ∏ a ∈ mon, toZ2 (x a) := by
  induction mon using Finset.induction_on with
  | empty => simp [monEval]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← monEval_singleton, monEval_union, Finset.singleton_union]

private def polyEval {ι : Type*} [Fintype ι] (c : Finset ι → ZMod 2) (x : ι → Bool) : ZMod 2 :=
  ∑ mon : Finset ι, c mon * monEval mon x

private lemma polyEval_add {ι : Type*} [Fintype ι] (c1 c2 : Finset ι → ZMod 2) (x : ι → Bool) :
    polyEval (fun s => c1 s + c2 s) x = polyEval c1 x + polyEval c2 x := by
  unfold polyEval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => by ring

private lemma polyEval_injective (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Injective (polyEval (ι := ι)) := by
  intro c1 c2 heq
  have hzero : ∀ c : Finset ι → ZMod 2, (∀ x, polyEval c x = 0) → ∀ mon, c mon = 0 := by
    intro c hc
    have hstrong : ∀ n : ℕ, ∀ mon : Finset ι, mon.card = n → c mon = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro mon hcard
        let xmon : ι → Bool := fun v => decide (v ∈ mon)
        have hx := hc xmon
        unfold polyEval at hx
        rw [Finset.sum_eq_single mon] at hx
        · have h1 : monEval mon xmon = 1 := by
            have hall : ∀ a ∈ mon, xmon a = true := fun a ha => decide_eq_true ha
            have hp : (∀ a ∈ mon, xmon a = true) ↔ True := iff_true_intro hall
            simp only [monEval, hp, ↓reduceIte]
          simpa [h1] using hx
        · intro s _ hsne
          by_cases hsub : s ⊆ mon
          · have hssub : s ⊂ mon := ssubset_iff_subset_ne.mpr ⟨hsub, hsne⟩
            have hlt : s.card < n := hcard ▸ Finset.card_lt_card hssub
            rw [ih s.card hlt s rfl, zero_mul]
          · have hnot : ¬ ∀ a ∈ s, xmon a = true := by
              intro hall; apply hsub; intro a ha; exact of_decide_eq_true (hall a ha)
            have hp : (∀ a ∈ s, xmon a = true) ↔ False := iff_false_intro hnot
            simp only [monEval, hp, ↓reduceIte, mul_zero]
        · intro hnot; exact absurd (Finset.mem_univ mon) hnot
    intro mon
    exact hstrong mon.card mon rfl
  have hdiff : ∀ x, polyEval (fun s => c1 s + c2 s) x = 0 := by
    intro x
    rw [polyEval_add, congrFun heq x, zmod2_add_self]
  funext mon
  exact (zmod2_add_eq_zero_iff (c1 mon) (c2 mon)).mp (hzero _ hdiff mon)

private lemma polyEval_surjective (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (polyEval (ι := ι)) := by
  have hbij : Function.Bijective (polyEval (ι := ι)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨polyEval_injective ι, ?_⟩
    simp [Fintype.card_finset, ZMod.card]
  exact hbij.2

private def HasDeg {ι : Type*} [Fintype ι] (u : ℕ) (f : (ι → Bool) → ZMod 2) : Prop :=
  ∃ c : Finset ι → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ u) ∧ ∀ x, f x = polyEval c x

private lemma hasDeg_mono {ι : Type*} [Fintype ι] {u v : ℕ} (huv : u ≤ v)
    {f : (ι → Bool) → ZMod 2} (hf : HasDeg u f) : HasDeg v f := by
  rcases hf with ⟨c, hdeg, heval⟩
  exact ⟨c, fun mon hne => le_trans (hdeg mon hne) huv, heval⟩

private lemma hasDeg_const {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ZMod 2) :
    HasDeg (ι := ι) 0 (fun _ => a) := by
  refine ⟨fun s => if s = ∅ then a else 0, ?_, fun x => ?_⟩
  · intro mon hne
    by_cases h : mon = ∅
    · subst h; simp
    · simp [h] at hne
  · unfold polyEval
    rw [Finset.sum_eq_single ∅]
    · simp [monEval_empty]
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ ∅) hnot

private lemma hasDeg_var {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    HasDeg (ι := ι) 1 (fun x => toZ2 (x a)) := by
  refine ⟨fun s => if s = {a} then 1 else 0, ?_, fun x => ?_⟩
  · intro mon hne
    by_cases h : mon = {a}
    · subst h; simp
    · simp [h] at hne
  · unfold polyEval
    rw [Finset.sum_eq_single {a}]
    · simp [monEval_singleton]
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ {a}) hnot

private lemma hasDeg_monEval {ι : Type*} [Fintype ι] [DecidableEq ι] (mon : Finset ι) :
    HasDeg mon.card (fun x => monEval mon x) := by
  refine ⟨fun s => if s = mon then 1 else 0, ?_, fun x => ?_⟩
  · intro s hne
    by_cases h : s = mon
    · subst h; exact le_rfl
    · simp [h] at hne
  · unfold polyEval
    rw [Finset.sum_eq_single mon]
    · simp
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ mon) hnot

private lemma hasDeg_add {ι : Type*} [Fintype ι] {u : ℕ} {f g : (ι → Bool) → ZMod 2}
    (hf : HasDeg u f) (hg : HasDeg u g) : HasDeg u (fun x => f x + g x) := by
  rcases hf with ⟨cf, hdf, hef⟩
  rcases hg with ⟨cg, hdg, heg⟩
  refine ⟨fun s => cf s + cg s, ?_, fun x => ?_⟩
  · intro mon hne
    dsimp only at hne
    by_cases h1 : cf mon = 0
    · rw [h1, zero_add] at hne; exact hdg mon hne
    · exact hdf mon h1
  · dsimp only
    rw [polyEval_add, hef x, heg x]

private lemma hasDeg_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] {u : ℕ} (s : Finset α)
    (f : α → (ι → Bool) → ZMod 2) (hf : ∀ i ∈ s, HasDeg u (f i)) :
    HasDeg u (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasDeg_mono (Nat.zero_le u) (hasDeg_const (ι := ι) 0)
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => ∑ i ∈ insert a s, f i x) = (fun x => f a x + ∑ i ∈ s, f i x) := by
      funext x; exact Finset.sum_insert ha
    rw [heq]
    exact hasDeg_add h1 h2

private lemma hasDeg_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : ℕ}
    {f g : (ι → Bool) → ZMod 2} (hf : HasDeg u f) (hg : HasDeg v g) :
    HasDeg (u + v) (fun x => f x * g x) := by
  rcases hf with ⟨cf, hdf, hef⟩
  rcases hg with ⟨cg, hdg, heg⟩
  let c : Finset ι → ZMod 2 := fun m =>
    ∑ s : Finset ι, ∑ t : Finset ι, if s ∪ t = m then cf s * cg t else 0
  refine ⟨c, ?_, fun x => ?_⟩
  · intro m hne
    have hex : ∃ s t : Finset ι, s ∪ t = m ∧ cf s * cg t ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hne
      dsimp only [c]
      refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
      split_ifs with hst
      · exact hall s t hst
      · rfl
    rcases hex with ⟨s, t, rfl, hst⟩
    have h1 : cf s ≠ 0 := left_ne_zero_of_mul hst
    have h2 : cg t ≠ 0 := right_ne_zero_of_mul hst
    calc (s ∪ t).card ≤ s.card + t.card := Finset.card_union_le s t
      _ ≤ u + v := Nat.add_le_add (hdf s h1) (hdg t h2)
  · dsimp only
    rw [hef x, heg x]
    unfold polyEval
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have h1 : (∑ s : Finset ι, ∑ t : Finset ι, cf s * monEval s x * (cg t * monEval t x)) =
        ∑ s : Finset ι, ∑ t : Finset ι, (cf s * cg t) * monEval (s ∪ t) x := by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [← monEval_union s t x]; ring
    rw [h1]
    have h2 : (∑ m : Finset ι, c m * monEval m x) =
        ∑ s : Finset ι, ∑ t : Finset ι, ∑ m : Finset ι,
          (if s ∪ t = m then cf s * cg t else 0) * monEval m x := by
      dsimp only [c]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_comm
    rw [h2]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single (s ∪ t)]
    · simp
    · intro m _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd (Finset.mem_univ (s ∪ t)) hnot

private lemma hasDeg_prod {ι α : Type*} [Fintype ι] [DecidableEq ι] (s : Finset α)
    (u : α → ℕ) (f : α → (ι → Bool) → ZMod 2) (hf : ∀ i ∈ s, HasDeg (u i) (f i)) :
    HasDeg (∑ i ∈ s, u i) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDeg_const (ι := ι) 1
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => ∏ i ∈ insert a s, f i x) = (fun x => f a x * ∏ i ∈ s, f i x) := by
      funext x; exact Finset.prod_insert ha
    rw [heq]
    exact hasDeg_mul h1 h2

private lemma hasDeg_comp_affine {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {u : ℕ}
    (φ : (ι' → Bool) → (ι → Bool))
    (hφ : ∀ a : ι, HasDeg 1 (fun y => toZ2 (φ y a)))
    {f : (ι → Bool) → ZMod 2} (hf : HasDeg u f) :
    HasDeg u (fun y => f (φ y)) := by
  rcases hf with ⟨c, hdeg, heval⟩
  have heq : (fun y => f (φ y)) = (fun y => ∑ mon : Finset ι, (fun y => c mon * monEval mon (φ y)) y) := by
    funext y; exact heval (φ y)
  rw [heq]
  refine hasDeg_sum Finset.univ (fun mon y => c mon * monEval mon (φ y)) fun mon _ => ?_
  by_cases hc0 : c mon = 0
  · simp only [hc0, zero_mul]
    exact hasDeg_mono (Nat.zero_le u) (hasDeg_const 0)
  · have hm : HasDeg mon.card (fun y => monEval mon (φ y)) := by
      have hpr : (fun y => monEval mon (φ y)) = (fun y => ∏ a ∈ mon, toZ2 (φ y a)) := by
        funext y; exact monEval_eq_prod mon (φ y)
      rw [hpr]
      have hcard : (∑ _a ∈ mon, (1 : ℕ)) = mon.card := by simp
      rw [← hcard]
      exact hasDeg_prod mon (fun _ => 1) (fun a y => toZ2 (φ y a)) (fun a _ => hφ a)
    have hmul : HasDeg (0 + mon.card) (fun y => c mon * monEval mon (φ y)) :=
      hasDeg_mul (hasDeg_const (c mon)) hm
    rw [zero_add] at hmul
    exact hasDeg_mono (hdeg mon hc0) hmul

private lemma hasDeg_coeff_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {u : ℕ}
    {c : Finset ι → ZMod 2} (h : HasDeg u (polyEval c)) {mon : Finset ι} (hlt : u < mon.card) :
    c mon = 0 := by
  rcases h with ⟨c', hd', heq⟩
  have hceq : c = c' := polyEval_injective ι (funext heq)
  rw [hceq]
  by_contra hne
  have hle := hd' mon hne
  omega

private def bitsToNat (m : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range m).foldl (fun acc j => acc ||| ((f j).toNat <<< j)) 0

private lemma testBit_bitsToNat (m : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (bitsToNat m f).testBit i = if i < m then f i else false := by
  induction m with
  | zero => simp [bitsToNat]
  | succ m ih =>
    unfold bitsToNat at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have h1 : i < m + 1 := by omega
      have h2 : ¬ m ≤ i := by omega
      simp [him, h1, h2]
    · by_cases heq : i = m
      · subst heq
        simp only [lt_irrefl, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one, le_refl,
          decide_true, Bool.true_and, Nat.sub_self, Bool.false_or]
        cases f i <;> decide
      · have h1 : ¬ i < m + 1 := by omega
        have h2 : m ≤ i := by omega
        have hpos : 1 ≤ i - m := by omega
        have hzero : (f m).toNat.testBit (i - m) = false := by
          apply Nat.testBit_lt_two_pow
          have hlt2 : (f m).toNat < 2 := by cases f m <;> decide
          have hpow : 2 ≤ 2 ^ (i - m) := by
            calc 2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ (i - m) := Nat.pow_le_pow_right (by omega) hpos
          omega
        simp [him, h1, h2, hzero]

private lemma lt_two_pow_of_testBit_false {x m : ℕ} (h : ∀ i, m ≤ i → x.testBit i = false) :
    x < 2 ^ m := by
  have heq : x = x % 2 ^ m := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < m
    · simp [hi]
    · simp only [hi, decide_false, Bool.false_and]
      exact h i (by omega)
  rw [heq]
  exact Nat.mod_lt x (by positivity)

private lemma bitsToNat_lt (m : ℕ) (f : ℕ → Bool) : bitsToNat m f < 2 ^ m := by
  apply lt_two_pow_of_testBit_false
  intro i hi
  rw [testBit_bitsToNat]
  have hnot : ¬ i < m := by omega
  simp [hnot]

private def keyBitsEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) where
  toFun := fun q i => q.val.testBit i.val
  invFun := fun f => ⟨bitsToNat k (fun i => if h : i < k then f ⟨i, h⟩ else false), bitsToNat_lt k _⟩
  left_inv := fun q => by
    ext
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_bitsToNat]
    by_cases hi : i < k
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le q.isLt hpow)).symm
  right_inv := fun f => by
    funext i
    simp [testBit_bitsToNat, i.isLt]

private lemma deg_iff_hasDeg (k u : ℕ) (f : Fin (2 ^ k) → Bool) :
    (∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ key : Fin (2 ^ k), f key =
        (((terms.filter (fun mon => ∀ j ∈ mon, key.val.testBit j.val = true)).card % 2) == 1)) ↔
    HasDeg u (fun x : Fin k → Bool => toZ2 (f ((keyBitsEquiv k).symm x))) := by
  classical
  constructor
  · rintro ⟨terms, hdeg, heval⟩
    refine ⟨fun mon => if mon ∈ terms then 1 else 0, ?_, fun x => ?_⟩
    · intro mon hne
      by_cases hm : mon ∈ terms
      · exact hdeg mon hm
      · simp [hm] at hne
    · dsimp only
      rw [heval ((keyBitsEquiv k).symm x), toZ2_nat_parity]
      have hbit : ∀ j : Fin k, ((keyBitsEquiv k).symm x).val.testBit j.val = x j := fun j =>
        congrFun ((keyBitsEquiv k).right_inv x) j
      simp_rw [hbit]
      unfold polyEval
      have hsum : (∑ mon : Finset (Fin k), (if mon ∈ terms then (1 : ZMod 2) else 0) * monEval mon x) =
          ∑ mon ∈ terms, monEval mon x := by
        rw [← Finset.sum_subset (Finset.subset_univ terms)]
        · refine Finset.sum_congr rfl fun mon hm => by simp [hm]
        · intro mon _ hm; simp [hm]
      rw [hsum, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun mon _ => ?_
      unfold monEval
      split_ifs <;> simp
  · rintro ⟨c, hdeg, heval⟩
    let terms : Finset (Finset (Fin k)) := Finset.univ.filter (fun mon => c mon = 1)
    refine ⟨terms, fun mon hm => hdeg mon (by rw [(Finset.mem_filter.mp hm).2]; decide), fun key => ?_⟩
    apply toZ2_injective
    have hx := heval (keyBitsEquiv k key)
    dsimp only at hx
    rw [(keyBitsEquiv k).symm_apply_apply key] at hx
    rw [hx, toZ2_nat_parity]
    unfold polyEval
    have hsum : (∑ mon : Finset (Fin k), c mon * monEval mon (keyBitsEquiv k key)) =
        ∑ mon ∈ terms, monEval mon (keyBitsEquiv k key) := by
      rw [← Finset.sum_subset (Finset.subset_univ terms)]
      · refine Finset.sum_congr rfl fun mon hm => by
          rw [(Finset.mem_filter.mp hm).2, one_mul]
      · intro mon _ hm
        have hc0 : c mon = 0 := by
          rcases zmod2_eq_zero_or_one (c mon) with h0 | h1
          · exact h0
          · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ mon, h1⟩) hm
        rw [hc0, zero_mul]
    rw [hsum, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun mon _ => ?_
    unfold monEval
    by_cases h1 : ∀ a ∈ mon, (keyBitsEquiv k key) a = true
    · have h1' : ∀ j ∈ mon, key.val.testBit j.val = true := h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1'), Nat.cast_one]
    · have h1' : ¬ ∀ j ∈ mon, key.val.testBit j.val = true := h1
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1'), Nat.cast_zero]

private def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

private def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

private def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k)) ((constant round).val.testBit (pos % k))

private def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

private lemma rotFn_lt (k s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

private lemma stepFn_lt (k word : ℕ) : stepFn k word < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro i hi
  have h := testBit_bitsToNat k (fun cell => xor (word.testBit cell)
    (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))) i
  have hnot : ¬ i < k := by omega
  simpa [stepFn, bitsToNat, hnot] using h

private lemma testBit_stepFn {k word i : ℕ} (hi : i < k) :
    (stepFn k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  have h := testBit_bitsToNat k (fun cell => xor (word.testBit cell)
    (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))) i
  simpa [stepFn, bitsToNat, hi] using h

private lemma testBit_rotFn {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  set a := s % k
  have ha : a < k := Nat.mod_lt s hk
  by_cases hia : i < a
  · have hge : ¬ a ≤ i := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.false_or]
    have hidx : (i + k - a) % k = k - a + i := by
      have h1 : k - a + i < k := by omega
      have h2 : i + k - a = k - a + i := by omega
      rw [h2, Nat.mod_eq_of_lt h1]
    rw [hidx]
  · have hge : a ≤ i := by omega
    simp only [hge, decide_true, Bool.true_and]
    have hbig : 2 ^ k ≤ 2 ^ (k - a + i) := Nat.pow_le_pow_right (by omega) (by omega)
    have hfalse : word.testBit (k - a + i) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hbig)
    rw [hfalse, Bool.or_false]
    have hidx : (i + k - a) % k = i - a := by
      have h1 : i + k - a = (i - a) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hidx]

private lemma stateFn_lt {k : ℕ} (constant : ℕ → Fin (2 ^ k)) {row key : ℕ}
    (hrow : row < 2 ^ k) (rounds : ℕ) :
    stateFn k constant row rounds key < 2 ^ k := by
  induction rounds with
  | zero =>
    unfold stateFn
    exact Nat.xor_lt_two_pow (rotFn_lt k 1 key) hrow
  | succ r ih =>
    unfold stateFn at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k _ _)) (constant (r + 1)).isLt

private lemma mod_sub_one {k q : ℕ} (hk : 2 ≤ k) (hq : 1 ≤ q) :
    ((q % k) + k - 1 % k) % k = (q - 1) % k := by
  rw [Nat.mod_eq_of_lt (show 1 < k by omega)]
  have hlt : q % k < k := Nat.mod_lt q (by omega)
  have hdiv := Nat.div_add_mod q k
  by_cases h0 : q % k = 0
  · have hqdiv : 1 ≤ q / k := by
      by_cases hz : q / k = 0
      · rw [hz, mul_zero, zero_add] at hdiv; omega
      · exact Nat.pos_of_ne_zero hz
    have heq : q - 1 = k * (q / k - 1) + (k - 1) := by
      have h1 : k * (q / k) = k * (q / k - 1) + k := by
        have : q / k = (q / k - 1) + 1 := by omega
        conv_lhs => rw [this, mul_add, mul_one]
      omega
    rw [h0, zero_add, heq, Nat.mul_add_mod]
  · have heq1 : q % k + k - 1 = (q % k - 1) + k := by omega
    have heq2 : q - 1 = k * (q / k) + (q % k - 1) := by omega
    rw [heq1, Nat.add_mod_right, heq2, Nat.mul_add_mod]

private lemma mod_sub_two {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    ((q % k) + k - 2 % k) % k = (q - 2) % k := by
  rw [Nat.mod_eq_of_lt (show 2 < k by omega)]
  have hlt : q % k < k := Nat.mod_lt q (by omega)
  have hdiv := Nat.div_add_mod q k
  by_cases hge : 2 ≤ q % k
  · have heq1 : q % k + k - 2 = (q % k - 2) + k := by omega
    have heq2 : q - 2 = k * (q / k) + (q % k - 2) := by omega
    rw [heq1, Nat.add_mod_right, heq2, Nat.mul_add_mod]
  · have hqdiv : 1 ≤ q / k := by
      by_cases hz : q / k = 0
      · rw [hz, mul_zero, zero_add] at hdiv; omega
      · exact Nat.pos_of_ne_zero hz
    have heq2 : q - 2 = k * (q / k - 1) + (q % k + k - 2) := by
      have h1 : k * (q / k) = k * (q / k - 1) + k := by
        have : q / k = (q / k - 1) + 1 := by omega
        conv_lhs => rw [this, mul_add, mul_one]
      omega
    rw [heq2, Nat.mul_add_mod]

private lemma mod_add_one_rot {k q : ℕ} (hk : 2 ≤ k) :
    ((q % k) + k - (k - 1) % k) % k = (q + 1) % k := by
  rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)]
  have heq : q % k + k - (k - 1) = q % k + 1 := by omega
  rw [heq, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma testBit_stateFn_succ {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hrow : row < 2 ^ k) (r q : ℕ) (hq : 1 ≤ q) :
    bitFn k constant row (r + 1) key q =
      let x := fun j => bitFn k constant row r key j
      let m := fun j => xor (xor (x j) (x (j - 1))) (x (j + 1))
      xor (xor (m q) (!(m (q + 1)) && m (q + 2))) (injectedFn k constant (r + 1) key q) := by
  have hk0 : 0 < k := by omega
  have hst : stateFn k constant row (r + 1) key =
      stepFn k (stateFn k constant row r key ^^^ rotFn k 1 (stateFn k constant row r key) ^^^
        rotFn k (k - 1) (stateFn k constant row r key)) ^^^
        rotFn k (2 * r) key ^^^ (constant (r + 1)).val := by
    unfold stateFn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold bitFn injectedFn
  rw [hst, Nat.testBit_xor, Nat.testBit_xor, testBit_stepFn (Nat.mod_lt q hk0)]
  have hlt := stateFn_lt constant (key := key) hrow r
  have hmix : ∀ j : ℕ, 1 ≤ j →
      (stateFn k constant row r key ^^^ rotFn k 1 (stateFn k constant row r key) ^^^
        rotFn k (k - 1) (stateFn k constant row r key)).testBit (j % k) =
      xor (xor (bitFn k constant row r key j) (bitFn k constant row r key (j - 1)))
        (bitFn k constant row r key (j + 1)) := by
    intro j hj
    have hjm : j % k < k := Nat.mod_lt j hk0
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn hk0 hlt hjm, testBit_rotFn hk0 hlt hjm,
      mod_sub_one hk hj, mod_add_one_rot hk]
    rfl
  have h1 : (q % k + 1) % k = (q + 1) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (q % k + 2) % k = (q + 2) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2, hmix q hq, hmix (q + 1) (by omega), hmix (q + 2) (by omega)]
  have hs1 : r + 1 - 1 = r := by omega
  rw [hs1]
  simp only [Bool.xor_assoc]
  rfl

private lemma bitFn_zero_eq {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row : ℕ) {key : ℕ} (hkey : key < 2 ^ k) {q : ℕ} (hq : 1 ≤ q) :
    bitFn k constant row 0 key q =
      xor (key.testBit ((q - 1) % k)) (row.testBit (q % k)) := by
  have hk0 : 0 < k := by omega
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [testBit_rotFn hk0 hkey (Nat.mod_lt q hk0), mod_sub_one hk hq]

private lemma injectedFn_one_eq {k : ℕ} (hk : 0 < k) (constant : ℕ → Fin (2 ^ k))
    {key : ℕ} (hkey : key < 2 ^ k) (q : ℕ) :
    injectedFn k constant 1 key q =
      xor (key.testBit (q % k)) ((constant 1).val.testBit (q % k)) := by
  unfold injectedFn
  have h0 : 2 * (1 - 1) = 0 := rfl
  rw [h0, testBit_rotFn hk hkey (Nat.mod_lt q hk)]
  simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]

private lemma injectedFn_two_eq {k : ℕ} (hk : 3 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {key : ℕ} (hkey : key < 2 ^ k) {q : ℕ} (hq : 2 ≤ q) :
    injectedFn k constant 2 key q =
      xor (key.testBit ((q - 2) % k)) ((constant 2).val.testBit (q % k)) := by
  unfold injectedFn
  have h2 : 2 * (2 - 1) = 2 := rfl
  rw [h2, testBit_rotFn (by omega) hkey (Nat.mod_lt q (by omega)), mod_sub_two hk hq]

private lemma twoRound_formula {k : ℕ} (hk : 3 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (p : ℕ)
    (hpin : ∀ j : Fin 9, bitFn k constant row.val 0 key.val (p + j.val) =
      bitFn k constant row.val 0 ref.val (p + j.val))
    (hgood :
      let old := fun (j : ℕ) => bitFn k constant row.val 0 ref.val (p + j)
      let first := fun (j : ℕ) => bitFn k constant row.val 1 ref.val (p + j)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p + 6))
      let β := xor τ (injectedFn k constant 1 ref.val (p + 7))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) :
    let old := fun (j : ℕ) => bitFn k constant row.val 0 ref.val (p + j)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p + 6))
    let β := xor (xor (xor (old 6) (old 7)) (old 8)) (injectedFn k constant 1 ref.val (p + 7))
    let c8 := xor (xor (xor (old 7) (old 8)) (row.val.testBit ((p + 9) % k)))
      ((constant 1).val.testBit ((p + 8) % k))
    let d := xor (xor α β) c8
    let c2 := injectedFn k constant 2 ref.val (p + 5)
    let b0 := key.val.testBit ((p + 8) % k)
    let b1 := key.val.testBit ((p + 9) % k)
    let b2 := key.val.testBit ((p + 10) % k)
    let s0 := xor (xor (old 7) (old 8)) (row.val.testBit ((p + 9) % k))
    let s1 := xor (xor (xor (old 8) (row.val.testBit ((p + 9) % k))) (row.val.testBit ((p + 10) % k))) true
    let s2 := xor (xor (xor (xor (row.val.testBit ((p + 9) % k)) (row.val.testBit ((p + 10) % k)))
      (row.val.testBit ((p + 11) % k))) d) true
    let U' := xor b0 s0
    let V' := xor (xor b0 b1) s1
    let W' := xor (xor (xor b0 b1) b2) s2
    bitFn k constant row.val 2 key.val (p + 5) =
      xor (xor (xor (U' && V' && W') U') (!d && V')) (xor d c2) := by
  intro old α β c8 d c2 b0 b1 b2 s0 s1 s2 U' V' W'
  rcases hgood with ⟨hτ, _, hf45, hf4⟩
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  have hkey_pin : ∀ r : ℕ, r < 8 → key.val.testBit ((p + r) % k) = ref.val.testBit ((p + r) % k) := by
    intro r hr
    have h1 := hpin ⟨r + 1, by omega⟩
    dsimp only at h1
    rw [bitFn_zero_eq hk2 constant row.val key.isLt (by omega),
      bitFn_zero_eq hk2 constant row.val ref.isLt (by omega)] at h1
    have hsub : p + (r + 1) - 1 = p + r := by omega
    rw [hsub] at h1
    apply toZ2_injective
    have h2 := congrArg toZ2 h1
    rw [toZ2_xor, toZ2_xor] at h2
    calc toZ2 (key.val.testBit ((p + r) % k))
        = (toZ2 (key.val.testBit ((p + r) % k)) + toZ2 (row.val.testBit ((p + (r + 1)) % k))) +
            toZ2 (row.val.testBit ((p + (r + 1)) % k)) := by
              rw [add_assoc, zmod2_add_self, add_zero]
      _ = (toZ2 (ref.val.testBit ((p + r) % k)) + toZ2 (row.val.testBit ((p + (r + 1)) % k))) +
            toZ2 (row.val.testBit ((p + (r + 1)) % k)) := by rw [h2]
      _ = toZ2 (ref.val.testBit ((p + r) % k)) := by rw [add_assoc, zmod2_add_self, add_zero]
  have hinj1_eq : ∀ r : ℕ, r < 8 →
      injectedFn k constant 1 key.val (p + r) = injectedFn k constant 1 ref.val (p + r) := by
    intro r hr
    rw [injectedFn_one_eq hk0 constant key.isLt, injectedFn_one_eq hk0 constant ref.isLt, hkey_pin r hr]
  have hinj2_eq : injectedFn k constant 2 key.val (p + 5) = c2 := by
    dsimp only [c2]
    rw [injectedFn_two_eq hk constant key.isLt (by omega),
      injectedFn_two_eq hk constant ref.isLt (by omega)]
    have hsub : p + 5 - 2 = p + 3 := by omega
    rw [hsub, hkey_pin 3 (by omega)]
  have hx : ∀ r : ℕ, r < 9 → bitFn k constant row.val 0 key.val (p + r) = old r := fun r hr =>
    hpin ⟨r, hr⟩
  have hx9 : bitFn k constant row.val 0 key.val (p + 9) = xor b0 (row.val.testBit ((p + 9) % k)) := by
    rw [bitFn_zero_eq hk2 constant row.val key.isLt (by omega)]
    have : p + 9 - 1 = p + 8 := by omega
    rw [this]
  have hx10 : bitFn k constant row.val 0 key.val (p + 10) = xor b1 (row.val.testBit ((p + 10) % k)) := by
    rw [bitFn_zero_eq hk2 constant row.val key.isLt (by omega)]
    have : p + 10 - 1 = p + 9 := by omega
    rw [this]
  have hx11 : bitFn k constant row.val 0 key.val (p + 11) = xor b2 (row.val.testBit ((p + 11) % k)) := by
    rw [bitFn_zero_eq hk2 constant row.val key.isLt (by omega)]
    have : p + 11 - 1 = p + 10 := by omega
    rw [this]
  have hy4 : bitFn k constant row.val 1 key.val (p + 4) = bitFn k constant row.val 1 ref.val (p + 4) := by
    rw [testBit_stateFn_succ hk2 constant row.isLt 0 (p + 4) (by omega),
      testBit_stateFn_succ hk2 constant row.isLt 0 (p + 4) (by omega)]
    dsimp only
    have hs1 : p + 4 - 1 = p + 3 := by omega
    have hs2 : p + 4 + 1 - 1 = p + 4 := by omega
    have hs3 : p + 4 + 2 - 1 = p + 5 := by omega
    have ha1 : p + 4 + 1 = p + 5 := by omega
    have ha2 : p + 4 + 2 = p + 6 := by omega
    have ha3 : p + 4 + 1 + 1 = p + 6 := by omega
    have ha4 : p + 4 + 2 + 1 = p + 7 := by omega
    rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hx 3 (by omega), hx 4 (by omega), hx 5 (by omega),
      hx 6 (by omega), hx 7 (by omega), hinj1_eq 4 (by omega)]
  have hy5 : bitFn k constant row.val 1 key.val (p + 5) = bitFn k constant row.val 1 ref.val (p + 5) := by
    rw [testBit_stateFn_succ hk2 constant row.isLt 0 (p + 5) (by omega),
      testBit_stateFn_succ hk2 constant row.isLt 0 (p + 5) (by omega)]
    dsimp only
    have hs1 : p + 5 - 1 = p + 4 := by omega
    have hs2 : p + 5 + 1 - 1 = p + 5 := by omega
    have hs3 : p + 5 + 2 - 1 = p + 6 := by omega
    have ha1 : p + 5 + 1 = p + 6 := by omega
    have ha2 : p + 5 + 2 = p + 7 := by omega
    have ha3 : p + 5 + 1 + 1 = p + 7 := by omega
    have ha4 : p + 5 + 2 + 1 = p + 8 := by omega
    rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hx 4 (by omega), hx 5 (by omega), hx 6 (by omega),
      hx 7 (by omega), hx 8 (by omega), hinj1_eq 5 (by omega)]
  set U := xor (xor (old 7) (old 8)) (bitFn k constant row.val 0 key.val (p + 9))
  set V := xor (xor (old 8) (bitFn k constant row.val 0 key.val (p + 9)))
    (bitFn k constant row.val 0 key.val (p + 10))
  set W := xor (xor (bitFn k constant row.val 0 key.val (p + 9))
    (bitFn k constant row.val 0 key.val (p + 10))) (bitFn k constant row.val 0 key.val (p + 11))
  have hU_eq : U = U' := by
    dsimp only [U, U', s0]
    rw [hx9]
    cases old 7 <;> cases old 8 <;> cases b0 <;> cases row.val.testBit ((p + 9) % k) <;> decide
  have hV_eq : V = !V' := by
    dsimp only [V, V', s1]
    rw [hx9, hx10]
    cases old 8 <;> cases b0 <;> cases b1 <;> cases row.val.testBit ((p + 9) % k) <;>
      cases row.val.testBit ((p + 10) % k) <;> decide
  have hW_eq : W = xor W' (!d) := by
    dsimp only [W, W', s2]
    rw [hx9, hx10, hx11]
    cases b0 <;> cases b1 <;> cases b2 <;> cases d <;>
      cases row.val.testBit ((p + 9) % k) <;> cases row.val.testBit ((p + 10) % k) <;>
      cases row.val.testBit ((p + 11) % k) <;> decide
  have hy6 : bitFn k constant row.val 1 key.val (p + 6) = xor α U := by
    rw [testBit_stateFn_succ hk2 constant row.isLt 0 (p + 6) (by omega)]
    dsimp only
    have hs1 : p + 6 - 1 = p + 5 := by omega
    have hs2 : p + 6 + 1 - 1 = p + 6 := by omega
    have hs3 : p + 6 + 2 - 1 = p + 7 := by omega
    have ha1 : p + 6 + 1 = p + 7 := by omega
    have ha2 : p + 6 + 2 = p + 8 := by omega
    have ha3 : p + 6 + 1 + 1 = p + 8 := by omega
    have ha4 : p + 6 + 2 + 1 = p + 9 := by omega
    rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hx 5 (by omega), hx 6 (by omega), hx 7 (by omega),
      hx 8 (by omega), hinj1_eq 6 (by omega)]
    have hτ' : xor (xor (old 7) (old 6)) (old 8) = false := by
      have hcomm : xor (xor (old 7) (old 6)) (old 8) = xor (xor (old 6) (old 7)) (old 8) := by
        cases old 6 <;> cases old 7 <;> cases old 8 <;> decide
      rw [hcomm]
      exact hτ
    have hm8 : xor (xor (old 8) (old 7)) (bitFn k constant row.val 0 key.val (p + 9)) = U := by
      dsimp only [U]
      cases old 7 <;> cases old 8 <;> cases bitFn k constant row.val 0 key.val (p + 9) <;> decide
    rw [hτ', hm8]
    dsimp only [α]
    cases old 5 <;> cases old 6 <;> cases old 7 <;> cases injectedFn k constant 1 ref.val (p + 6) <;>
      cases U <;> decide
  have hy7 : bitFn k constant row.val 1 key.val (p + 7) = xor β (!U && V) := by
    rw [testBit_stateFn_succ hk2 constant row.isLt 0 (p + 7) (by omega)]
    dsimp only
    have hs1 : p + 7 - 1 = p + 6 := by omega
    have hs2 : p + 7 + 1 - 1 = p + 7 := by omega
    have hs3 : p + 7 + 2 - 1 = p + 8 := by omega
    have ha1 : p + 7 + 1 = p + 8 := by omega
    have ha2 : p + 7 + 2 = p + 9 := by omega
    have ha3 : p + 7 + 1 + 1 = p + 9 := by omega
    have ha4 : p + 7 + 2 + 1 = p + 10 := by omega
    rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hx 6 (by omega), hx 7 (by omega), hx 8 (by omega),
      hinj1_eq 7 (by omega)]
    have hτ' : xor (xor (old 7) (old 6)) (old 8) = xor (xor (old 6) (old 7)) (old 8) := by
      cases old 6 <;> cases old 7 <;> cases old 8 <;> decide
    have hm8 : xor (xor (old 8) (old 7)) (bitFn k constant row.val 0 key.val (p + 9)) = U := by
      dsimp only [U]
      cases old 7 <;> cases old 8 <;> cases bitFn k constant row.val 0 key.val (p + 9) <;> decide
    have hm9 : xor (xor (bitFn k constant row.val 0 key.val (p + 9)) (old 8))
        (bitFn k constant row.val 0 key.val (p + 10)) = V := by
      dsimp only [V]
      cases old 8 <;> cases bitFn k constant row.val 0 key.val (p + 9) <;>
        cases bitFn k constant row.val 0 key.val (p + 10) <;> decide
    rw [hτ', hm8, hm9]
    dsimp only [β]
    cases xor (xor (old 6) (old 7)) (old 8) <;> cases injectedFn k constant 1 ref.val (p + 7) <;>
      cases (!U && V) <;> decide
  have hy8 : bitFn k constant row.val 1 key.val (p + 8) = xor c8 (!V && W) := by
    rw [testBit_stateFn_succ hk2 constant row.isLt 0 (p + 8) (by omega)]
    dsimp only
    have hs1 : p + 8 - 1 = p + 7 := by omega
    have hs2 : p + 8 + 1 - 1 = p + 8 := by omega
    have hs3 : p + 8 + 2 - 1 = p + 9 := by omega
    have ha1 : p + 8 + 1 = p + 9 := by omega
    have ha2 : p + 8 + 2 = p + 10 := by omega
    have ha3 : p + 8 + 1 + 1 = p + 10 := by omega
    have ha4 : p + 8 + 2 + 1 = p + 11 := by omega
    rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hx 7 (by omega), hx 8 (by omega),
      injectedFn_one_eq hk0 constant key.isLt]
    have hm8 : xor (xor (old 8) (old 7)) (bitFn k constant row.val 0 key.val (p + 9)) = U := by
      dsimp only [U]
      cases old 7 <;> cases old 8 <;> cases bitFn k constant row.val 0 key.val (p + 9) <;> decide
    have hm9 : xor (xor (bitFn k constant row.val 0 key.val (p + 9)) (old 8))
        (bitFn k constant row.val 0 key.val (p + 10)) = V := by
      dsimp only [V]
      cases old 8 <;> cases bitFn k constant row.val 0 key.val (p + 9) <;>
        cases bitFn k constant row.val 0 key.val (p + 10) <;> decide
    have hm10 : xor (xor (bitFn k constant row.val 0 key.val (p + 10))
        (bitFn k constant row.val 0 key.val (p + 9)))
        (bitFn k constant row.val 0 key.val (p + 11)) = W := by
      dsimp only [W]
      cases bitFn k constant row.val 0 key.val (p + 9) <;>
        cases bitFn k constant row.val 0 key.val (p + 10) <;>
        cases bitFn k constant row.val 0 key.val (p + 11) <;> decide
    rw [hm8, hm9, hm10]
    have hUc : xor U (xor b0 ((constant 1).val.testBit ((p + 8) % k))) = c8 := by
      dsimp only [U, c8]
      rw [hx9]
      cases old 7 <;> cases old 8 <;> cases b0 <;> cases row.val.testBit ((p + 9) % k) <;>
        cases (constant 1).val.testBit ((p + 8) % k) <;> decide
    rw [← hUc]
    change xor (xor U (!V && W)) (xor b0 ((constant 1).val.testBit ((p + 8) % k))) =
      xor (xor U (xor b0 ((constant 1).val.testBit ((p + 8) % k)))) (!V && W)
    cases U <;> cases (!V && W) <;> cases b0 <;>
      cases (constant 1).val.testBit ((p + 8) % k) <;> decide
  rw [testBit_stateFn_succ hk2 constant row.isLt 1 (p + 5) (by omega)]
  dsimp only
  have hs1 : p + 5 - 1 = p + 4 := by omega
  have hs2 : p + 5 + 1 - 1 = p + 5 := by omega
  have hs3 : p + 5 + 2 - 1 = p + 6 := by omega
  have ha1 : p + 5 + 1 = p + 6 := by omega
  have ha2 : p + 5 + 2 = p + 7 := by omega
  have ha3 : p + 5 + 1 + 1 = p + 7 := by omega
  have ha4 : p + 5 + 2 + 1 = p + 8 := by omega
  rw [hs1, hs2, hs3, ha1, ha2, ha3, ha4, hy4, hy5, hy6, hy7, hy8, hinj2_eq]
  have hf4' : bitFn k constant row.val 1 ref.val (p + 4) = β := hf4
  have hf45' : xor (bitFn k constant row.val 1 ref.val (p + 4))
      (bitFn k constant row.val 1 ref.val (p + 5)) = !α := hf45
  have hf5 : bitFn k constant row.val 1 ref.val (p + 5) = xor (!α) β := by
    rw [hf4'] at hf45'
    revert hf45'
    cases α <;> cases β <;> cases bitFn k constant row.val 1 ref.val (p + 5) <;> decide
  rw [hf4', hf5, hU_eq, hV_eq, hW_eq]
  dsimp only [d]
  cases α <;> cases β <;> cases c8 <;> cases c2 <;> cases U' <;> cases V' <;> cases W' <;> decide

private def runFn {α : Type*} (steps : ℕ) (ask : ℕ → ℕ → α → Bool) (x : α) : ℕ :=
  (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0

private lemma runFn_succ {α : Type*} (steps : ℕ) (ask : ℕ → ℕ → α → Bool) (x : α) :
    runFn (steps + 1) ask x =
      runFn steps ask x + ((ask steps (runFn steps ask x) x).toNat <<< steps) := by
  unfold runFn
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma runFn_lt {α : Type*} (steps : ℕ) (ask : ℕ → ℕ → α → Bool) (x : α) :
    runFn steps ask x < 2 ^ steps := by
  induction steps with
  | zero => simp [runFn]
  | succ s ih =>
    rw [runFn_succ, Nat.shiftLeft_eq]
    have hb : (ask s (runFn s ask x) x).toNat ≤ 1 := by
      cases ask s (runFn s ask x) x <;> decide
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
    nlinarith

private lemma runFn_mod {α : Type*} (ask : ℕ → ℕ → α → Bool) (x : α)
    {u steps : ℕ} (hu : u ≤ steps) :
    runFn steps ask x % 2 ^ u = runFn u ask x := by
  induction steps with
  | zero =>
    have hu0 : u = 0 := by omega
    subst hu0; simp [runFn]
  | succ s ih =>
    by_cases heq : u = s + 1
    · subst heq; exact Nat.mod_eq_of_lt (runFn_lt (s + 1) ask x)
    · have hus : u ≤ s := by omega
      rw [runFn_succ, Nat.shiftLeft_eq]
      have hdvd : 2 ^ u ∣ 2 ^ s := Nat.pow_dvd_pow 2 hus
      rcases hdvd with ⟨q, hq⟩
      rw [hq, show (ask s (runFn s ask x) x).toNat * (2 ^ u * q) =
          2 ^ u * ((ask s (runFn s ask x) x).toNat * q) by ring,
        Nat.add_mul_mod_self_left]
      exact ih hus

private lemma runFn_testBit {α : Type*} (ask : ℕ → ℕ → α → Bool) (x : α)
    {u steps : ℕ} (hu : u < steps) :
    (runFn steps ask x).testBit u = ask u (runFn u ask x) x := by
  have hmod := runFn_mod ask x (by omega : u + 1 ≤ steps)
  have htb : (runFn (u + 1) ask x).testBit u = (runFn steps ask x).testBit u := by
    rw [← hmod, Nat.testBit_mod_two_pow]
    simp
  rw [← htb, runFn_succ]
  have hadd : runFn u ask x + ((ask u (runFn u ask x) x).toNat <<< u) =
      runFn u ask x ||| ((ask u (runFn u ask x) x).toNat <<< u) := by
    have hlt := runFn_lt u ask x
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hju : j < u
    · have hnot : ¬ u ≤ j := by omega
      simp only [hnot, decide_false, Bool.false_and, Bool.or_false]
      rw [Nat.shiftLeft_eq]
      have hdvd : 2 ^ (j + 1) ∣ 2 ^ u := Nat.pow_dvd_pow 2 (by omega)
      rcases hdvd with ⟨q, hq⟩
      have hdiv : (runFn u ask x + (ask u (runFn u ask x) x).toNat * 2 ^ u) % 2 ^ (j + 1) =
          runFn u ask x % 2 ^ (j + 1) := by
        rw [hq, show (ask u (runFn u ask x) x).toNat * (2 ^ (j + 1) * q) =
            2 ^ (j + 1) * ((ask u (runFn u ask x) x).toNat * q) by ring,
          Nat.add_mul_mod_self_left]
      have htb1 : (runFn u ask x + (ask u (runFn u ask x) x).toNat * 2 ^ u).testBit j =
          ((runFn u ask x + (ask u (runFn u ask x) x).toNat * 2 ^ u) % 2 ^ (j + 1)).testBit j := by
        rw [Nat.testBit_mod_two_pow]; simp
      have htb2 : (runFn u ask x).testBit j = (runFn u ask x % 2 ^ (j + 1)).testBit j := by
        rw [Nat.testBit_mod_two_pow]; simp
      rw [htb1, hdiv, ← htb2]
    · have hge : u ≤ j := by omega
      have hf : (runFn u ask x).testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hge))
      simp only [hf, hge, decide_true, Bool.true_and, Bool.false_or]
      rw [Nat.shiftLeft_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ j = 2 ^ u * 2 ^ (j - u) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
      rw [hpow, ← Nat.div_div_eq_div_mul,
        show runFn u ask x + (ask u (runFn u ask x) x).toNat * 2 ^ u =
          runFn u ask x + 2 ^ u * (ask u (runFn u ask x) x).toNat by ring,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [hadd, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hf : (runFn u ask x).testBit u = false := Nat.testBit_lt_two_pow (runFn_lt u ask x)
  simp only [hf, le_refl, decide_true, Bool.true_and, Nat.sub_self, Bool.false_or]
  cases ask u (runFn u ask x) x <;> decide

private lemma runFn_eq_iff {α : Type*} (steps : ℕ) (ask : ℕ → ℕ → α → Bool) (x : α)
    {p : ℕ} (hp : p < 2 ^ steps) :
    runFn steps ask x = p ↔
      ∀ u : Fin steps, ask u.val (p % 2 ^ u.val) x = p.testBit u.val := by
  constructor
  · intro heq u
    subst heq
    rw [runFn_mod ask x (le_of_lt u.isLt), runFn_testBit ask x u.isLt]
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < steps
    · have hstrong : ∀ i : ℕ, i ≤ steps → runFn i ask x = p % 2 ^ i := by
        intro i
        induction i with
        | zero => intro _; simp [runFn, Nat.mod_one]
        | succ i ih =>
          intro hi
          have hprev := ih (by omega)
          have hbit := hall ⟨i, by omega⟩
          rw [← hprev] at hbit
          apply Nat.eq_of_testBit_eq
          intro t
          rw [Nat.testBit_mod_two_pow]
          by_cases ht : t < i + 1
          · simp only [ht, decide_true, Bool.true_and]
            by_cases hti : t < i
            · have hm := runFn_mod ask x (show i ≤ i + 1 by omega)
              have h1 : (runFn (i + 1) ask x).testBit t = (runFn (i + 1) ask x % 2 ^ i).testBit t := by
                rw [Nat.testBit_mod_two_pow]; simp [hti]
              rw [h1, hm, hprev, Nat.testBit_mod_two_pow]; simp [hti]
            · have hteq : t = i := by omega
              rw [hteq, runFn_testBit ask x (Nat.lt_succ_self i), hbit]
          · simp only [ht, decide_false, Bool.false_and]
            exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (runFn_lt (i + 1) ask x)
              (Nat.pow_le_pow_right (by omega) (show i + 1 ≤ t by omega)))
      have hfull := hstrong steps le_rfl
      rw [Nat.mod_eq_of_lt hp] at hfull
      rw [hfull]
    · have hpow : 2 ^ steps ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (runFn_lt steps ask x) hpow)
      have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hp hpow)
      rw [h1, h2]

private def pathInd {ι : Type*} (d : ℕ) (ask : ℕ → ℕ → (ι → Bool) → Bool) (p : ℕ)
    (y : ι → Bool) : ZMod 2 :=
  ∏ u : Fin d, (1 + toZ2 (ask u.val (p % 2 ^ u.val) y) + toZ2 (p.testBit u.val))

private lemma pathInd_eq {ι : Type*} (d : ℕ) (ask : ℕ → ℕ → (ι → Bool) → Bool)
    {p : ℕ} (hp : p < 2 ^ d) (y : ι → Bool) :
    pathInd d ask p y = if runFn d ask y = p then 1 else 0 := by
  unfold pathInd
  by_cases h : runFn d ask y = p
  · simp only [h, ↓reduceIte]
    refine Finset.prod_eq_one fun u _ => ?_
    have hu := (runFn_eq_iff d ask y hp).mp h u
    rw [hu, add_assoc, zmod2_add_self, add_zero]
  · simp only [h, ↓reduceIte]
    have hnot : ¬ ∀ u : Fin d, ask u.val (p % 2 ^ u.val) y = p.testBit u.val :=
      fun hall => h ((runFn_eq_iff d ask y hp).mpr hall)
    push Not at hnot
    rcases hnot with ⟨u, hu⟩
    refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
    cases h1 : ask u.val (p % 2 ^ u.val) y <;> cases h2 : p.testBit u.val
    · rw [h1, h2] at hu; exact absurd rfl hu
    · decide
    · decide
    · rw [h1, h2] at hu; exact absurd rfl hu

private lemma pathInd_hasDeg {ι : Type*} [Fintype ι] [DecidableEq ι] (b d : ℕ)
    (ask : ℕ → ℕ → (ι → Bool) → Bool)
    (hask : ∀ (u : Fin d) (path : ℕ), HasDeg b (fun y => toZ2 (ask u.val path y)))
    (p : ℕ) :
    HasDeg (b * d) (pathInd d ask p) := by
  have hfac : ∀ u : Fin d,
      HasDeg b (fun y => 1 + toZ2 (ask u.val (p % 2 ^ u.val) y) + toZ2 (p.testBit u.val)) := by
    intro u
    have h1 : HasDeg b (fun y => (1 : ZMod 2) + toZ2 (ask u.val (p % 2 ^ u.val) y)) :=
      hasDeg_add (hasDeg_mono (Nat.zero_le b) (hasDeg_const 1)) (hask u (p % 2 ^ u.val))
    exact hasDeg_add h1 (hasDeg_mono (Nat.zero_le b) (hasDeg_const _))
  have hprod : HasDeg (∑ _u ∈ (Finset.univ : Finset (Fin d)), b)
      (fun y => ∏ u ∈ (Finset.univ : Finset (Fin d)),
        (1 + toZ2 (ask u.val (p % 2 ^ u.val) y) + toZ2 (p.testBit u.val))) :=
    hasDeg_prod (Finset.univ : Finset (Fin d)) (fun _ => b)
      (fun u y => 1 + toZ2 (ask u.val (p % 2 ^ u.val) y) + toZ2 (p.testBit u.val))
      (fun u _ => hfac u)
  have hsum : (∑ _u ∈ (Finset.univ : Finset (Fin d)), b) = b * d := by simp [mul_comm]
  rw [hsum] at hprod
  unfold pathInd
  exact hprod

private def block3 {m : ℕ} (i : Fin m) : Finset (Fin m × Fin 3) :=
  (Finset.univ : Finset (Fin 3)).image (fun j => (i, j))

private lemma card_block3 {m : ℕ} (i : Fin m) : (block3 i).card = 3 := by
  unfold block3
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

private lemma disjoint_block3 {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (block3 i) (block3 j) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rcases Finset.mem_image.mp hv1 with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hv2 with ⟨b, _, h⟩
  exact hij (congrArg Prod.fst h).symm

private lemma monEval_block3 {m : ℕ} (i : Fin m) (y : (Fin m × Fin 3) → Bool) :
    monEval (block3 i) y = toZ2 (y (i, 0) && y (i, 1) && y (i, 2)) := by
  have hset : block3 i = {(i, 0), (i, 1), (i, 2)} := by
    ext ⟨i', j⟩
    simp only [block3, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨j', rfl, rfl⟩
      fin_cases j' <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨0, rfl, rfl⟩
      · exact ⟨1, rfl, rfl⟩
      · exact ⟨2, rfl, rfl⟩
  rw [hset, monEval_eq_prod]
  have h01 : (i, (0 : Fin 3)) ≠ (i, 1) := fun h => by
    have h' := congrArg Prod.snd h; dsimp only at h'; exact absurd h' (by decide)
  have h02 : (i, (0 : Fin 3)) ≠ (i, 2) := fun h => by
    have h' := congrArg Prod.snd h; dsimp only at h'; exact absurd h' (by decide)
  have h12 : (i, (1 : Fin 3)) ≠ (i, 2) := fun h => by
    have h' := congrArg Prod.snd h; dsimp only at h'; exact absurd h' (by decide)
  rw [Finset.prod_insert (by simp [h01, h02]), Finset.prod_insert (by simp [h12]),
    Finset.prod_singleton, toZ2_and, toZ2_and, mul_assoc]

private lemma card_filled_eq (m f : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter
      (fun mon => ((Finset.univ : Finset (Fin m)).filter (fun i => block3 i ⊆ mon)).card = f)).card =
    Nat.choose m f * 7 ^ (m - f) := by
  classical
  let filledOf : Finset (Fin m × Fin 3) → Finset (Fin m) :=
    fun mon => Finset.univ.filter (fun i => block3 i ⊆ mon)
  have hfib : ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter
      (fun mon => (filledOf mon).card = f)).card =
      ∑ F ∈ (Finset.univ : Finset (Fin m)).powersetCard f,
        ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => filledOf mon = F)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext mon
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_powersetCard, Finset.subset_univ]
      constructor
      · intro hcard; exact ⟨filledOf mon, hcard, rfl⟩
      · rintro ⟨F, hF, rfl⟩; exact hF
    · intro F1 _ F2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro mon h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hfib]
  have heach : ∀ F ∈ (Finset.univ : Finset (Fin m)).powersetCard f,
      ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => filledOf mon = F)).card =
      7 ^ (m - f) := by
    intro F hF
    have hFcard : F.card = f := (Finset.mem_powersetCard.mp hF).2
    let nonFull : Finset (Finset (Fin 3)) := Finset.univ.erase Finset.univ
    have hnf_card : nonFull.card = 7 := by decide
    let e : {mon : Finset (Fin m × Fin 3) // filledOf mon = F} ≃
        ({i : Fin m // i ∉ F} → {s : Finset (Fin 3) // s ∈ nonFull}) :=
      { toFun := fun ⟨mon, hmon⟩ ⟨i, hi⟩ =>
          ⟨Finset.univ.filter (fun j : Fin 3 => (i, j) ∈ mon), by
            rw [Finset.mem_erase]
            refine ⟨?_, Finset.mem_univ _⟩
            intro hall
            apply hi
            rw [← hmon, Finset.mem_filter]
            refine ⟨Finset.mem_univ i, fun v hv => ?_⟩
            rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
            have hj : j ∈ Finset.univ.filter (fun j : Fin 3 => (i, j) ∈ mon) := by
              rw [hall]; exact Finset.mem_univ j
            exact (Finset.mem_filter.mp hj).2⟩
        invFun := fun g =>
          ⟨Finset.univ.filter (fun v : Fin m × Fin 3 =>
              if hv : v.1 ∈ F then True else v.2 ∈ (g ⟨v.1, hv⟩).1), by
            ext i
            simp only [filledOf, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hsub
              by_contra hiF
              have hall : (g ⟨i, hiF⟩).1 = Finset.univ := by
                ext j
                simp only [Finset.mem_univ, iff_true]
                have hmem : (i, j) ∈ block3 i := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
                have h2 := hsub hmem
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiF, ↓reduceDIte] at h2
                exact h2
              exact (Finset.mem_erase.mp (g ⟨i, hiF⟩).2).1 hall
            · intro hiF v hv
              rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
              simp [hiF]⟩
        left_inv := fun ⟨mon, hmon⟩ => by
          ext ⟨i, j⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hiF : i ∈ F
          · simp only [hiF, ↓reduceDIte, true_iff]
            have hmemF : i ∈ filledOf mon := hmon.symm ▸ hiF
            dsimp only [filledOf] at hmemF
            have hsub : block3 i ⊆ mon := (Finset.mem_filter.mp hmemF).2
            exact hsub (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
          · simp [hiF]
        right_inv := fun g => by
          funext ⟨i, hi⟩
          ext j
          simp [hi] }
    have hcard_eq : ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => filledOf mon = F)).card =
        Fintype.card {mon : Finset (Fin m × Fin 3) // filledOf mon = F} := by
      rw [Fintype.card_subtype]
    rw [hcard_eq, Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, hnf_card]
    have hcomp : Fintype.card {i : Fin m // i ∉ F} = m - f := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hFcard]
    rw [hcomp]
  rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

private lemma card_filledLt_eq_count (m T : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter
      (fun mon => ((Finset.univ : Finset (Fin m)).filter (fun i => block3 i ⊆ mon)).card < T)).card =
    (Finset.range (m + 1)).sum (fun filled =>
      if filled < T then Nat.choose m filled * 7 ^ (m - filled) else 0) := by
  classical
  let filledOf : Finset (Fin m × Fin 3) → ℕ :=
    fun mon => ((Finset.univ : Finset (Fin m)).filter (fun i => block3 i ⊆ mon)).card
  have hle : ∀ mon : Finset (Fin m × Fin 3), filledOf mon < m + 1 := fun mon => by
    have h1 : filledOf mon ≤ m := by
      calc filledOf mon ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
        _ = m := Finset.card_fin m
    omega
  have hpart : ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => filledOf mon < T)).card =
      ∑ filled ∈ (Finset.range (m + 1)).filter (fun f => f < T),
        ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => filledOf mon = filled)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext mon
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · intro hlt; exact ⟨filledOf mon, ⟨hle mon, hlt⟩, rfl⟩
      · rintro ⟨f, ⟨_, hlt⟩, rfl⟩; exact hlt
    · intro f1 _ f2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro mon h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs
  · exact card_filled_eq m f
  · rfl

private lemma slice_hit_le_count {m b d L : ℕ}
    (ask : ℕ → ℕ → ((Fin m × Fin 3) → Bool) → Bool)
    (Q : ℕ → Fin L → Fin m → ((Fin m × Fin 3) → Bool) → ZMod 2)
    (hask : ∀ (u : Fin d) (path : ℕ), HasDeg b (fun y => toZ2 (ask u.val path y)))
    (hQ : ∀ path a i, HasDeg 2 (Q path a i)) :
    let S := (Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter
      (fun y => ∃ a : Fin L, ∀ i : Fin m, monEval (block3 i) y = Q (runFn d ask y) a i y)
    S.card ≤ (Finset.range (m + 1)).sum (fun filled =>
      if filled < L * (b * d + 1) then Nat.choose m filled * 7 ^ (m - filled) else 0) := by
  classical
  intro S
  by_cases hL0 : L = 0
  · subst hL0
    have hemp : S = ∅ := by
      ext y
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨a, _⟩
      exact a.elim0
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  set T := L * (b * d + 1)
  set t := b * d + 1
  let G : Finset (Finset (Fin m × Fin 3)) := Finset.univ.filter
    (fun mon => ((Finset.univ : Finset (Fin m)).filter (fun i => block3 i ⊆ mon)).card < T)
  have hGcard : G.card = (Finset.range (m + 1)).sum (fun filled =>
      if filled < T then Nat.choose m filled * 7 ^ (m - filled) else 0) :=
    card_filledLt_eq_count m T
  have hmon_span : ∀ n : ℕ, ∀ mon : Finset (Fin m × Fin 3), mon.card = n →
      ∃ c : Finset (Fin m × Fin 3) → ZMod 2,
        (∀ s, s ∉ G → c s = 0) ∧ ∀ y ∈ S, monEval mon y = polyEval c y := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro mon hcard
      by_cases hmem : mon ∈ G
      · refine ⟨fun s => if s = mon then 1 else 0, ?_, fun y _ => ?_⟩
        · intro s hs
          have hne : s ≠ mon := fun h => hs (h ▸ hmem)
          simp [hne]
        · unfold polyEval
          rw [Finset.sum_eq_single mon]
          · simp
          · intro s _ hne; simp [hne]
          · intro hnot; exact absurd (Finset.mem_univ mon) hnot
      · set F := (Finset.univ : Finset (Fin m)).filter (fun i => block3 i ⊆ mon)
        have hFge : T ≤ F.card := by
          by_contra hlt
          push Not at hlt
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ mon, hlt⟩)
        let eF : Fin F.card ≃ {i : Fin m // i ∈ F} := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
        let blk : Fin L → Fin t → Fin m := fun a r =>
          (eF ⟨a.val * t + r.val, by
            have ha : a.val + 1 ≤ L := a.isLt
            have hr : r.val < t := r.isLt
            have hm : (a.val + 1) * t ≤ L * t := Nat.mul_le_mul_right t ha
            have hadd : a.val * t + t = (a.val + 1) * t := by ring
            have hTt : T = L * t := rfl
            omega⟩).1
        have hblk_in : ∀ a r, block3 (blk a r) ⊆ mon := fun a r =>
          (Finset.mem_filter.mp (eF _).2).2
        have hblk_inj : Function.Injective (fun p : Fin L × Fin t => blk p.1 p.2) := by
          intro p1 p2 heq
          have heq' : eF ⟨p1.1.val * t + p1.2.val, _⟩ = eF ⟨p2.1.val * t + p2.2.val, _⟩ :=
            Subtype.ext heq
          have hidx := congrArg Fin.val (eF.injective heq')
          dsimp only at hidx
          have htpos : 0 < t := by omega
          have hq : p1.1.val = p2.1.val := by
            have h1 : (p1.1.val * t + p1.2.val) / t = p1.1.val := by
              rw [mul_comm, Nat.mul_add_div htpos, Nat.div_eq_of_lt p1.2.isLt, add_zero]
            have h2 : (p2.1.val * t + p2.2.val) / t = p2.1.val := by
              rw [mul_comm, Nat.mul_add_div htpos, Nat.div_eq_of_lt p2.2.isLt, add_zero]
            rw [hidx] at h1; omega
          have hr : p1.2.val = p2.2.val := by nlinarith
          exact Prod.ext (Fin.ext hq) (Fin.ext hr)
        let grpSet : Fin L → Finset (Fin m × Fin 3) := fun a =>
          (Finset.univ : Finset (Fin t)).biUnion (fun r => block3 (blk a r))
        let allGrp : Finset (Fin m × Fin 3) := (Finset.univ : Finset (Fin L)).biUnion grpSet
        have hgrp_disj : ∀ a1 a2 : Fin L, a1 ≠ a2 → Disjoint (grpSet a1) (grpSet a2) := by
          intro a1 a2 hne
          rw [Finset.disjoint_left]
          intro v hv1 hv2
          rcases Finset.mem_biUnion.mp hv1 with ⟨r1, _, h1⟩
          rcases Finset.mem_biUnion.mp hv2 with ⟨r2, _, h2⟩
          have hbeq : blk a1 r1 = blk a2 r2 := by
            by_contra hbn
            exact Finset.disjoint_left.mp (disjoint_block3 hbn) h1 h2
          exact hne (congrArg Prod.fst (hblk_inj (a₁ := (a1, r1)) (a₂ := (a2, r2)) hbeq))
        have hgrp_card : ∀ a : Fin L, (grpSet a).card = 3 * t := by
          intro a
          rw [Finset.card_biUnion]
          · simp [card_block3, mul_comm]
          · intro r1 _ r2 _ hne
            exact disjoint_block3 fun h => hne (congrArg Prod.snd (hblk_inj (a₁ := (a, r1)) (a₂ := (a, r2)) h))
        have hall_card : allGrp.card = 3 * t * L := by
          rw [Finset.card_biUnion]
          · simp [hgrp_card, mul_comm]
          · intro a1 _ a2 _ hne; exact hgrp_disj a1 a2 hne
        have hall_sub : allGrp ⊆ mon := by
          intro v hv
          rcases Finset.mem_biUnion.mp hv with ⟨a, _, ha⟩
          rcases Finset.mem_biUnion.mp ha with ⟨r, _, hr⟩
          exact hblk_in a r hr
        let rest : Finset (Fin m × Fin 3) := mon \ allGrp
        have hrest_card : rest.card = n - 3 * t * L := by
          rw [Finset.card_sdiff_of_subset hall_sub, hcard, hall_card]
        have hle_n : 3 * t * L ≤ n := by
          rw [← hcard, ← hall_card]; exact Finset.card_le_card hall_sub
        have hmon_grp : ∀ (a : Fin L) (y : (Fin m × Fin 3) → Bool),
            monEval (grpSet a) y = ∏ r : Fin t, monEval (block3 (blk a r)) y := by
          intro a y
          rw [monEval_eq_prod, Finset.prod_biUnion]
          · refine Finset.prod_congr rfl fun r _ => (monEval_eq_prod _ y).symm
          · intro r1 _ r2 _ hne
            exact disjoint_block3 fun h => hne (congrArg Prod.snd (hblk_inj (a₁ := (a, r1)) (a₂ := (a, r2)) h))
        have hmon_all : ∀ y : (Fin m × Fin 3) → Bool,
            monEval mon y = (∏ a : Fin L, monEval (grpSet a) y) * monEval rest y := by
          intro y
          have hun : allGrp ∪ rest = mon := Finset.union_sdiff_of_subset hall_sub
          rw [← hun, ← monEval_union]
          congr 1
          rw [monEval_eq_prod, Finset.prod_biUnion]
          · refine Finset.prod_congr rfl fun a _ => (monEval_eq_prod _ y).symm
          · intro a1 _ a2 _ hne; exact hgrp_disj a1 a2 hne
        let Qprod : ℕ → Fin L → ((Fin m × Fin 3) → Bool) → ZMod 2 :=
          fun p a y => ∏ r : Fin t, Q p a (blk a r) y
        have hQprod_deg : ∀ p a, HasDeg (2 * t) (Qprod p a) := fun p a => by
          have hsum : (∑ _r : Fin t, (2 : ℕ)) = 2 * t := by simp [mul_comm]
          dsimp only [Qprod]
          rw [← hsum]
          exact hasDeg_prod Finset.univ (fun _ => 2) (fun r y => Q p a (blk a r) y)
            (fun r _ => hQ p a (blk a r))
        let remPoly : ((Fin m × Fin 3) → Bool) → ZMod 2 := fun y =>
          ∑ p ∈ Finset.range (2 ^ d),
            pathInd d ask p y *
              (∑ J ∈ (Finset.univ : Finset (Fin L)).powerset.erase ∅,
                (∏ a ∈ Finset.univ \ J, monEval (grpSet a) y) * (∏ a ∈ J, Qprod p a y)) *
              monEval rest y
        have hrem_eq : ∀ y ∈ S, monEval mon y = remPoly y := by
          intro y hy
          have hy_ex : ∃ a0 : Fin L, ∀ i : Fin m, monEval (block3 i) y = Q (runFn d ask y) a0 i y :=
            (Finset.mem_filter.mp hy).2
          have hvanish : ∀ p ∈ Finset.range (2 ^ d),
              pathInd d ask p y * (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) = 0 := by
            intro p hp
            rw [pathInd_eq d ask (Finset.mem_range.mp hp) y]
            by_cases hrun : runFn d ask y = p
            · simp only [hrun, ↓reduceIte, one_mul]
              rcases hy_ex with ⟨a0, ha0⟩
              refine Finset.prod_eq_zero (Finset.mem_univ a0) ?_
              rw [hmon_grp a0 y]
              have hpeq : (∏ r : Fin t, monEval (block3 (blk a0 r)) y) = Qprod p a0 y := by
                refine Finset.prod_congr rfl fun r _ => ?_
                rw [ha0 (blk a0 r), hrun]
              rw [hpeq, zmod2_add_self]
            · simp [hrun]
          have hexpand : ∀ p : ℕ,
              (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) =
              (∏ a : Fin L, monEval (grpSet a) y) +
                ∑ J ∈ (Finset.univ : Finset (Fin L)).powerset.erase ∅,
                  (∏ a ∈ Finset.univ \ J, monEval (grpSet a) y) * (∏ a ∈ J, Qprod p a y) := by
            intro p
            have hcomm : (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) =
                ∏ a : Fin L, (Qprod p a y + monEval (grpSet a) y) :=
              Finset.prod_congr rfl fun a _ => add_comm _ _
            rw [hcomm, Finset.prod_add]
            have hmem0 : (∅ : Finset (Fin L)) ∈ (Finset.univ : Finset (Fin L)).powerset :=
              Finset.empty_mem_powerset _
            rw [← Finset.add_sum_erase _ _ hmem0]
            simp only [Finset.sdiff_empty, Finset.prod_empty, one_mul]
            refine congrArg ((∏ a : Fin L, monEval (grpSet a) y) + ·) ?_
            refine Finset.sum_congr rfl fun J _ => mul_comm _ _
          have hsum0 : (∑ p ∈ Finset.range (2 ^ d),
              pathInd d ask p y * (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) * monEval rest y) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            rw [hvanish p hp, zero_mul]
          have hsum_ind : (∑ p ∈ Finset.range (2 ^ d), pathInd d ask p y) = 1 := by
            rw [Finset.sum_eq_single (runFn d ask y)]
            · rw [pathInd_eq d ask (runFn_lt d ask y) y]; simp
            · intro p hp hne
              rw [pathInd_eq d ask (Finset.mem_range.mp hp) y]; simp [Ne.symm hne]
            · intro hnot
              exact absurd (Finset.mem_range.mpr (runFn_lt d ask y)) hnot
          have hsplit : (∑ p ∈ Finset.range (2 ^ d),
              pathInd d ask p y * (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) * monEval rest y) =
              monEval mon y + remPoly y := by
            have h1 : (∑ p ∈ Finset.range (2 ^ d),
                pathInd d ask p y * (∏ a : Fin L, (monEval (grpSet a) y + Qprod p a y)) * monEval rest y) =
                (∑ p ∈ Finset.range (2 ^ d),
                  pathInd d ask p y * (∏ a : Fin L, monEval (grpSet a) y) * monEval rest y) +
                remPoly y := by
              dsimp only [remPoly]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [hexpand p, mul_add, add_mul]
            rw [h1]
            refine congrArg (· + remPoly y) ?_
            rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_ind, one_mul, hmon_all y]
          rw [hsplit] at hsum0
          exact (zmod2_add_eq_zero_iff _ _).mp hsum0
        have hrem_deg : HasDeg (n - 1) remPoly := by
          refine hasDeg_sum (Finset.range (2 ^ d)) _ fun p _ => ?_
          have hterm : (fun y => pathInd d ask p y *
              (∑ J ∈ (Finset.univ : Finset (Fin L)).powerset.erase ∅,
                (∏ a ∈ Finset.univ \ J, monEval (grpSet a) y) * (∏ a ∈ J, Qprod p a y)) *
              monEval rest y) =
              (fun y => ∑ J ∈ (Finset.univ : Finset (Fin L)).powerset.erase ∅,
                pathInd d ask p y *
                  ((∏ a ∈ Finset.univ \ J, monEval (grpSet a) y) * (∏ a ∈ J, Qprod p a y)) *
                  monEval rest y) := by
            funext y
            rw [Finset.mul_sum, Finset.sum_mul]
          rw [hterm]
          refine hasDeg_sum _ _ fun J hJ => ?_
          have hJne : J ≠ ∅ := (Finset.mem_erase.mp hJ).1
          have hJpos : 1 ≤ J.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hJne)
          have hJle : J.card ≤ L := by
            calc J.card ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_le_univ J
              _ = L := Finset.card_fin L
          have hd1 : HasDeg (b * d) (pathInd d ask p) := pathInd_hasDeg b d ask hask p
          have hd2 : HasDeg (3 * t * (L - J.card)) (fun y => ∏ a ∈ Finset.univ \ J, monEval (grpSet a) y) := by
            have hs : (∑ a ∈ Finset.univ \ J, (grpSet a).card) = 3 * t * (L - J.card) := by
              simp [hgrp_card, Finset.card_sdiff_of_subset (Finset.subset_univ J), mul_comm]
            rw [← hs]
            exact hasDeg_prod (Finset.univ \ J) (fun a => (grpSet a).card)
              (fun a y => monEval (grpSet a) y) (fun a _ => hasDeg_monEval (grpSet a))
          have hd3 : HasDeg (2 * t * J.card) (fun y => ∏ a ∈ J, Qprod p a y) := by
            have hs : (∑ _a ∈ J, 2 * t) = 2 * t * J.card := by simp [mul_comm]
            rw [← hs]
            exact hasDeg_prod J (fun _ => 2 * t) (fun a y => Qprod p a y) (fun a _ => hQprod_deg p a)
          have hd4 : HasDeg rest.card (fun y => monEval rest y) := hasDeg_monEval rest
          have hprod := hasDeg_mul (hasDeg_mul hd1 (hasDeg_mul hd2 hd3)) hd4
          have hdeg_le : b * d + (3 * t * (L - J.card) + 2 * t * J.card) + rest.card ≤ n - 1 := by
            rw [hrest_card]
            have hmul1 : 3 * t * (L - J.card) + 3 * t * J.card = 3 * t * L := by
              rw [← mul_add, Nat.sub_add_cancel hJle]
            have hmul2 : t * 1 ≤ t * J.card := Nat.mul_le_mul_left t hJpos
            have hmul3 : 3 * t * J.card = 2 * t * J.card + t * J.card := by ring
            omega
          exact hasDeg_mono hdeg_le hprod
        rcases hrem_deg with ⟨cR, hcR_deg, hcR_eval⟩
        have hpos_n : 1 ≤ n := by
          have : 1 ≤ L := Nat.pos_of_ne_zero hL0
          have : 1 ≤ t := by omega
          nlinarith
        have hchoose : ∀ s : Finset (Fin m × Fin 3),
            ∃ cs : Finset (Fin m × Fin 3) → ZMod 2,
              (∀ u, u ∉ G → cs u = 0) ∧
              (cR s ≠ 0 → ∀ y ∈ S, monEval s y = polyEval cs y) := by
          intro s
          by_cases hne : cR s = 0
          · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => False.elim (h hne)⟩
          · have hlt : s.card < n := by
              have := hcR_deg s hne; omega
            rcases ih s.card hlt s rfl with ⟨cs, hcsG, hcsEq⟩
            exact ⟨cs, hcsG, fun _ => hcsEq⟩
        choose cs hcsG hcsEq using hchoose
        refine ⟨fun u => ∑ s : Finset (Fin m × Fin 3), cR s * cs s u, ?_, fun y hy => ?_⟩
        · intro u hu
          refine Finset.sum_eq_zero fun s _ => ?_
          rw [hcsG s u hu, mul_zero]
        · rw [hrem_eq y hy, hcR_eval y]
          unfold polyEval
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          by_cases h0 : cR s = 0
          · simp [h0]
          · rw [hcsEq s h0 y hy]
            unfold polyEval
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ => by ring
  let evalS : ({s : Finset (Fin m × Fin 3) // s ∈ G} → ZMod 2) →
      ({y : (Fin m × Fin 3) → Bool // y ∈ S} → ZMod 2) :=
    fun d y => ∑ s : {s : Finset (Fin m × Fin 3) // s ∈ G}, d s * monEval s.1 y.1
  have hsurj : Function.Surjective evalS := by
    intro f
    let fExt : ((Fin m × Fin 3) → Bool) → ZMod 2 := fun y => if hy : y ∈ S then f ⟨y, hy⟩ else 0
    rcases polyEval_surjective (Fin m × Fin 3) fExt with ⟨c0, hc0⟩
    choose cm hcmG hcmEq using (fun mon : Finset (Fin m × Fin 3) => hmon_span mon.card mon rfl)
    refine ⟨fun s => ∑ mon : Finset (Fin m × Fin 3), c0 mon * cm mon s.1, ?_⟩
    funext ⟨y, hy⟩
    have hfval : f ⟨y, hy⟩ = polyEval c0 y := by
      have := congrFun hc0 y
      simp only [fExt, hy, ↓reduceDIte] at this
      exact this.symm
    rw [hfval]
    unfold polyEval
    dsimp only [evalS]
    have hstep1 : (∑ mon : Finset (Fin m × Fin 3), c0 mon * monEval mon y) =
        ∑ mon : Finset (Fin m × Fin 3), c0 mon * ∑ s ∈ G, cm mon s * monEval s y := by
      refine Finset.sum_congr rfl fun mon _ => ?_
      rw [hcmEq mon y hy]
      congr 1
      unfold polyEval
      symm
      refine Finset.sum_subset (Finset.subset_univ G) fun s _ hs => ?_
      rw [hcmG mon s hs, zero_mul]
    rw [hstep1]
    have hstep2 :
        (∑ s : {s : Finset (Fin m × Fin 3) // s ∈ G},
          (∑ mon : Finset (Fin m × Fin 3), c0 mon * cm mon s.1) * monEval s.1 y) =
        ∑ s ∈ G, (∑ mon : Finset (Fin m × Fin 3), c0 mon * cm mon s) * monEval s y :=
      Finset.sum_coe_sort G (fun s =>
        (∑ mon : Finset (Fin m × Fin 3), c0 mon * cm mon s) * monEval s y)
    rw [hstep2]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun mon _ => Finset.sum_congr rfl fun s _ => by ring
  have hcard_le : Fintype.card ({y : (Fin m × Fin 3) → Bool // y ∈ S} → ZMod 2) ≤
      Fintype.card ({s : Finset (Fin m × Fin 3) // s ∈ G} → ZMod 2) :=
    Fintype.card_le_of_surjective evalS hsurj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe] at hcard_le
  have hScard : S.card ≤ G.card :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard_le
  rwa [hGcard] at hScard

private lemma slice_full_implies_m_lt_N {m N : ℕ}
    (Q : Fin N → Fin m → ((Fin m × Fin 3) → Bool) → ZMod 2)
    (hQ : ∀ u i, HasDeg 2 (Q u i))
    (hcover : ∀ y : (Fin m × Fin 3) → Bool, ∃ u : Fin N, ∀ i : Fin m, monEval (block3 i) y = Q u i y) :
    m + 1 ≤ N := by
  classical
  by_contra hlt
  have hNm : N ≤ m := by omega
  let idx : Fin N → Fin m := fun u => ⟨u.val, lt_of_lt_of_le u.isLt hNm⟩
  have hidx_inj : Function.Injective idx := fun u1 u2 h => Fin.ext (congrArg (Fin.val : Fin m → ℕ) h)
  let topMon : Finset (Fin m × Fin 3) := (Finset.univ : Finset (Fin N)).biUnion (fun u => block3 (idx u))
  have htop_card : topMon.card = 3 * N := by
    rw [Finset.card_biUnion]
    · simp [card_block3, mul_comm]
    · intro u1 _ u2 _ hne
      exact disjoint_block3 (fun h => hne (hidx_inj h))
  have hprod0 : ∀ y : (Fin m × Fin 3) → Bool,
      (∏ u : Fin N, (monEval (block3 (idx u)) y + Q u (idx u) y)) = 0 := by
    intro y
    rcases hcover y with ⟨u, hu⟩
    refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
    rw [hu (idx u), zmod2_add_self]
  let remPoly : ((Fin m × Fin 3) → Bool) → ZMod 2 := fun y =>
    ∑ J ∈ (Finset.univ : Finset (Fin N)).powerset.erase ∅,
      (∏ u ∈ Finset.univ \ J, monEval (block3 (idx u)) y) * (∏ u ∈ J, Q u (idx u) y)
  have htop_eq : ∀ y : (Fin m × Fin 3) → Bool, monEval topMon y = remPoly y := by
    intro y
    have h0 := hprod0 y
    have hcomm : (∏ u : Fin N, (monEval (block3 (idx u)) y + Q u (idx u) y)) =
        ∏ u : Fin N, (Q u (idx u) y + monEval (block3 (idx u)) y) :=
      Finset.prod_congr rfl fun u _ => add_comm _ _
    rw [hcomm, Finset.prod_add] at h0
    have hmem0 : (∅ : Finset (Fin N)) ∈ (Finset.univ : Finset (Fin N)).powerset :=
      Finset.empty_mem_powerset _
    rw [← Finset.add_sum_erase _ _ hmem0] at h0
    simp only [Finset.sdiff_empty, Finset.prod_empty, one_mul] at h0
    have htop_prod : (∏ u : Fin N, monEval (block3 (idx u)) y) = monEval topMon y := by
      symm
      rw [monEval_eq_prod, Finset.prod_biUnion]
      · refine Finset.prod_congr rfl fun u _ => (monEval_eq_prod _ y).symm
      · intro u1 _ u2 _ hne; exact disjoint_block3 (fun h => hne (hidx_inj h))
    rw [htop_prod] at h0
    have heq_rem : (∑ x ∈ (Finset.univ : Finset (Fin N)).powerset.erase ∅,
        (∏ i ∈ x, Q i (idx i) y) * ∏ i ∈ Finset.univ \ x, monEval (block3 (idx i)) y) = remPoly y := by
      refine Finset.sum_congr rfl fun J _ => mul_comm _ _
    rw [heq_rem] at h0
    exact (zmod2_add_eq_zero_iff _ _).mp h0
  have hrem_deg : HasDeg (3 * N - 1) remPoly := by
    refine hasDeg_sum _ _ fun J hJ => ?_
    have hJne : J ≠ ∅ := (Finset.mem_erase.mp hJ).1
    have hJpos : 1 ≤ J.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hJne)
    have hJle : J.card ≤ N := by
      calc J.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ J
        _ = N := Finset.card_fin N
    have hd1 : HasDeg (3 * (N - J.card)) (fun y => ∏ u ∈ Finset.univ \ J, monEval (block3 (idx u)) y) := by
      have hs : (∑ u ∈ Finset.univ \ J, (block3 (idx u)).card) = 3 * (N - J.card) := by
        simp [card_block3, Finset.card_sdiff_of_subset (Finset.subset_univ J), mul_comm]
      rw [← hs]
      exact hasDeg_prod (Finset.univ \ J) (fun u => (block3 (idx u)).card)
        (fun u y => monEval (block3 (idx u)) y) (fun u _ => hasDeg_monEval (block3 (idx u)))
    have hd2 : HasDeg (2 * J.card) (fun y => ∏ u ∈ J, Q u (idx u) y) := by
      have hs : (∑ _u ∈ J, (2 : ℕ)) = 2 * J.card := by simp [mul_comm]
      rw [← hs]
      exact hasDeg_prod J (fun _ => 2) (fun u y => Q u (idx u) y) (fun u _ => hQ u (idx u))
    have hmul := hasDeg_mul hd1 hd2
    have hle : 3 * (N - J.card) + 2 * J.card ≤ 3 * N - 1 := by omega
    exact hasDeg_mono hle hmul
  have hNpos : 1 ≤ N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    subst hN0
    rcases hcover (fun _ => false) with ⟨u, _⟩
    exact u.elim0
  have hmon_poly : (fun y => monEval topMon y) = polyEval (fun s => if s = topMon then 1 else 0) := by
    funext y
    unfold polyEval
    rw [Finset.sum_eq_single topMon]
    · simp
    · intro s _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ topMon) hnot
  have hdeg_top : HasDeg (3 * N - 1) (polyEval (fun s => if s = topMon then 1 else 0)) := by
    rw [← hmon_poly]
    have hfeq : (fun y => monEval topMon y) = remPoly := funext htop_eq
    rw [hfeq]
    exact hrem_deg
  have h0 := hasDeg_coeff_zero_of_lt hdeg_top (mon := topMon) (by rw [htop_card]; omega)
  simp at h0

private lemma choose_pow2_mod2_iff (q N : ℕ) (hq : q ≤ 2) (hN : N < 2 * 2 ^ q) :
    Nat.choose N (2 ^ q) % 2 = 1 ↔ 2 ^ q ≤ N := by
  interval_cases q
  · interval_cases N <;> decide
  · interval_cases N <;> decide
  · interval_cases N <;> decide

private lemma elemSym_eq_choose_zmod2 {s : ℕ} (K : ℕ) (ind : Fin s → Bool) :
    (∑ A ∈ (Finset.univ : Finset (Fin s)).powersetCard K, ∏ r ∈ A, toZ2 (ind r)) =
      ((Nat.choose ((Finset.univ : Finset (Fin s)).filter (fun r => ind r = true)).card K : ℕ) : ZMod 2) := by
  classical
  set T := (Finset.univ : Finset (Fin s)).filter (fun r => ind r = true)
  have hterm : ∀ A : Finset (Fin s),
      (∏ r ∈ A, toZ2 (ind r)) = if A ⊆ T then (1 : ZMod 2) else 0 := by
    intro A
    by_cases hsub : A ⊆ T
    · simp only [hsub, ↓reduceIte]
      refine Finset.prod_eq_one fun r hr => ?_
      have ht : ind r = true := (Finset.mem_filter.mp (hsub hr)).2
      rw [ht]; rfl
    · simp only [hsub, ↓reduceIte]
      have hex : ∃ r ∈ A, ind r = false := by
        by_contra hall
        push Not at hall
        apply hsub
        intro r hr
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
        cases h : ind r
        · exact absurd h (hall r hr)
        · rfl
      rcases hex with ⟨r, hrA, hrf⟩
      refine Finset.prod_eq_zero hrA ?_
      rw [hrf]; rfl
  rw [Finset.sum_congr rfl (fun A _ => hterm A)]
  have hfilt : ((Finset.univ : Finset (Fin s)).powersetCard K).filter (fun A => A ⊆ T) =
      T.powersetCard K := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [← Finset.sum_filter, hfilt, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one]

private lemma upper_deg_bound {a c ℓ : ℕ} (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hc : c ≤ a) (hℓ : ℓ < c) :
    2 ^ (c - ℓ - 1) * (ℓ + 1) ≤ 2 ^ (a - 1) := by
  have hc3 : c ≤ 3 := by omega
  interval_cases a <;> interval_cases c <;> interval_cases ℓ <;> decide

private lemma deg2_cancel_cube {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v w aff : (ι → Bool) → ZMod 2) (p0 p1 p2 : ZMod 2)
    (hu : HasDeg 1 u) (hv : HasDeg 1 v) (hw : HasDeg 1 w) (haff : HasDeg 1 aff) :
    HasDeg 2 (fun x => u x * v x * w x +
      (u x + 1 + p0) * (v x + 1 + p1) * (w x + 1 + p2) + aff x) := by
  have heq : (fun x => u x * v x * w x +
      (u x + 1 + p0) * (v x + 1 + p1) * (w x + 1 + p2) + aff x) =
      (fun x =>
        (1 + p2) * (u x * v x) + (1 + p1) * (u x * w x) + (1 + p0) * (v x * w x) +
        (1 + p1) * (1 + p2) * u x + (1 + p0) * (1 + p2) * v x + (1 + p0) * (1 + p1) * w x +
        (1 + p0) * (1 + p1) * (1 + p2) + aff x) := by
    funext x
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hring : u x * v x * w x + (u x + 1 + p0) * (v x + 1 + p1) * (w x + 1 + p2) + aff x =
        2 * (u x * v x * w x) +
        ((1 + p2) * (u x * v x) + (1 + p1) * (u x * w x) + (1 + p0) * (v x * w x) +
        (1 + p1) * (1 + p2) * u x + (1 + p0) * (1 + p2) * v x + (1 + p0) * (1 + p1) * w x +
        (1 + p0) * (1 + p1) * (1 + p2) + aff x) := by ring
    rw [hring, h2, zero_mul, zero_add]
  rw [heq]
  have h02 : ∀ a : ZMod 2, HasDeg 2 (fun _ : ι → Bool => a) := fun a =>
    hasDeg_mono (by omega) (hasDeg_const a)
  have hcmul : ∀ (c0 : ZMod 2) (f : (ι → Bool) → ZMod 2), HasDeg 2 f →
      HasDeg 2 (fun x => c0 * f x) := fun c0 f hf => by
    simpa only [zero_add] using hasDeg_mul (hasDeg_const c0) hf
  have h12 : ∀ f : (ι → Bool) → ZMod 2, HasDeg 1 f → HasDeg 2 f := fun f hf =>
    hasDeg_mono (by omega) hf
  refine hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add (hasDeg_add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact hcmul _ _ (hasDeg_mul hu hv)
  · exact hcmul _ _ (hasDeg_mul hu hw)
  · exact hcmul _ _ (hasDeg_mul hv hw)
  · exact hcmul _ _ (h12 _ hu)
  · exact hcmul _ _ (h12 _ hv)
  · exact hcmul _ _ (h12 _ hw)
  · exact h02 _
  · exact h12 _ haff

private lemma card_fiber_eq {k : ℕ} (pinC : Finset (Fin k)) (refBits : Fin k → Bool) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => ∀ c ∈ pinC, x c = refBits c)).card =
      2 ^ (k - pinC.card) := by
  classical
  let e : {x : Fin k → Bool // ∀ c ∈ pinC, x c = refBits c} ≃ ({c : Fin k // c ∉ pinC} → Bool) :=
    { toFun := fun ⟨x, _⟩ ⟨c, _⟩ => x c
      invFun := fun g => ⟨fun c => if hc : c ∈ pinC then refBits c else g ⟨c, hc⟩, fun c hc => by simp [hc]⟩
      left_inv := fun ⟨x, hx⟩ => by
        ext c
        by_cases hc : c ∈ pinC
        · simp [hc, hx c hc]
        · simp [hc]
      right_inv := fun g => by
        funext ⟨c, hc⟩
        simp [hc] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

private lemma card_mul_eight_pow_le {k m : ℕ} (pinC : Finset (Fin k)) (refBits : Fin k → Bool)
    (coord : Fin m × Fin 3 → Fin k) (hcoord_inj : Function.Injective coord)
    (hcoord_free : ∀ p, coord p ∉ pinC)
    (P : (Fin k → Bool) → Prop) [DecidablePred P] (count : ℕ)
    (hslice : ∀ ext : ({c : Fin k // c ∉ pinC ∧ c ∉ Set.range coord} → Bool),
      ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter (fun y =>
        P (fun c =>
          if hc : c ∈ pinC then refBits c
          else if hr : c ∈ Set.range coord then y (Classical.choose hr)
          else ext ⟨c, hc, hr⟩))).card ≤ count) :
    8 ^ m * ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun x => (∀ c ∈ pinC, x c = refBits c) ∧ P x)).card ≤
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => ∀ c ∈ pinC, x c = refBits c)).card * count := by
  classical
  let Ext := {c : Fin k // c ∉ pinC ∧ c ∉ Set.range coord} → Bool
  let emb : Ext × ((Fin m × Fin 3) → Bool) → (Fin k → Bool) := fun ⟨ext, y⟩ c =>
    if hc : c ∈ pinC then refBits c
    else if hr : c ∈ Set.range coord then y (Classical.choose hr)
    else ext ⟨c, hc, hr⟩
  have hemb_pin : ∀ p, ∀ c ∈ pinC, emb p c = refBits c := fun ⟨ext, y⟩ c hc => by
    simp [emb, hc]
  have hemb_coord : ∀ ext y q, emb (ext, y) (coord q) = y q := fun ext y q => by
    have hnot : coord q ∉ pinC := hcoord_free q
    have hmem : coord q ∈ Set.range coord := ⟨q, rfl⟩
    simp only [emb, hnot, ↓reduceDIte, hmem]
    have hch : Classical.choose hmem = q := hcoord_inj (Classical.choose_spec hmem)
    rw [hch]
  let e : {x : Fin k → Bool // ∀ c ∈ pinC, x c = refBits c} ≃ Ext × ((Fin m × Fin 3) → Bool) :=
    { toFun := fun ⟨x, _⟩ => (fun c => x c.1, fun q => x (coord q))
      invFun := fun p => ⟨emb p, hemb_pin p⟩
      left_inv := fun ⟨x, hx⟩ => by
        ext c
        dsimp only [emb]
        by_cases hc : c ∈ pinC
        · simp [hc, hx c hc]
        · by_cases hr : c ∈ Set.range coord
          · simp only [hc, hr, ↓reduceDIte]
            rw [Classical.choose_spec hr]
          · simp [hc, hr]
      right_inv := fun ⟨ext, y⟩ => by
        ext c
        · dsimp only [emb]
          simp [c.2.1, c.2.2]
        · exact hemb_coord ext y c }
  have hfib_card : ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => ∀ c ∈ pinC, x c = refBits c)).card =
      Fintype.card Ext * 8 ^ m := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod]
    congr 1
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      mul_comm, pow_mul]
    rfl
  have hhit_card : ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun x => (∀ c ∈ pinC, x c = refBits c) ∧ P x)).card =
      ∑ ext : Ext, ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter (fun y => P (emb (ext, y)))).card := by
    have h1 : ((Finset.univ : Finset (Fin k → Bool)).filter
        (fun x => (∀ c ∈ pinC, x c = refBits c) ∧ P x)).card =
        Fintype.card {x : {x : Fin k → Bool // ∀ c ∈ pinC, x c = refBits c} // P x.1} := by
      rw [Fintype.card_subtype]
      let eSub : {x : Fin k → Bool // (∀ c ∈ pinC, x c = refBits c) ∧ P x} ≃
          {x : {x : Fin k → Bool // ∀ c ∈ pinC, x c = refBits c} // P x.1} :=
        { toFun := fun ⟨x, h1, h2⟩ => ⟨⟨x, h1⟩, h2⟩
          invFun := fun ⟨⟨x, h1⟩, h2⟩ => ⟨x, h1, h2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.card_subtype, Fintype.card_congr eSub]
      rw [Fintype.card_subtype]
    rw [h1]
    let e2 : {x : {x : Fin k → Bool // ∀ c ∈ pinC, x c = refBits c} // P x.1} ≃
        {p : Ext × ((Fin m × Fin 3) → Bool) // P (emb p)} :=
      { toFun := fun ⟨x, hx⟩ => ⟨e x, by
          have heq : emb (e x) = x.1 := congrArg Subtype.val (e.left_inv x)
          rwa [heq]⟩
        invFun := fun ⟨p, hp⟩ => ⟨e.symm p, hp⟩
        left_inv := fun ⟨x, _⟩ => Subtype.ext (e.left_inv x)
        right_inv := fun ⟨p, _⟩ => Subtype.ext (e.right_inv p) }
    rw [Fintype.card_congr e2, Fintype.card_subtype]
    rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun ext _ => ?_
    rw [Finset.card_filter]
  rw [hfib_card, hhit_card]
  have hsum_le : (∑ ext : Ext, ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter
      (fun y => P (emb (ext, y)))).card) ≤ Fintype.card Ext * count := by
    calc ∑ ext : Ext, ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter
            (fun y => P (emb (ext, y)))).card
        ≤ ∑ _ext : Ext, count := Finset.sum_le_sum fun ext _ => hslice ext
      _ = Fintype.card Ext * count := by simp
  calc 8 ^ m * ∑ ext : Ext, ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter
          (fun y => P (emb (ext, y)))).card
      ≤ 8 ^ m * (Fintype.card Ext * count) := Nat.mul_le_mul_left _ hsum_le
    _ = Fintype.card Ext * 8 ^ m * count := by ring

private lemma count_lt_eight_pow_of_le (m T : ℕ) (hT : T ≤ m) :
    (Finset.range (m + 1)).sum (fun filled =>
      if filled < T then Nat.choose m filled * 7 ^ (m - filled) else 0) < 8 ^ m := by
  have hbinom : (Finset.range (m + 1)).sum (fun filled => Nat.choose m filled * 7 ^ (m - filled)) = 8 ^ m := by
    have h := add_pow (1 : ℕ) 7 m
    simp only [one_pow, one_mul] at h
    have h8 : (1 + 7 : ℕ) = 8 := rfl
    rw [h8] at h
    rw [h]
    refine Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [← hbinom]
  refine Finset.sum_lt_sum ?_ ?_
  · intro f _
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  · refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), ?_⟩
    have hnot : ¬ m < T := by omega
    simp [hnot]

end PEqualNP.Outside.L_meta_25688_aux

theorem PEqualNP.Outside.L_meta_25688 : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k) →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, bit row.val 0 keyWord.val z.val = bit row.val 0 ref.val z.val)
  let deg := fun (u : Nat) (f : K → Bool) =>
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) =>
    (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
  let out := fun (input : K) (i : Fin m) => bit row.val 2 input.val (starts i+5)
  (∀ (b d L : Nat) (ask : Nat → Nat → K → Bool) (leaf : Nat → Fin L → Fin m → K → Bool),
    (∀ (u : Fin d) (path : Nat), deg b (ask u.val path)) →
    (∀ path a i, deg 2 (leaf path a i)) →
    let hit := fiber.filter (fun sample => ∃ a, ∀ i, leaf (run d ask sample) a i sample = out sample i)
    let count := (Finset.range (m+1)).sum (fun filled =>
      if filled < L*(b*d+1) then Nat.choose m filled * 7^(m-filled) else 0)
    8^m * hit.card ≤ fiber.card * count ∧
    (hit = fiber → m+1 ≤ L*2^d ∧ m < L*(b*d+1))) ∧
  ∀ a : Nat, 1 ≤ a → a ≤ 3 →
    let size := 2^a-1
    let steps := a*(m/size) + Nat.clog 2 (m%size+1)
    ∃ (choose : Nat → Nat → K → Bool) (pred : Nat → Fin m → K → Bool),
      (∀ (level : Fin steps) (path : Nat), deg (2^(a-1)) (choose level.val path)) ∧
      (∀ path i, deg 2 (pred path i)) ∧
      ∀ x ∈ fiber, ∀ i, pred (run steps choose x) i x = out x i := by
  classical
  intro k hk constant rot step state injected bit m starts hinj good row ref hgood pin hpin hfree
    K bitOf par fiber deg run out
  have href_fib : ref ∈ fiber := Finset.mem_filter.mpr ⟨Finset.mem_univ ref, fun _ _ => rfl⟩
  have hfib_pos : 0 < fiber.card := Finset.card_pos.mpr ⟨ref, href_fib⟩
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨?_, ?_⟩
    · intro b d L ask leaf _ _ hit count
      have hsub : hit ⊆ fiber := Finset.filter_subset _ _
      have hcard_le : hit.card ≤ fiber.card := Finset.card_le_card hsub
      refine ⟨?_, ?_⟩
      · by_cases hL0 : L = 0
        · subst hL0
          have hemp : hit = ∅ := by
            ext x
            simp only [hit, Finset.mem_filter, Finset.notMem_empty, iff_false]
            rintro ⟨_, a, _⟩; exact a.elim0
          rw [hemp, Finset.card_empty, mul_zero]; exact Nat.zero_le _
        · have hpos : 0 < L * (b * d + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hL0) (by omega)
          have hcnt : count = 1 := by simp [count, hpos]
          rw [hcnt]; simpa using hcard_le
      · intro heq
        have hne : hit.Nonempty := by rw [heq]; exact ⟨ref, href_fib⟩
        rcases hne with ⟨x, hx⟩
        rcases (Finset.mem_filter.mp hx).2 with ⟨a0, _⟩
        have hLpos : 1 ≤ L := Nat.pos_of_ne_zero (by intro h0; subst h0; exact a0.elim0)
        have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
        exact ⟨by nlinarith, Nat.mul_pos hLpos (Nat.succ_pos _)⟩
    · intro a ha1 _ size steps
      have hsize : 1 ≤ size := by
        have : 2 ≤ 2 ^ a := by calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha1
        omega
      have hsteps : steps = 0 := by simp [steps]
      refine ⟨fun _ _ _ => false, fun _ i => i.elim0, ?_, ?_, ?_⟩
      · intro level _; rw [hsteps] at level; exact level.elim0
      · intro _ i; exact i.elim0
      · intro _ _ i; exact i.elim0
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hk12 : 12 ≤ k := by
      let f : Fin m × Fin 12 → Fin k := fun z => ⟨(starts z.1 + z.2.val) % k, Nat.mod_lt _ hk⟩
      have hfinj : Function.Injective f := fun z1 z2 h => hinj (congrArg Fin.val h)
      have hle := Fintype.card_le_of_injective f hfinj
      simp only [Fintype.card_prod, Fintype.card_fin] at hle
      nlinarith
    have hk3 : 3 ≤ k := by omega
    have hk2 : 2 ≤ k := by omega
    let shiftBack : Fin k → Fin k := fun z => ⟨(z.val + k - 1) % k, Nat.mod_lt _ hk⟩
    have hshift_inj : Function.Injective shiftBack := by
      intro z1 z2 h
      have hv := congrArg Fin.val h
      dsimp only [shiftBack] at hv
      have h1 : (z1.val + k - 1) % k = if z1.val = 0 then k - 1 else z1.val - 1 := by
        by_cases h0 : z1.val = 0
        · simp [h0, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        · simp only [h0, ↓reduceIte]
          rw [show z1.val + k - 1 = (z1.val - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
      have h2 : (z2.val + k - 1) % k = if z2.val = 0 then k - 1 else z2.val - 1 := by
        by_cases h0 : z2.val = 0
        · simp [h0, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        · simp only [h0, ↓reduceIte]
          rw [show z2.val + k - 1 = (z2.val - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
      rw [h1, h2] at hv
      ext
      split_ifs at hv <;> omega
    let pinC : Finset (Fin k) := pin.image shiftBack
    have hfib_iff : ∀ keyWord : K, keyWord ∈ fiber ↔
        ∀ c ∈ pinC, bitOf keyWord c = bitOf ref c := by
      intro keyWord
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, pinC, Finset.mem_image]
      have hbit0 : ∀ (q : K) (z : Fin k),
          bit row.val 0 q.val z.val = xor (bitOf q (shiftBack z)) (row.val.testBit z.val) := by
        intro q z
        change PEqualNP.Outside.L_meta_25688_aux.bitFn k constant row.val 0 q.val z.val = _
        unfold PEqualNP.Outside.L_meta_25688_aux.bitFn PEqualNP.Outside.L_meta_25688_aux.stateFn
        simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor, Nat.mod_eq_of_lt z.isLt]
        rw [PEqualNP.Outside.L_meta_25688_aux.testBit_rotFn hk q.isLt z.isLt,
          Nat.mod_eq_of_lt (by omega : 1 < k)]
      constructor
      · rintro h c ⟨z, hz, rfl⟩
        have h1 := h z hz
        rw [hbit0 keyWord z, hbit0 ref z] at h1
        apply PEqualNP.Outside.L_meta_25688_aux.toZ2_injective
        have h2 := congrArg PEqualNP.Outside.L_meta_25688_aux.toZ2 h1
        rw [PEqualNP.Outside.L_meta_25688_aux.toZ2_xor, PEqualNP.Outside.L_meta_25688_aux.toZ2_xor] at h2
        calc PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf keyWord (shiftBack z))
            = (PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf keyWord (shiftBack z)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (row.val.testBit z.val)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (row.val.testBit z.val) := by
                  rw [add_assoc, PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
          _ = (PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf ref (shiftBack z)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (row.val.testBit z.val)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (row.val.testBit z.val) := by rw [h2]
          _ = PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf ref (shiftBack z)) := by
                  rw [add_assoc, PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
      · intro h z hz
        rw [hbit0 keyWord z, hbit0 ref z, h (shiftBack z) ⟨z, hz, rfl⟩]
    let coord : Fin m × Fin 3 → Fin k := fun p => ⟨(starts p.1 + 8 + p.2.val) % k, Nat.mod_lt _ hk⟩
    have hcoord_shift : ∀ p : Fin m × Fin 3,
        coord p = shiftBack ⟨(starts p.1 + 9 + p.2.val) % k, Nat.mod_lt _ hk⟩ := by
      intro p
      ext
      dsimp only [coord, shiftBack]
      have hm1 := PEqualNP.Outside.L_meta_25688_aux.mod_sub_one hk2 (q := starts p.1 + 9 + p.2.val) (by omega)
      rw [Nat.mod_eq_of_lt (show 1 < k by omega)] at hm1
      rw [hm1]
      congr 1
      omega
    have hcoord_inj : Function.Injective coord := by
      intro p1 p2 heq
      rw [hcoord_shift p1, hcoord_shift p2] at heq
      have hv := congrArg Fin.val (hshift_inj heq)
      dsimp only at hv
      have h1 := hinj (a₁ := (p1.1, ⟨9 + p1.2.val, by omega⟩))
        (a₂ := (p2.1, ⟨9 + p2.2.val, by omega⟩)) (by
          dsimp only
          rwa [show starts p1.1 + (9 + p1.2.val) = starts p1.1 + 9 + p1.2.val by omega,
            show starts p2.1 + (9 + p2.2.val) = starts p2.1 + 9 + p2.2.val by omega])
      have hfst : p1.1 = p2.1 := congrArg (Prod.fst : Fin m × Fin 12 → Fin m) h1
      have hsnd : p1.2.val = p2.2.val := by
        have h2 := congrArg (fun z : Fin m × Fin 12 => z.2.val) h1
        dsimp only at h2
        omega
      exact Prod.ext hfst (Fin.ext hsnd)
    have hcoord_free : ∀ p : Fin m × Fin 3, coord p ∉ pinC := by
      intro p hmem
      rcases Finset.mem_image.mp hmem with ⟨z, hz, hzeq⟩
      rw [hcoord_shift p] at hzeq
      have h2 := congrArg Fin.val (hshift_inj hzeq)
      exact hfree p.1 p.2 z hz h2
    let oldRef : Fin m → ℕ → Bool := fun i j => bit row.val 0 ref.val (starts i + j)
    let αi : Fin m → Bool := fun i =>
      xor (xor (xor (oldRef i 5) (oldRef i 6)) (oldRef i 7)) (injected 1 ref.val (starts i + 6))
    let βi : Fin m → Bool := fun i =>
      xor (xor (xor (oldRef i 6) (oldRef i 7)) (oldRef i 8)) (injected 1 ref.val (starts i + 7))
    let c8i : Fin m → Bool := fun i =>
      xor (xor (xor (oldRef i 7) (oldRef i 8)) (row.val.testBit ((starts i + 9) % k)))
        ((constant 1).val.testBit ((starts i + 8) % k))
    let di : Fin m → Bool := fun i => xor (xor (αi i) (βi i)) (c8i i)
    let c2i : Fin m → Bool := fun i => injected 2 ref.val (starts i + 5)
    let s0i : Fin m → Bool := fun i =>
      xor (xor (oldRef i 7) (oldRef i 8)) (row.val.testBit ((starts i + 9) % k))
    let s1i : Fin m → Bool := fun i =>
      xor (xor (xor (oldRef i 8) (row.val.testBit ((starts i + 9) % k)))
        (row.val.testBit ((starts i + 10) % k))) true
    let s2i : Fin m → Bool := fun i =>
      xor (xor (xor (xor (row.val.testBit ((starts i + 9) % k)) (row.val.testBit ((starts i + 10) % k)))
        (row.val.testBit ((starts i + 11) % k))) (di i)) true
    let U' : Fin m → (Fin k → Bool) → Bool := fun i x => xor (x (coord (i, 0))) (s0i i)
    let V' : Fin m → (Fin k → Bool) → Bool := fun i x =>
      xor (xor (x (coord (i, 0))) (x (coord (i, 1)))) (s1i i)
    let W' : Fin m → (Fin k → Bool) → Bool := fun i x =>
      xor (xor (xor (x (coord (i, 0))) (x (coord (i, 1)))) (x (coord (i, 2)))) (s2i i)
    let aff : Fin m → (Fin k → Bool) → Bool := fun i x =>
      xor (xor (U' i x) (!(di i) && V' i x)) (xor (di i) (c2i i))
    have hU'_deg : ∀ i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
        (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i x)) := fun i => by
      have h : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i x)) =
          (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 0))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (s0i i)) := by
        funext x; exact PEqualNP.Outside.L_meta_25688_aux.toZ2_xor _ _
      rw [h]
      exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 0)))
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
    have hV'_deg : ∀ i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
        (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i x)) := fun i => by
      have h : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i x)) =
          (fun x => (PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 0))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 1)))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (s1i i)) := by
        funext x; simp only [V', PEqualNP.Outside.L_meta_25688_aux.toZ2_xor]
      rw [h]
      exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 0)))
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 1))))
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
    have hW'_deg : ∀ i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
        (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (W' i x)) := fun i => by
      have h : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (W' i x)) =
          (fun x => ((PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 0))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 1)))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (x (coord (i, 2)))) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (s2i i)) := by
        funext x; simp only [W', PEqualNP.Outside.L_meta_25688_aux.toZ2_xor]
      rw [h]
      exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 0)))
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 1))))
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (coord (i, 2))))
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
    have haff_deg : ∀ i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
        (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i x)) := fun i => by
      have h : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i x)) =
          (fun x => (PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i x) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (!(di i)) *
              PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i x)) +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (xor (di i) (c2i i))) := by
        funext x; simp only [aff, PEqualNP.Outside.L_meta_25688_aux.toZ2_xor,
          PEqualNP.Outside.L_meta_25688_aux.toZ2_and]
      rw [h]
      exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add (hU'_deg i)
          (by simpa only [zero_add] using (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mul
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _) (hV'_deg i))))
        (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
    have hout_formula : ∀ x ∈ fiber, ∀ i : Fin m,
        out x i = xor (U' i (bitOf x) && V' i (bitOf x) && W' i (bitOf x)) (aff i (bitOf x)) := by
      intro x hx i
      have hpin_i : ∀ j : Fin 9,
          PEqualNP.Outside.L_meta_25688_aux.bitFn k constant row.val 0 x.val (starts i + j.val) =
          PEqualNP.Outside.L_meta_25688_aux.bitFn k constant row.val 0 ref.val (starts i + j.val) := by
        intro j
        rcases hpin i j with ⟨z, hz, hzv⟩
        have hfx := (Finset.mem_filter.mp hx).2 z hz
        change bit row.val 0 x.val (starts i + j.val) = bit row.val 0 ref.val (starts i + j.val)
        dsimp only [bit]
        rw [← hzv, ← Nat.mod_eq_of_lt z.isLt]
        exact hfx
      have htr := PEqualNP.Outside.L_meta_25688_aux.twoRound_formula hk3 constant row ref x
        (starts i) hpin_i (hgood i)
      dsimp only [out]
      change PEqualNP.Outside.L_meta_25688_aux.bitFn k constant row.val 2 x.val (starts i + 5) = _
      rw [htr]
      dsimp only [U', V', W', aff, bitOf, coord, s0i, s1i, s2i, di, αi, βi, c8i, c2i, oldRef]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero,
        show starts i + 8 + 1 = starts i + 9 by omega,
        show starts i + 8 + 2 = starts i + 10 by omega, Bool.xor_assoc]
      rfl
    refine ⟨?_, ?_⟩
    · intro b d L ask leaf hask hleaf hit count
      have hask_deg : ∀ (u : Fin d) (path : ℕ),
          PEqualNP.Outside.L_meta_25688_aux.HasDeg b
            (fun x : Fin k → Bool => PEqualNP.Outside.L_meta_25688_aux.toZ2
              (ask u.val path ((PEqualNP.Outside.L_meta_25688_aux.keyBitsEquiv k).symm x))) :=
        fun u path => (PEqualNP.Outside.L_meta_25688_aux.deg_iff_hasDeg k b _).mp (hask u path)
      have hleaf_deg : ∀ path a i,
          PEqualNP.Outside.L_meta_25688_aux.HasDeg 2
            (fun x : Fin k → Bool => PEqualNP.Outside.L_meta_25688_aux.toZ2
              (leaf path a i ((PEqualNP.Outside.L_meta_25688_aux.keyBitsEquiv k).symm x))) :=
        fun path a i => (PEqualNP.Outside.L_meta_25688_aux.deg_iff_hasDeg k 2 _).mp (hleaf path a i)
      let eK := PEqualNP.Outside.L_meta_25688_aux.keyBitsEquiv k
      let Pbits : (Fin k → Bool) → Prop := fun x =>
        ∃ a : Fin L, ∀ i : Fin m,
          leaf (run d ask (eK.symm x)) a i (eK.symm x) = out (eK.symm x) i
      have hfib_bits : fiber.card =
          ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => ∀ c ∈ pinC, x c = bitOf ref c)).card := by
        rw [← Fintype.card_coe fiber, ← Fintype.card_subtype]
        refine Fintype.card_congr
          { toFun := fun ⟨q, hq⟩ => ⟨eK q, (hfib_iff q).mp hq⟩
            invFun := fun ⟨x, hx⟩ => ⟨eK.symm x, (hfib_iff _).mpr (by
              intro c hc
              have hb : bitOf (eK.symm x) c = x c := congrFun (eK.right_inv x) c
              rw [hb]; exact hx c hc)⟩
            left_inv := fun ⟨q, _⟩ => Subtype.ext (eK.left_inv q)
            right_inv := fun ⟨x, _⟩ => Subtype.ext (eK.right_inv x) }
      have hhit_bits : hit.card =
          ((Finset.univ : Finset (Fin k → Bool)).filter
            (fun x => (∀ c ∈ pinC, x c = bitOf ref c) ∧ Pbits x)).card := by
        rw [← Fintype.card_coe hit, ← Fintype.card_subtype]
        refine Fintype.card_congr
          { toFun := fun ⟨q, hq⟩ => ⟨eK q, (hfib_iff q).mp (Finset.mem_filter.mp hq).1, by
              rcases (Finset.mem_filter.mp hq).2 with ⟨a, ha⟩
              exact ⟨a, fun i => by rw [eK.symm_apply_apply q]; exact ha i⟩⟩
            invFun := fun ⟨x, hx1, hx2⟩ => ⟨eK.symm x, Finset.mem_filter.mpr ⟨(hfib_iff _).mpr (by
              intro c hc
              have hb : bitOf (eK.symm x) c = x c := congrFun (eK.right_inv x) c
              rw [hb]; exact hx1 c hc), hx2⟩⟩
            left_inv := fun ⟨q, _⟩ => Subtype.ext (eK.left_inv q)
            right_inv := fun ⟨x, _⟩ => Subtype.ext (eK.right_inv x) }
      let invMap : ((Fin m × Fin 3) → Bool) → ((Fin m × Fin 3) → Bool) := fun y p =>
        if p.2.val = 0 then xor (y (p.1, 0)) (s0i p.1)
        else if p.2.val = 1 then xor (xor (y (p.1, 0)) (y (p.1, 1))) (xor (s0i p.1) (s1i p.1))
        else xor (xor (y (p.1, 1)) (y (p.1, 2))) (xor (s1i p.1) (s2i p.1))
      let fwdMap : ((Fin m × Fin 3) → Bool) → ((Fin m × Fin 3) → Bool) := fun z p =>
        if p.2.val = 0 then xor (z (p.1, 0)) (s0i p.1)
        else if p.2.val = 1 then xor (xor (z (p.1, 0)) (z (p.1, 1))) (s1i p.1)
        else xor (xor (xor (z (p.1, 0)) (z (p.1, 1))) (z (p.1, 2))) (s2i p.1)
      have htri_l0 : ∀ a s0 : Bool, xor (xor a s0) s0 = a := by decide
      have htri_l1 : ∀ a b s0 s1 : Bool, xor (xor (xor a s0) (xor (xor a b) (xor s0 s1))) s1 = b := by decide
      have htri_l2 : ∀ a b c s0 s1 s2 : Bool,
          xor (xor (xor (xor a s0) (xor (xor a b) (xor s0 s1))) (xor (xor b c) (xor s1 s2))) s2 = c := by decide
      have htri_r1 : ∀ a b s0 s1 : Bool, xor (xor (xor a s0) (xor (xor a b) s1)) (xor s0 s1) = b := by decide
      have htri_r2 : ∀ a b c s1 s2 : Bool,
          xor (xor (xor (xor a b) s1) (xor (xor (xor a b) c) s2)) (xor s1 s2) = c := by decide
      have hinv_bi : Function.Bijective invMap := by
        refine Function.bijective_iff_has_inverse.mpr ⟨fwdMap, fun y => ?_, fun z => ?_⟩
        · funext ⟨i, j⟩
          fin_cases j
          · simp only [fwdMap, invMap]; exact htri_l0 _ _
          · simp only [fwdMap, invMap]; exact htri_l1 _ _ _ _
          · simp only [fwdMap, invMap]; exact htri_l2 _ _ _ _ _ _
        · funext ⟨i, j⟩
          fin_cases j
          · simp only [fwdMap, invMap]; exact htri_l0 _ _
          · simp only [fwdMap, invMap]; exact htri_r1 _ _ _ _
          · simp only [fwdMap, invMap]; exact htri_r2 _ _ _ _ _
      have hinv_deg : ∀ p : Fin m × Fin 3,
          PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
            (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y p)) := by
        rintro ⟨i, j⟩
        fin_cases j
        · change PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
            (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 0)))
          have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 0))) =
              (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 0)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (s0i i)) := by
            funext y
            change PEqualNP.Outside.L_meta_25688_aux.toZ2 (xor (y (i, 0)) (s0i i)) = _
            exact PEqualNP.Outside.L_meta_25688_aux.toZ2_xor _ _
          rw [h]
          exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (i, 0))
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
        · change PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
            (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 1)))
          have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 1))) =
              (fun y => (PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 0)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 1))) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (xor (s0i i) (s1i i))) := by
            funext y
            change PEqualNP.Outside.L_meta_25688_aux.toZ2
              (xor (xor (y (i, 0)) (y (i, 1))) (xor (s0i i) (s1i i))) = _
            rw [PEqualNP.Outside.L_meta_25688_aux.toZ2_xor, PEqualNP.Outside.L_meta_25688_aux.toZ2_xor]
          rw [h]
          exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (i, 0))
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (i, 1)))
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
        · change PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
            (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 2)))
          have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (i, 2))) =
              (fun y => (PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 1)) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 2))) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (xor (s1i i) (s2i i))) := by
            funext y
            change PEqualNP.Outside.L_meta_25688_aux.toZ2
              (xor (xor (y (i, 1)) (y (i, 2))) (xor (s1i i) (s2i i))) = _
            rw [PEqualNP.Outside.L_meta_25688_aux.toZ2_xor, PEqualNP.Outside.L_meta_25688_aux.toZ2_xor]
          rw [h]
          exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (i, 1))
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_var (i, 2)))
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
      have hbound : 8 ^ m * hit.card ≤ fiber.card * count := by
        rw [hfib_bits, hhit_bits]
        refine PEqualNP.Outside.L_meta_25688_aux.card_mul_eight_pow_le pinC (bitOf ref) coord
          hcoord_inj hcoord_free Pbits count ?_
        intro ext
        let emb0 : ((Fin m × Fin 3) → Bool) → (Fin k → Bool) := fun z c =>
          if hc : c ∈ pinC then bitOf ref c
          else if hr : c ∈ Set.range coord then z (Classical.choose hr)
          else ext ⟨c, hc, hr⟩
        let φ : ((Fin m × Fin 3) → Bool) → (Fin k → Bool) := fun y => emb0 (invMap y)
        have hφ_coord : ∀ y p, φ y (coord p) = invMap y p := by
          intro y p
          have hnot := hcoord_free p
          have hmem : coord p ∈ Set.range coord := ⟨p, rfl⟩
          simp only [φ, emb0, hnot, ↓reduceDIte, hmem]
          rw [hcoord_inj (Classical.choose_spec hmem)]
        have hφ_aff : ∀ c : Fin k, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
            (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) := by
          intro c
          by_cases hc : c ∈ pinC
          · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
                (fun _ => PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf ref c)) := by
              funext y; simp [φ, emb0, hc]
            rw [h]
            exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _)
          · by_cases hr : c ∈ Set.range coord
            · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
                  (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (Classical.choose hr))) := by
                funext y; simp only [φ, emb0, hc, hr, ↓reduceDIte]
              rw [h]
              exact hinv_deg (Classical.choose hr)
            · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
                  (fun _ => PEqualNP.Outside.L_meta_25688_aux.toZ2 (ext ⟨c, hc, hr⟩)) := by
                funext y; simp only [φ, emb0, hc, hr, ↓reduceDIte]
              rw [h]
              exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
                (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _)
        have hφ_UVW : ∀ y i, U' i (φ y) = y (i, 0) ∧ V' i (φ y) = y (i, 1) ∧ W' i (φ y) = y (i, 2) := by
          intro y i
          have hc0 := hφ_coord y (i, 0)
          have hc1 := hφ_coord y (i, 1)
          have hc2 := hφ_coord y (i, 2)
          dsimp only [U', V', W']
          rw [hc0, hc1, hc2]
          simp only [invMap]
          exact ⟨htri_l0 _ _, htri_l1 _ _ _ _, htri_l2 _ _ _ _ _ _⟩
        have hφ_fib : ∀ y, eK.symm (φ y) ∈ fiber := fun y => (hfib_iff _).mpr fun c hc => by
          have hb : bitOf (eK.symm (φ y)) c = φ y c := congrFun (eK.right_inv (φ y)) c
          rw [hb]; simp [φ, emb0, hc]
        let askY : ℕ → ℕ → ((Fin m × Fin 3) → Bool) → Bool := fun lv pt y => ask lv pt (eK.symm (φ y))
        let QY : ℕ → Fin L → Fin m → ((Fin m × Fin 3) → Bool) → ZMod 2 := fun pt a i y =>
          PEqualNP.Outside.L_meta_25688_aux.toZ2 (leaf pt a i (eK.symm (φ y))) +
          PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (φ y))
        have haskY : ∀ (u : Fin d) (path : ℕ),
            PEqualNP.Outside.L_meta_25688_aux.HasDeg b
              (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (askY u.val path y)) :=
          fun u path => PEqualNP.Outside.L_meta_25688_aux.hasDeg_comp_affine φ hφ_aff (hask_deg u path)
        have hQY : ∀ path a i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 2 (QY path a i) :=
          fun path a i => PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_comp_affine φ hφ_aff (hleaf_deg path a i))
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_comp_affine φ hφ_aff (haff_deg i)))
        have hcard_eq : ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter (fun z => Pbits (emb0 z))).card =
            ((Finset.univ : Finset ((Fin m × Fin 3) → Bool)).filter
              (fun y => ∃ a : Fin L, ∀ i : Fin m,
                PEqualNP.Outside.L_meta_25688_aux.monEval (PEqualNP.Outside.L_meta_25688_aux.block3 i) y =
                  QY (PEqualNP.Outside.L_meta_25688_aux.runFn d askY y) a i y)).card := by
          have hP_iff : ∀ y, Pbits (φ y) ↔ ∃ a : Fin L, ∀ i : Fin m,
              PEqualNP.Outside.L_meta_25688_aux.monEval (PEqualNP.Outside.L_meta_25688_aux.block3 i) y =
                QY (PEqualNP.Outside.L_meta_25688_aux.runFn d askY y) a i y := by
            intro y
            have hrun_eq : run d ask (eK.symm (φ y)) = PEqualNP.Outside.L_meta_25688_aux.runFn d askY y := rfl
            dsimp only [Pbits]
            rw [hrun_eq]
            refine exists_congr fun a => forall_congr' fun i => ?_
            have hout := hout_formula (eK.symm (φ y)) (hφ_fib y) i
            have hb_eq : bitOf (eK.symm (φ y)) = φ y := eK.right_inv (φ y)
            rw [hb_eq] at hout
            rcases hφ_UVW y i with ⟨hU, hV, hW⟩
            rw [hU, hV, hW] at hout
            rw [hout, PEqualNP.Outside.L_meta_25688_aux.monEval_block3 i y]
            dsimp only [QY]
            rw [← PEqualNP.Outside.L_meta_25688_aux.toZ2_eq_iff,
              PEqualNP.Outside.L_meta_25688_aux.toZ2_xor]
            constructor
            · intro h
              rw [h, add_assoc, PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
            · intro h
              calc PEqualNP.Outside.L_meta_25688_aux.toZ2
                    (leaf (PEqualNP.Outside.L_meta_25688_aux.runFn d askY y) a i (eK.symm (φ y)))
                  = (PEqualNP.Outside.L_meta_25688_aux.toZ2
                      (leaf (PEqualNP.Outside.L_meta_25688_aux.runFn d askY y) a i (eK.symm (φ y))) +
                      PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (φ y))) +
                      PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (φ y)) := by
                        rw [add_assoc, PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
                _ = PEqualNP.Outside.L_meta_25688_aux.toZ2 (y (i, 0) && y (i, 1) && y (i, 2)) +
                      PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (φ y)) := by rw [← h]
          rw [← Fintype.card_subtype, ← Fintype.card_subtype]
          let eI := Equiv.ofBijective invMap hinv_bi
          refine Fintype.card_congr
            { toFun := fun ⟨z, hz⟩ => ⟨eI.symm z, (hP_iff _).mp (by
                have : φ (eI.symm z) = emb0 z := by
                  dsimp only [φ]; rw [show invMap (eI.symm z) = eI (eI.symm z) from rfl, eI.apply_symm_apply]
                rwa [this])⟩
              invFun := fun ⟨y, hy⟩ => ⟨eI y, (hP_iff y).mpr hy⟩
              left_inv := fun ⟨z, _⟩ => Subtype.ext (eI.apply_symm_apply z)
              right_inv := fun ⟨y, _⟩ => Subtype.ext (eI.symm_apply_apply y) }
        rw [hcard_eq]
        exact PEqualNP.Outside.L_meta_25688_aux.slice_hit_le_count askY QY haskY hQY
      refine ⟨hbound, fun heq => ?_⟩
      have hcnt_ge : 8 ^ m ≤ count := by
        rw [heq] at hbound
        exact Nat.le_of_mul_le_mul_left (by nlinarith) hfib_pos
      have hm_lt : m < L * (b * d + 1) := by
        by_contra hle
        push Not at hle
        have hlt := PEqualNP.Outside.L_meta_25688_aux.count_lt_eight_pow_of_le m (L * (b * d + 1)) hle
        omega
      refine ⟨?_, hm_lt⟩
      let ext0 : {c : Fin k // c ∉ pinC ∧ c ∉ Set.range coord} → Bool := fun _ => false
      let emb0 : ((Fin m × Fin 3) → Bool) → (Fin k → Bool) := fun z c =>
        if hc : c ∈ pinC then bitOf ref c
        else if hr : c ∈ Set.range coord then z (Classical.choose hr)
        else ext0 ⟨c, hc, hr⟩
      let φ : ((Fin m × Fin 3) → Bool) → (Fin k → Bool) := fun y => emb0 (invMap y)
      have hφ_coord : ∀ y p, φ y (coord p) = invMap y p := by
        intro y p
        have hnot := hcoord_free p
        have hmem : coord p ∈ Set.range coord := ⟨p, rfl⟩
        simp only [φ, emb0, hnot, ↓reduceDIte, hmem]
        rw [hcoord_inj (Classical.choose_spec hmem)]
      have hφ_aff : ∀ c : Fin k, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
          (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) := by
        intro c
        by_cases hc : c ∈ pinC
        · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
              (fun _ => PEqualNP.Outside.L_meta_25688_aux.toZ2 (bitOf ref c)) := by
            funext y; simp [φ, emb0, hc]
          rw [h]
          exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _)
        · by_cases hr : c ∈ Set.range coord
          · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
                (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (invMap y (Classical.choose hr))) := by
              funext y; simp only [φ, emb0, hc, hr, ↓reduceDIte]
            rw [h]
            exact hinv_deg (Classical.choose hr)
          · have h : (fun y => PEqualNP.Outside.L_meta_25688_aux.toZ2 (φ y c)) =
                (fun _ => PEqualNP.Outside.L_meta_25688_aux.toZ2 (ext0 ⟨c, hc, hr⟩)) := by
              funext y; simp only [φ, emb0, hc, hr, ↓reduceDIte]
            rw [h]
            exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _)
      have hφ_UVW : ∀ y i, U' i (φ y) = y (i, 0) ∧ V' i (φ y) = y (i, 1) ∧ W' i (φ y) = y (i, 2) := by
        intro y i
        have hc0 := hφ_coord y (i, 0)
        have hc1 := hφ_coord y (i, 1)
        have hc2 := hφ_coord y (i, 2)
        dsimp only [U', V', W']
        rw [hc0, hc1, hc2]
        simp only [invMap]
        exact ⟨htri_l0 _ _, htri_l1 _ _ _ _, htri_l2 _ _ _ _ _ _⟩
      have hφ_fib : ∀ y, eK.symm (φ y) ∈ fiber := fun y => (hfib_iff _).mpr fun c hc => by
        have hb : bitOf (eK.symm (φ y)) c = φ y c := congrFun (eK.right_inv (φ y)) c
        rw [hb]; simp [φ, emb0, hc]
      let eN : Fin (L * 2 ^ d) ≃ Fin L × Fin (2 ^ d) :=
        (finProdFinEquiv (m := L) (n := 2 ^ d)).symm
      let Qflat : Fin (L * 2 ^ d) → Fin m → ((Fin m × Fin 3) → Bool) → ZMod 2 := fun u i y =>
        PEqualNP.Outside.L_meta_25688_aux.toZ2 (leaf (eN u).2.val (eN u).1 i (eK.symm (φ y))) +
        PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (φ y))
      have hQflat : ∀ u i, PEqualNP.Outside.L_meta_25688_aux.HasDeg 2 (Qflat u i) :=
        fun u i => PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_comp_affine φ hφ_aff
            (hleaf_deg (eN u).2.val (eN u).1 i))
          (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
            (PEqualNP.Outside.L_meta_25688_aux.hasDeg_comp_affine φ hφ_aff (haff_deg i)))
      have hcov : ∀ y : (Fin m × Fin 3) → Bool,
          ∃ u : Fin (L * 2 ^ d), ∀ i : Fin m,
            PEqualNP.Outside.L_meta_25688_aux.monEval (PEqualNP.Outside.L_meta_25688_aux.block3 i) y =
              Qflat u i y := by
        intro y
        have hy_hit : eK.symm (φ y) ∈ hit := by rw [heq]; exact hφ_fib y
        rcases (Finset.mem_filter.mp hy_hit).2 with ⟨a0, ha0⟩
        have hrun_lt : run d ask (eK.symm (φ y)) < 2 ^ d :=
          PEqualNP.Outside.L_meta_25688_aux.runFn_lt d ask (eK.symm (φ y))
        refine ⟨eN.symm (a0, ⟨run d ask (eK.symm (φ y)), hrun_lt⟩), fun i => ?_⟩
        dsimp only [Qflat]
        rw [eN.apply_symm_apply]
        have hout := hout_formula (eK.symm (φ y)) (hφ_fib y) i
        have hb_eq : bitOf (eK.symm (φ y)) = φ y := eK.right_inv (φ y)
        rw [hb_eq] at hout
        rcases hφ_UVW y i with ⟨hU, hV, hW⟩
        rw [hU, hV, hW] at hout
        have hi := ha0 i
        rw [hout, ← PEqualNP.Outside.L_meta_25688_aux.toZ2_eq_iff,
          PEqualNP.Outside.L_meta_25688_aux.toZ2_xor] at hi
        rw [PEqualNP.Outside.L_meta_25688_aux.monEval_block3 i y, hi, add_assoc,
          PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
      exact PEqualNP.Outside.L_meta_25688_aux.slice_full_implies_m_lt_N Qflat hQflat hcov
    · intro a ha1 ha3 size steps
      have hsize_pos : 0 < size := by
        have : 2 ≤ 2 ^ a := by calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha1
        omega
      set q := m / size
      set rem := m % size
      set crem := Nat.clog 2 (rem + 1)
      have hrem_lt : rem < size := Nat.mod_lt m hsize_pos
      have hcrem_le : crem ≤ a := by
        dsimp only [crem]
        exact Nat.clog_le_of_le_pow (by omega : rem + 1 ≤ 2 ^ a)
      have hrem_lt_pow : rem < 2 ^ crem := by
        have h1 : rem + 1 ≤ 2 ^ crem := Nat.le_pow_clog (by decide : 1 < 2) (rem + 1)
        omega
      let coord3 : Fin m → ℕ → (Fin k → Bool) → Bool := fun i j x =>
        match j with
        | 0 => U' i x
        | 1 => V' i x
        | _ => W' i x
      have hcoord3_deg : ∀ i j, PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
          (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 i j x)) := by
        intro i j
        cases j with
        | zero => exact hU'_deg i
        | succ j =>
          cases j with
          | zero => exact hV'_deg i
          | succ _ => exact hW'_deg i
      let grpSize : ℕ → ℕ := fun g => if g < q then size else if g = q then rem else 0
      let grpBits : ℕ → ℕ := fun g => if g < q then a else crem
      let grpBase : ℕ → ℕ := fun g => a * g
      let grpMem : (g : ℕ) → Fin (grpSize g) → Fin m := fun g r =>
        ⟨g * size + r.val, by
          by_cases hg : g < q
          · have h1 : (g + 1) * size ≤ q * size := Nat.mul_le_mul_right size (by omega)
            have h2 : q * size + rem = m := by
              rw [mul_comm]; exact Nat.div_add_mod m size
            have hr : r.val < size := by simpa [grpSize, hg] using r.isLt
            have hadd : g * size + size = (g + 1) * size := by ring
            omega
          · by_cases hgq : g = q
            · subst hgq
              have hr : r.val < rem := by simpa [grpSize, hg] using r.isLt
              have h2 : q * size + rem = m := by
                rw [mul_comm]; exact Nat.div_add_mod m size
              omega
            · have hr : r.val < 0 := by simpa [grpSize, hg, hgq] using r.isLt
              omega⟩
      let grpOfLevel : ℕ → ℕ := fun lv => if lv < a * q then lv / a else q
      let innerOfLevel : ℕ → ℕ := fun lv => if lv < a * q then lv % a else lv - a * q
      let matchPrefix : (g ℓ : ℕ) → ℕ → Fin (grpSize g) → (Fin k → Bool) → Bool :=
        fun g ℓ path r x =>
          decide ((∀ j : Fin ℓ, coord3 (grpMem g r) j.val x = path.testBit (grpBase g + j.val)) ∧
            coord3 (grpMem g r) ℓ x = false)
      let choose : ℕ → ℕ → K → Bool := fun lv path x =>
        let g := grpOfLevel lv
        let ℓ := innerOfLevel lv
        let c := grpBits g
        let Kth := 2 ^ (c - ℓ - 1)
        let cnt := ((Finset.univ : Finset (Fin (grpSize g))).filter
          (fun r => matchPrefix g ℓ path r (bitOf x) = true)).card
        decide (Nat.choose cnt Kth % 2 = 1)
      let eK := PEqualNP.Outside.L_meta_25688_aux.keyBitsEquiv k
      let predZ : ℕ → Fin m → (Fin k → Bool) → ZMod 2 := fun path i x =>
        let g := i.val / size
        let c := grpBits g
        let base := grpBase g
        let p0 := PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 0 < c then path.testBit (base + 0) else false)
        let p1 := PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 1 < c then path.testBit (base + 1) else false)
        let p2 := PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 2 < c then path.testBit (base + 2) else false)
        let u := PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i x)
        let v := PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i x)
        let w := PEqualNP.Outside.L_meta_25688_aux.toZ2 (W' i x)
        u * v * w + (u + 1 + p0) * (v + 1 + p1) * (w + 1 + p2) +
          PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i x)
      let pred : ℕ → Fin m → K → Bool := fun path i x => decide (predZ path i (bitOf x) = 1)
      have hpred_toZ2 : ∀ path i x,
          PEqualNP.Outside.L_meta_25688_aux.toZ2 (pred path i (eK.symm x)) = predZ path i x := by
        intro path i x
        dsimp only [pred]
        have hb : bitOf (eK.symm x) = x := eK.right_inv x
        rw [hb]
        rcases PEqualNP.Outside.L_meta_25688_aux.zmod2_eq_zero_or_one (predZ path i x) with h0 | h1
        · rw [h0]; decide
        · rw [h1]; decide
      refine ⟨choose, pred, ?_, ?_, ?_⟩
      · intro level path
        refine (PEqualNP.Outside.L_meta_25688_aux.deg_iff_hasDeg k (2 ^ (a - 1)) _).mpr ?_
        set g := grpOfLevel level.val
        set ℓ := innerOfLevel level.val
        set c := grpBits g
        have hℓc : ℓ < c := by
          by_cases hlt : level.val < a * q
          · have hg : g < q := by
              dsimp only [g, grpOfLevel]; simp only [hlt, ↓reduceIte]
              exact Nat.div_lt_of_lt_mul hlt
            have hce : c = a := by dsimp only [c, grpBits]; simp only [hg, ↓reduceIte]
            have hℓe : ℓ = level.val % a := by dsimp only [ℓ, innerOfLevel]; simp only [hlt, ↓reduceIte]
            rw [hce, hℓe]; exact Nat.mod_lt _ (by omega)
          · have hg : g = q := by dsimp only [g, grpOfLevel]; simp only [hlt, ↓reduceIte]
            have hce : c = crem := by dsimp only [c, grpBits]; simp only [hg, lt_irrefl, ↓reduceIte]
            have hℓe : ℓ = level.val - a * q := by dsimp only [ℓ, innerOfLevel]; simp only [hlt, ↓reduceIte]
            have hst : level.val < a * q + crem := level.isLt
            omega
        have hca : c ≤ a := by
          dsimp only [c, grpBits]; split_ifs
          · exact le_rfl
          · exact hcrem_le
        have hch_eq : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2
            (choose level.val path (eK.symm x))) =
            (fun x => ∑ A ∈ (Finset.univ : Finset (Fin (grpSize g))).powersetCard (2 ^ (c - ℓ - 1)),
              ∏ r ∈ A, PEqualNP.Outside.L_meta_25688_aux.toZ2 (matchPrefix g ℓ path r x)) := by
          funext x
          have hb : bitOf (eK.symm x) = x := eK.right_inv x
          dsimp only [choose]
          change PEqualNP.Outside.L_meta_25688_aux.toZ2
            (decide (Nat.choose ((Finset.univ : Finset (Fin (grpSize g))).filter
              (fun r => matchPrefix g ℓ path r (bitOf (eK.symm x)) = true)).card (2 ^ (c - ℓ - 1)) % 2 = 1)) = _
          rw [hb, PEqualNP.Outside.L_meta_25688_aux.elemSym_eq_choose_zmod2]
          have hdec : decide (Nat.choose ((Finset.univ : Finset (Fin (grpSize g))).filter
              (fun r => matchPrefix g ℓ path r x = true)).card (2 ^ (c - ℓ - 1)) % 2 = 1) =
              ((Nat.choose ((Finset.univ : Finset (Fin (grpSize g))).filter
                (fun r => matchPrefix g ℓ path r x = true)).card (2 ^ (c - ℓ - 1)) % 2) == 1) := by
            by_cases h1 : Nat.choose ((Finset.univ : Finset (Fin (grpSize g))).filter
                (fun r => matchPrefix g ℓ path r x = true)).card (2 ^ (c - ℓ - 1)) % 2 = 1
            · simp [h1]
            · simp [h1]
          rw [hdec, PEqualNP.Outside.L_meta_25688_aux.toZ2_nat_parity]
        rw [hch_eq]
        have hmp_deg : ∀ r : Fin (grpSize g),
            PEqualNP.Outside.L_meta_25688_aux.HasDeg (ℓ + 1)
              (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (matchPrefix g ℓ path r x)) := by
          intro r
          have hmp_eq : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (matchPrefix g ℓ path r x)) =
              (fun x => (∏ j : Fin ℓ, (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) j.val x) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (path.testBit (grpBase g + j.val)))) *
                (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) ℓ x))) := by
            funext x
            dsimp only [matchPrefix]
            by_cases hall : (∀ j : Fin ℓ, coord3 (grpMem g r) j.val x = path.testBit (grpBase g + j.val)) ∧
                coord3 (grpMem g r) ℓ x = false
            · rw [decide_eq_true hall]
              have hprod1 : (∏ j : Fin ℓ, (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) j.val x) +
                  PEqualNP.Outside.L_meta_25688_aux.toZ2 (path.testBit (grpBase g + j.val)))) = 1 :=
                Finset.prod_eq_one fun j _ => by
                  rw [hall.1 j, add_assoc, PEqualNP.Outside.L_meta_25688_aux.zmod2_add_self, add_zero]
              rw [hprod1, hall.2]; decide
            · rw [decide_eq_false hall]
              symm
              by_cases hℓ0 : coord3 (grpMem g r) ℓ x = false
              · have hnot : ¬ ∀ j : Fin ℓ, coord3 (grpMem g r) j.val x = path.testBit (grpBase g + j.val) :=
                  fun h => hall ⟨h, hℓ0⟩
                push Not at hnot
                rcases hnot with ⟨j, hj⟩
                have hprod0 : (∏ j : Fin ℓ, (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) j.val x) +
                    PEqualNP.Outside.L_meta_25688_aux.toZ2 (path.testBit (grpBase g + j.val)))) = 0 := by
                  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
                  cases h1 : coord3 (grpMem g r) j.val x <;> cases h2 : path.testBit (grpBase g + j.val)
                  · rw [h1, h2] at hj; exact absurd rfl hj
                  · decide
                  · decide
                  · rw [h1, h2] at hj; exact absurd rfl hj
                rw [hprod0, zero_mul]; rfl
              · have ht : coord3 (grpMem g r) ℓ x = true := by
                  cases h : coord3 (grpMem g r) ℓ x
                  · exact absurd h hℓ0
                  · rfl
                rw [ht]
                have h0 : (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 true : ZMod 2) = 0 := by decide
                rw [h0, mul_zero]; rfl
          rw [hmp_eq]
          have h1 : PEqualNP.Outside.L_meta_25688_aux.HasDeg ℓ
              (fun x => ∏ j : Fin ℓ, (1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) j.val x) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (path.testBit (grpBase g + j.val)))) := by
            have hs : (∑ _j : Fin ℓ, (1 : ℕ)) = ℓ := by simp
            have hpr := PEqualNP.Outside.L_meta_25688_aux.hasDeg_prod (Finset.univ : Finset (Fin ℓ))
              (fun _ => 1)
              (fun (j : Fin ℓ) x => 1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) j.val x) +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 (path.testBit (grpBase g + j.val)))
              fun j _ =>
              PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
                (PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
                  (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
                    (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const 1))
                  (hcoord3_deg (grpMem g r) j.val))
                (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
                  (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const _))
            rwa [hs] at hpr
          have h2 : PEqualNP.Outside.L_meta_25688_aux.HasDeg 1
              (fun x => 1 + PEqualNP.Outside.L_meta_25688_aux.toZ2 (coord3 (grpMem g r) ℓ x)) :=
            PEqualNP.Outside.L_meta_25688_aux.hasDeg_add
              (PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono (by omega)
                (PEqualNP.Outside.L_meta_25688_aux.hasDeg_const 1))
              (hcoord3_deg (grpMem g r) ℓ)
          exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mul h1 h2
        refine PEqualNP.Outside.L_meta_25688_aux.hasDeg_sum _ _ fun A hA => ?_
        have hAcard : A.card = 2 ^ (c - ℓ - 1) := (Finset.mem_powersetCard.mp hA).2
        have hpr := PEqualNP.Outside.L_meta_25688_aux.hasDeg_prod A (fun _ => ℓ + 1)
          (fun r x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (matchPrefix g ℓ path r x))
          (fun r _ => hmp_deg r)
        have hsumA : (∑ _r ∈ A, (ℓ + 1)) = 2 ^ (c - ℓ - 1) * (ℓ + 1) := by
          simp [hAcard]
        rw [hsumA] at hpr
        exact PEqualNP.Outside.L_meta_25688_aux.hasDeg_mono
          (PEqualNP.Outside.L_meta_25688_aux.upper_deg_bound ha1 ha3 hca hℓc) hpr
      · intro path i
        refine (PEqualNP.Outside.L_meta_25688_aux.deg_iff_hasDeg k 2 _).mpr ?_
        have hfn : (fun x => PEqualNP.Outside.L_meta_25688_aux.toZ2 (pred path i (eK.symm x))) =
            predZ path i := funext (hpred_toZ2 path i)
        rw [hfn]
        exact PEqualNP.Outside.L_meta_25688_aux.deg2_cancel_cube _ _ _ _ _ _ _
          (hU'_deg i) (hV'_deg i) (hW'_deg i) (haff_deg i)
      · intro x hx i
        set g := i.val / size
        have hg_le : g ≤ q := Nat.div_le_div_right (le_of_lt i.isLt)
        have hbase_add : grpBase g + grpBits g ≤ steps := by
          change a * g + grpBits g ≤ a * q + crem
          dsimp only [grpBits]
          by_cases hgq : g < q
          · simp only [hgq, ↓reduceIte]
            have : a * (g + 1) ≤ a * q := Nat.mul_le_mul_left a (by omega)
            have : a * g + a = a * (g + 1) := by ring
            omega
          · have hgeq : g = q := by omega
            rw [hgeq]
            simp only [lt_irrefl, ↓reduceIte, le_refl]
        have hgs_lt : grpSize g < 2 ^ grpBits g := by
          dsimp only [grpSize, grpBits]
          by_cases hgq : g < q
          · simp only [hgq, ↓reduceIte]; dsimp only [size]; omega
          · have hgeq : g = q := by omega
            simp only [hgeq, lt_irrefl, ↓reduceIte]
            exact hrem_lt_pow
        have hinv : ∀ ℓ : ℕ, ℓ ≤ grpBits g →
            ((Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
              ∀ j : Fin ℓ, coord3 (grpMem g r) j.val (bitOf x) =
                (run steps choose x).testBit (grpBase g + j.val))).card ≤
            2 ^ (grpBits g - ℓ) - 1 := by
          intro ℓ
          induction ℓ with
          | zero =>
            intro _
            simp only [Nat.sub_zero]
            calc ((Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
                    ∀ j : Fin 0, coord3 (grpMem g r) j.val (bitOf x) =
                      (run steps choose x).testBit (grpBase g + j.val))).card
                ≤ (Finset.univ : Finset (Fin (grpSize g))).card := Finset.card_filter_le _ _
              _ = grpSize g := Finset.card_fin _
              _ ≤ 2 ^ grpBits g - 1 := Nat.le_sub_one_of_lt hgs_lt
          | succ ℓ ih =>
            intro hℓle
            have hprev := ih (by omega)
            set lv := grpBase g + ℓ
            have hlv_lt : lv < steps := by omega
            have hglv : grpOfLevel lv = g := by
              dsimp only [lv, grpBase, grpOfLevel]
              by_cases hgq : g < q
              · have hℓa : ℓ < a := by
                  have hcb : grpBits g = a := by dsimp only [grpBits]; simp only [hgq, ↓reduceIte]
                  omega
                have hlt : a * g + ℓ < a * q := by
                  have h1 : a * (g + 1) ≤ a * q := Nat.mul_le_mul_left a (by omega)
                  have h2 : a * g + a = a * (g + 1) := by ring
                  omega
                simp only [hlt, ↓reduceIte]
                rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hℓa, add_zero]
              · have hgeq : g = q := by omega
                rw [hgeq]
                have hnot : ¬ a * q + ℓ < a * q := by omega
                simp only [hnot, ↓reduceIte]
            have hilv : innerOfLevel lv = ℓ := by
              dsimp only [lv, grpBase, innerOfLevel]
              by_cases hgq : g < q
              · have hℓa : ℓ < a := by
                  have hcb : grpBits g = a := by dsimp only [grpBits]; simp only [hgq, ↓reduceIte]
                  omega
                have hlt : a * g + ℓ < a * q := by
                  have h1 : a * (g + 1) ≤ a * q := Nat.mul_le_mul_left a (by omega)
                  have h2 : a * g + a = a * (g + 1) := by ring
                  omega
                simp only [hlt, ↓reduceIte]
                rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hℓa]
              · have hgeq : g = q := by omega
                rw [hgeq]
                have hnot : ¬ a * q + ℓ < a * q := by omega
                simp only [hnot, ↓reduceIte]
                omega
            set prevSet := (Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
              ∀ j : Fin ℓ, coord3 (grpMem g r) j.val (bitOf x) =
                (run steps choose x).testBit (grpBase g + j.val))
            set S0 := prevSet.filter (fun r => coord3 (grpMem g r) ℓ (bitOf x) = false)
            set S1 := prevSet.filter (fun r => coord3 (grpMem g r) ℓ (bitOf x) = true)
            have hsum_card : S0.card + S1.card = prevSet.card := by
              have hdisj : Disjoint S0 S1 := by
                rw [Finset.disjoint_left]
                intro r h0 h1
                have hb0 := (Finset.mem_filter.mp h0).2
                have hb1 := (Finset.mem_filter.mp h1).2
                rw [hb0] at hb1; exact Bool.noConfusion hb1
              have hun : S0 ∪ S1 = prevSet := by
                ext r
                simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
                constructor
                · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
                · intro h
                  cases coord3 (grpMem g r) ℓ (bitOf x)
                  · left; exact ⟨h, rfl⟩
                  · right; exact ⟨h, rfl⟩
              rw [← Finset.card_union_of_disjoint hdisj, hun]
            have htb_prev : ∀ j : Fin ℓ,
                (run lv choose x).testBit (grpBase g + j.val) =
                (run steps choose x).testBit (grpBase g + j.val) := by
              intro j
              have hm : run steps choose x % 2 ^ lv = run lv choose x :=
                PEqualNP.Outside.L_meta_25688_aux.runFn_mod choose x (le_of_lt hlv_lt)
              have h1 : (run steps choose x % 2 ^ lv).testBit (grpBase g + j.val) =
                  (run steps choose x).testBit (grpBase g + j.val) := by
                rw [Nat.testBit_mod_two_pow]
                have : grpBase g + j.val < lv := by omega
                simp [this]
              rw [← h1, hm]
            have hS0_eq : ((Finset.univ : Finset (Fin (grpSize g))).filter
                (fun r => matchPrefix g ℓ (run lv choose x) r (bitOf x) = true)) = S0 := by
              ext r
              simp only [S0, prevSet, matchPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
                decide_eq_true_eq]
              constructor
              · rintro ⟨h1, h2⟩
                exact ⟨fun j => by rw [← htb_prev j]; exact h1 j, h2⟩
              · rintro ⟨h1, h2⟩
                exact ⟨fun j => by rw [htb_prev j]; exact h1 j, h2⟩
            have hbit_lv : (run steps choose x).testBit lv =
                decide (2 ^ (grpBits g - ℓ - 1) ≤ S0.card) := by
              have htb : (run steps choose x).testBit lv = choose lv (run lv choose x) x :=
                PEqualNP.Outside.L_meta_25688_aux.runFn_testBit choose x hlv_lt
              rw [htb]
              dsimp only [choose]
              rw [hglv, hilv, hS0_eq]
              have hpow2 : 2 ^ (grpBits g - ℓ) = 2 * 2 ^ (grpBits g - ℓ - 1) := by
                have heq : grpBits g - ℓ = (grpBits g - ℓ - 1) + 1 := by omega
                conv_lhs => rw [heq, pow_succ, mul_comm]
              have hS0_lt : S0.card < 2 * 2 ^ (grpBits g - ℓ - 1) := by
                have hpos : 1 ≤ 2 ^ (grpBits g - ℓ) := Nat.one_le_pow _ 2 (by decide)
                omega
              have hq2 : grpBits g - ℓ - 1 ≤ 2 := by
                have hga : grpBits g ≤ a := by
                  dsimp only [grpBits]; split_ifs
                  · exact le_rfl
                  · exact hcrem_le
                omega
              have hiff := PEqualNP.Outside.L_meta_25688_aux.choose_pow2_mod2_iff
                (grpBits g - ℓ - 1) S0.card hq2 hS0_lt
              by_cases hle0 : 2 ^ (grpBits g - ℓ - 1) ≤ S0.card
              · rw [decide_eq_true hle0, decide_eq_true (hiff.mpr hle0)]
              · rw [decide_eq_false hle0, decide_eq_false (fun h => hle0 (hiff.mp h))]
            have hnext_eq : ((Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
                ∀ j : Fin (ℓ + 1), coord3 (grpMem g r) j.val (bitOf x) =
                  (run steps choose x).testBit (grpBase g + j.val))) =
                if 2 ^ (grpBits g - ℓ - 1) ≤ S0.card then S1 else S0 := by
              ext r
              by_cases hle0 : 2 ^ (grpBits g - ℓ - 1) ≤ S0.card
              · simp only [hle0, ↓reduceIte, S1, prevSet, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hall
                  refine ⟨fun j => hall j.castSucc, ?_⟩
                  have hl := hall (Fin.last ℓ)
                  dsimp only [Fin.last] at hl
                  change coord3 (grpMem g r) ℓ (bitOf x) = (run steps choose x).testBit lv at hl
                  rw [hbit_lv, decide_eq_true hle0] at hl
                  exact hl
                · rintro ⟨h1, h2⟩ j
                  refine Fin.lastCases ?_ ?_ j
                  · dsimp only [Fin.last]
                    change coord3 (grpMem g r) ℓ (bitOf x) = (run steps choose x).testBit lv
                    rw [hbit_lv, decide_eq_true hle0]
                    exact h2
                  · intro j'; exact h1 j'
              · simp only [hle0, ↓reduceIte, S0, prevSet, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hall
                  refine ⟨fun j => hall j.castSucc, ?_⟩
                  have hl := hall (Fin.last ℓ)
                  dsimp only [Fin.last] at hl
                  change coord3 (grpMem g r) ℓ (bitOf x) = (run steps choose x).testBit lv at hl
                  rw [hbit_lv, decide_eq_false hle0] at hl
                  exact hl
                · rintro ⟨h1, h2⟩ j
                  refine Fin.lastCases ?_ ?_ j
                  · dsimp only [Fin.last]
                    change coord3 (grpMem g r) ℓ (bitOf x) = (run steps choose x).testBit lv
                    rw [hbit_lv, decide_eq_false hle0]
                    exact h2
                  · intro j'; exact h1 j'
            rw [hnext_eq]
            have hpow2 : 2 ^ (grpBits g - ℓ) = 2 * 2 ^ (grpBits g - (ℓ + 1)) := by
              have heq : grpBits g - ℓ = (grpBits g - (ℓ + 1)) + 1 := by omega
              conv_lhs => rw [heq, pow_succ, mul_comm]
            have hsubeq : grpBits g - ℓ - 1 = grpBits g - (ℓ + 1) := by omega
            split_ifs with hle0
            · rw [hsubeq] at hle0; omega
            · rw [hsubeq] at hle0; omega
        have hzero := hinv (grpBits g) le_rfl
        simp only [Nat.sub_self, pow_zero] at hzero
        have hcard0 : ((Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
            ∀ j : Fin (grpBits g), coord3 (grpMem g r) j.val (bitOf x) =
              (run steps choose x).testBit (grpBase g + j.val))).card = 0 := by omega
        have hrem_i : i.val % size < grpSize g := by
          dsimp only [grpSize]
          by_cases hgq : g < q
          · simp only [hgq, ↓reduceIte]; exact Nat.mod_lt _ hsize_pos
          · have hgeq : g = q := by omega
            simp only [hgeq, lt_irrefl, ↓reduceIte]
            have hdm := Nat.div_add_mod i.val size
            have hdm2 := Nat.div_add_mod m size
            have hlt_im : i.val < m := i.isLt
            dsimp only [rem, q] at *
            dsimp only [g] at hgeq
            rw [hgeq] at hdm
            omega
        let ri : Fin (grpSize g) := ⟨i.val % size, hrem_i⟩
        have hmem_ri : grpMem g ri = i := by
          ext
          dsimp only [grpMem, ri, g]
          rw [mul_comm]
          exact Nat.div_add_mod i.val size
        have hnot_all : ¬ ∀ j : Fin (grpBits g),
            coord3 i j.val (bitOf x) = (run steps choose x).testBit (grpBase g + j.val) := by
          intro hall
          have hmem : ri ∈ (Finset.univ : Finset (Fin (grpSize g))).filter (fun r =>
              ∀ j : Fin (grpBits g), coord3 (grpMem g r) j.val (bitOf x) =
                (run steps choose x).testBit (grpBase g + j.val)) := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ ri, fun j => ?_⟩
            rw [hmem_ri]; exact hall j
          have hpos := Finset.card_pos.mpr ⟨ri, hmem⟩
          omega
        push Not at hnot_all
        rcases hnot_all with ⟨j0, hj0⟩
        apply PEqualNP.Outside.L_meta_25688_aux.toZ2_injective
        have hp_eq := hpred_toZ2 (run steps choose x) i (bitOf x)
        have hsymm : eK.symm (bitOf x) = x := eK.left_inv x
        rw [hsymm] at hp_eq
        rw [hp_eq, hout_formula x hx i, PEqualNP.Outside.L_meta_25688_aux.toZ2_xor,
          PEqualNP.Outside.L_meta_25688_aux.toZ2_and, PEqualNP.Outside.L_meta_25688_aux.toZ2_and]
        dsimp only [predZ]
        have hga : grpBits g ≤ 3 := by
          have : grpBits g ≤ a := by
            dsimp only [grpBits]; split_ifs
            · exact le_rfl
            · exact hcrem_le
          omega
        have hzero_prod :
            (PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i (bitOf x)) + 1 +
              PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 0 < grpBits g then (run steps choose x).testBit (grpBase g + 0) else false)) *
            (PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i (bitOf x)) + 1 +
              PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 1 < grpBits g then (run steps choose x).testBit (grpBase g + 1) else false)) *
            (PEqualNP.Outside.L_meta_25688_aux.toZ2 (W' i (bitOf x)) + 1 +
              PEqualNP.Outside.L_meta_25688_aux.toZ2 (if 2 < grpBits g then (run steps choose x).testBit (grpBase g + 2) else false)) = 0 := by
          have hj3 : j0.val < 3 := lt_of_lt_of_le j0.isLt hga
          have hjlt := j0.isLt
          have hne_z : ∀ b1 b2 : Bool, b1 ≠ b2 →
              PEqualNP.Outside.L_meta_25688_aux.toZ2 b1 + 1 +
                PEqualNP.Outside.L_meta_25688_aux.toZ2 b2 = 0 := by
            intro b1 b2 hne
            cases b1 <;> cases b2 <;> simp_all [PEqualNP.Outside.L_meta_25688_aux.toZ2]
            · decide
            · decide
          rcases j0 with ⟨jv, hjv⟩
          interval_cases jv
          · simp only [hjv, ↓reduceIte]
            change U' i (bitOf x) ≠ (run steps choose x).testBit (grpBase g + 0) at hj0
            rw [hne_z _ _ hj0, zero_mul, zero_mul]
          · simp only [hjv, ↓reduceIte]
            change V' i (bitOf x) ≠ (run steps choose x).testBit (grpBase g + 1) at hj0
            rw [hne_z _ _ hj0, mul_zero, zero_mul]
          · simp only [hjv, ↓reduceIte]
            change W' i (bitOf x) ≠ (run steps choose x).testBit (grpBase g + 2) at hj0
            rw [hne_z _ _ hj0, mul_zero]
        change PEqualNP.Outside.L_meta_25688_aux.toZ2 (U' i (bitOf x)) *
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (V' i (bitOf x)) *
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (W' i (bitOf x)) + _ +
            PEqualNP.Outside.L_meta_25688_aux.toZ2 (aff i (bitOf x)) = _
        rw [hzero_prod, add_zero]
