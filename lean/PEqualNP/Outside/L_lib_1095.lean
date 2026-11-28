import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1095

open Finset

abbrev Word (k : Nat) := Fin k → ZMod 2

def localRule (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) : Prop :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

def ext (n : Nat) (U : Finset (Fin n)) (b : Word n) (z : U → ZMod 2) : Word n :=
  fun i => if h : i ∈ U then z ⟨i, h⟩ else b i

def observed (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) : Word m :=
  fun r => ∑ i, (ext n U b z i + T i (ext n U b z)) * Q i r

def uniform (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) : Prop :=
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card

def dot {m : Nat} (s w : Word m) : ZMod 2 := ∑ r, s r * w r

def Cond (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) : Prop :=
  ∀ s : Word m, s ≠ 0 → ∃ i ∈ U, dot s (Q i) = 1 ∧ ∀ k, dot s (Q k) = 1 → i ∉ D k

def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma chi_add_one (a : ZMod 2) : chi (a + 1) = - chi a := by
  revert a; decide

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

lemma dot_add_left {m : Nat} (a b w : Word m) : dot (a + b) w = dot a w + dot b w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {m : Nat} (s a b : Word m) : dot s (a + b) = dot s a + dot s b := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_single {m : Nat} (s : Word m) (r : Fin m) (c : ZMod 2) :
    dot s (Pi.single r c) = s r * c := by
  simp [dot, Pi.single_apply]

lemma dot_single_left {m : Nat} (w : Word m) (r : Fin m) (c : ZMod 2) :
    dot (Pi.single r c) w = c * w r := by
  simp [dot, Pi.single_apply]

lemma dot_zero_left {m : Nat} (w : Word m) : dot 0 w = 0 := by
  simp [dot]

lemma chi_sum {m : Nat} (w : Word m) :
    ∑ s : Word m, chi (dot s w) = if w = 0 then (2:ℤ)^m else 0 := by
  split_ifs with hw
  · subst hw
    simp [dot, chi, ZMod.card]
  · obtain ⟨r, hr⟩ : ∃ r, w r ≠ 0 := by
      by_contra h; push Not at h; exact hw (funext h)
    have hr1 : w r = 1 := (z2 _).resolve_left hr
    have key : ∑ s : Word m, chi (dot s w)
        = ∑ s : Word m, chi (dot (s + Pi.single r 1) w) :=
      (Equiv.sum_comp (Equiv.addRight (Pi.single r 1 : Word m)) (fun s => chi (dot s w))).symm
    have : ∑ s : Word m, chi (dot (s + Pi.single r 1) w) = - ∑ s : Word m, chi (dot s w) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [dot_add_left, dot_single_left, hr1, one_mul, chi_add_one]
    linarith

lemma dot_observed (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (s : Word m) :
    dot s (observed n m Q U T b z)
      = ∑ k, (ext n U b z k + T k (ext n U b z)) * dot s (Q k) := by
  simp only [dot, observed, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun r _ => ?_))
  ring


lemma word_add_eq_zero {m : Nat} (a b : Word m) : a + b = 0 ↔ a = b := by
  have h : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide
  constructor
  · intro hab; funext r; exact (h _ _).1 (congrFun hab r)
  · intro hab; funext r; exact (h _ _).2 (congrFun hab r)

lemma ext_flip (n : Nat) (U : Finset (Fin n)) (b : Word n) (z : U → ZMod 2) (i : Fin n)
    (hi : i ∈ U) :
    ext n U b (z + Pi.single ⟨i, hi⟩ 1) = ext n U b z + Pi.single i 1 := by
  funext k
  simp only [ext, Pi.add_apply]
  by_cases hk : k ∈ U
  · simp only [hk, dite_true]
    congr 1
    by_cases hki : k = i
    · subst hki; simp
    · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne]
      intro h; exact hki (congrArg Subtype.val h)
  · simp only [hk, dite_false]
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    rw [Pi.single_eq_of_ne hki, add_zero]

lemma balanced (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) (T : Fin n → Word n → ZMod 2) (hT : localRule n D T) (b : Word n)
    (s : Word m) (i : Fin n) (hi : i ∈ U) (hs : dot s (Q i) = 1)
    (hfree : ∀ k, dot s (Q k) = 1 → i ∉ D k) :
    ∑ z : U → ZMod 2, chi (dot s (observed n m Q U T b z)) = 0 := by
  have step : ∀ z : U → ZMod 2, dot s (observed n m Q U T b (z + Pi.single ⟨i, hi⟩ 1))
      = dot s (observed n m Q U T b z) + 1 := by
    intro z
    rw [dot_observed, dot_observed, ext_flip]
    have hterm : ∀ k, (ext n U b z k + (Pi.single i (1 : ZMod 2) : Word n) k
          + T k (ext n U b z + Pi.single i 1)) * dot s (Q k)
        = (ext n U b z k + T k (ext n U b z)) * dot s (Q k)
          + (Pi.single i (1 : ZMod 2) : Word n) k * dot s (Q k) := by
      intro k
      rcases z2 (dot s (Q k)) with h0 | h1
      · rw [h0]; ring
      · have hTk : T k (ext n U b z + Pi.single i 1) = T k (ext n U b z) := by
          apply hT
          intro j hj
          have hji : j ≠ i := fun h => hfree k h1 (h ▸ hj)
          simp [Pi.single_eq_of_ne hji]
        rw [hTk]; ring
    simp only [Pi.add_apply]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, hs]
  have key : ∑ z : U → ZMod 2, chi (dot s (observed n m Q U T b z))
      = ∑ z : U → ZMod 2, chi (dot s (observed n m Q U T b (z + Pi.single ⟨i, hi⟩ 1))) :=
    (Equiv.sum_comp (Equiv.addRight (Pi.single ⟨i, hi⟩ 1 : U → ZMod 2))
      (fun z => chi (dot s (observed n m Q U T b z)))).symm
  have : ∑ z : U → ZMod 2, chi (dot s (observed n m Q U T b (z + Pi.single ⟨i, hi⟩ 1)))
      = - ∑ z : U → ZMod 2, chi (dot s (observed n m Q U T b z)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [step, chi_add_one]
  linarith

lemma uniform_of_cond (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) (hC : Cond n m D Q U) : uniform n m D Q U := by
  intro T hT b v
  set f := observed n m Q U T b with hf
  have hcard : (Nat.card {z : U → ZMod 2 // f z = v} : ℤ)
      = ∑ z : U → ZMod 2, if f z = v then (1:ℤ) else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast; rfl
  have h1 : ((2:ℤ)^m) * (Nat.card {z : U → ZMod 2 // f z = v} : ℤ)
      = ∑ z : U → ZMod 2, ∑ s : Word m, chi (dot s (f z + v)) := by
    rw [hcard, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [chi_sum]
    by_cases h : f z = v
    · have h' : f z + v = 0 := (word_add_eq_zero _ _).2 h
      rw [if_pos h, if_pos h', mul_one]
    · rw [if_neg h, if_neg (mt (word_add_eq_zero _ _).1 h), mul_zero]
  have h2 : ∑ z : U → ZMod 2, ∑ s : Word m, chi (dot s (f z + v))
      = ∑ s : Word m, chi (dot s v) * ∑ z : U → ZMod 2, chi (dot s (f z)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [dot_add_right, chi_add, mul_comm]
  have h3 : ∑ s : Word m, chi (dot s v) * ∑ z : U → ZMod 2, chi (dot s (f z))
      = (2:ℤ)^U.card := by
    rw [Finset.sum_eq_single (0 : Word m)]
    · simp [dot_zero_left, chi, ZMod.card]
    · intro s _ hs
      obtain ⟨i, hi, hsi, hfree⟩ := hC s hs
      rw [hf, balanced n m D Q U T hT b s i hi hsi hfree, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have : ((2:ℤ)^m) * (Nat.card {z : U → ZMod 2 // f z = v} : ℤ) = (2:ℤ)^U.card := by
    rw [h1, h2, h3]
  exact_mod_cast this

lemma cond_of_uniform (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) (hu : uniform n m D Q U) : Cond n m D Q U := by
  by_contra hC
  unfold Cond at hC
  push Not at hC
  obtain ⟨s, hs0, hs⟩ := hC
  have hex : ∀ i, ∃ k, i ∈ U → dot s (Q i) = 1 → dot s (Q k) = 1 ∧ i ∈ D k := by
    intro i
    by_cases h : i ∈ U ∧ dot s (Q i) = 1
    · obtain ⟨k, hk⟩ := hs i h.1 h.2
      exact ⟨k, fun _ _ => hk⟩
    · exact ⟨i, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose c hc using hex
  let T : Fin n → Word n → ZMod 2 := fun k x =>
    ∑ i, if (i ∈ U ∧ dot s (Q i) = 1 ∧ c i = k) then x i else 0
  have hT : localRule n D T := by
    intro k x y hxy
    simp only [T]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · exact hxy i (h.2.2 ▸ (hc i h.1 h.2.1).2)
    · rfl
  have hconst : ∀ z, dot s (observed n m Q U T 0 z) = 0 := by
    intro z
    rw [dot_observed]
    set x := ext n U 0 z with hx
    have hTsum : ∑ k, T k x * dot s (Q k)
        = ∑ i, if (i ∈ U ∧ dot s (Q i) = 1) then x i else 0 := by
      simp only [T, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hP : i ∈ U ∧ dot s (Q i) = 1
      · rw [if_pos hP]
        have : ∀ k, (if (i ∈ U ∧ dot s (Q i) = 1 ∧ c i = k) then x i else 0) * dot s (Q k)
            = if c i = k then x i * dot s (Q k) else 0 := by
          intro k
          by_cases hk : c i = k
          · rw [if_pos ⟨hP.1, hP.2, hk⟩, if_pos hk]
          · rw [if_neg (fun h => hk h.2.2), if_neg hk, zero_mul]
        rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_ite_eq]
        simp [(hc i hP.1 hP.2).1]
      · rw [if_neg hP]
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rw [if_neg (fun h => hP ⟨h.1, h.2.1⟩), zero_mul]
    simp only [add_mul]
    rw [Finset.sum_add_distrib, hTsum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hk : k ∈ U
    · rcases z2 (dot s (Q k)) with h0 | h1
      · rw [if_neg (fun h => by rw [h.2] at h0; exact one_ne_zero h0), h0]; ring
      · rw [if_pos ⟨hk, h1⟩, h1, mul_one]
        have : ∀ a : ZMod 2, a + a = 0 := by decide
        exact this _
    · have hx0 : x k = 0 := by simp [hx, ext, hk]
      rw [hx0, if_neg (fun h => hk h.1)]; ring
  obtain ⟨r, hr⟩ : ∃ r, s r ≠ 0 := by
    by_contra h; push Not at h; exact hs0 (funext h)
  have hr1 : s r = 1 := (z2 _).resolve_left hr
  have h := hu T hT 0 (Pi.single r 1)
  have hempty : Nat.card {z : U → ZMod 2 // observed n m Q U T 0 z = Pi.single r 1} = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨z, hz⟩
    have h1 := hconst z
    rw [hz, dot_single, hr1, mul_one] at h1
    exact one_ne_zero h1
  rw [hempty, mul_zero] at h
  exact absurd h.symm (by positivity)

lemma uniform_iff (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) : uniform n m D Q U ↔ Cond n m D Q U :=
  ⟨cond_of_uniform n m D Q U, uniform_of_cond n m D Q U⟩

lemma card_word (m : Nat) : Fintype.card (Word m) = 2^m := by
  simp [Word, ZMod.card]

lemma card_nz (m : Nat) : (univ.filter (fun s : Word m => s ≠ 0)).card = 2^m - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_word]

lemma la_bound {n m : Nat} (t q : Word m) (w : Fin n → Word m) (R : Finset (Fin n))
    (htq : dot t q = 1) (hR : ∀ k ∈ R, dot t (w k) = 0)
    (hs : ∀ s, s ≠ t → dot s q = 1 → ∃ k ∈ R, dot s (w k) = 1) : m ≤ R.card + 1 := by
  let F : Word m → (R → ZMod 2) × ZMod 2 := fun s => (fun k => dot s (w k), dot s q)
  have hself : ∀ a : ZMod 2, a + a = 0 := by decide
  have hinj : Function.Injective F := by
    intro a b hab
    simp only [F, Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    set d := a + b with hd
    have hdw : ∀ k ∈ R, dot d (w k) = 0 := by
      intro k hk
      have := congrFun h1 ⟨k, hk⟩
      simp only at this
      rw [hd, dot_add_left, this, hself]
    have hdq : dot d q = 0 := by rw [hd, dot_add_left, h2, hself]
    have hd0 : d = 0 := by
      by_contra hne
      have hne' : d + t ≠ t := by
        intro h; apply hne
        have := congrArg (· + t) h
        simpa [add_assoc, (word_add_eq_zero t t).2 rfl] using this
      obtain ⟨k, hk, hk1⟩ := hs (d + t) hne' (by rw [dot_add_left, hdq, htq, zero_add])
      rw [dot_add_left, hdw k hk, hR k hk, add_zero] at hk1
      exact zero_ne_one hk1
    exact (word_add_eq_zero a b).1 hd0
  have hc := Fintype.card_le_of_injective F hinj
  rw [card_word] at hc
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, ZMod.card] at hc
  have : 2^m ≤ 2^(R.card + 1) := by rw [pow_succ]; exact hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

lemma wires_eq {n : Nat} (D : Fin n → Finset (Fin n)) :
    ∑ i, (D i).card = ∑ j, (univ.filter (fun i => j ∈ D i)).card := by
  have h : ∀ i, (D i).card = ∑ j, if j ∈ D i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext j; simp
  simp_rw [h, Finset.card_filter]
  exact Finset.sum_comm

lemma part2 (m : Nat) (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (W : Finset (Fin n)) (hW : W.card = 2^m - 1) (hu : uniform n m D Q univ)
    (hj : ∀ j ∈ W, ¬ uniform n m D Q (univ.erase j)) :
    2^m - 1 ≤ n ∧ (∀ j ∈ W, m - 1 ≤ (univ.filter (fun i => j ∈ D i)).card) ∧
      (2^m - 1) * (m - 1) ≤ ∑ i, (D i).card := by
  rw [uniform_iff] at hu
  simp only [uniform_iff] at hj
  have hex : ∀ j, ∃ t : Word m, j ∈ W → (t ≠ 0 ∧ dot t (Q j) = 1 ∧
      (∀ k, dot t (Q k) = 1 → j ∉ D k) ∧
      ∀ i, i ≠ j → dot t (Q i) = 1 → ∃ k, dot t (Q k) = 1 ∧ i ∈ D k) := by
    intro j
    by_cases hjW : j ∈ W
    · have h := hj j hjW
      unfold Cond at h
      push Not at h
      obtain ⟨s, hs0, hs⟩ := h
      obtain ⟨i, _, hi1, hfree⟩ := hu s hs0
      have hij : i = j := by
        by_contra hne
        obtain ⟨k, hk1, hk2⟩ := hs i (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) hi1
        exact hfree k hk1 hk2
      subst hij
      refine ⟨s, fun _ => ⟨hs0, hi1, hfree, ?_⟩⟩
      intro i' hi' h1
      exact hs i' (Finset.mem_erase.2 ⟨hi', Finset.mem_univ _⟩) h1
    · exact ⟨0, fun h => absurd h hjW⟩
  choose t ht using hex
  have hinj : Set.InjOn t W := by
    intro j hjW j' hj'W heq
    by_contra hne
    have h1 : dot (t j) (Q j') = 1 := by rw [heq]; exact (ht j' hj'W).2.1
    obtain ⟨k, hk1, hk2⟩ := (ht j hjW).2.2.2 j' (Ne.symm hne) h1
    exact (ht j' hj'W).2.2.1 k (by rw [← heq]; exact hk1) hk2
  have hsurj : ∀ s : Word m, s ≠ 0 → ∃ j' ∈ W, t j' = s := by
    have hsub : W.image t ⊆ univ.filter (fun s : Word m => s ≠ 0) := by
      intro s hs
      obtain ⟨j, hjW, rfl⟩ := Finset.mem_image.1 hs
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ht j hjW).1⟩
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [card_nz, Finset.card_image_of_injOn hinj, hW])
    intro s hs
    have : s ∈ W.image t := by rw [heq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩
    obtain ⟨j, hjW, hjs⟩ := Finset.mem_image.1 this
    exact ⟨j, hjW, hjs⟩
  have hread : ∀ j ∈ W, m - 1 ≤ (univ.filter (fun i => j ∈ D i)).card := by
    intro j hjW
    have := la_bound (t j) (Q j) Q (univ.filter (fun i => j ∈ D i)) (ht j hjW).2.1
      (by
        intro k hk
        have hk' := (Finset.mem_filter.1 hk).2
        rcases z2 (dot (t j) (Q k)) with h0 | h1
        · exact h0
        · exact absurd hk' ((ht j hjW).2.2.1 k h1))
      (by
        intro s hst hsq
        have hs0 : s ≠ 0 := by
          rintro rfl; rw [dot_zero_left] at hsq; exact zero_ne_one hsq
        obtain ⟨j', hj'W, hj's⟩ := hsurj s hs0
        have hne : j ≠ j' := by rintro rfl; exact hst hj's.symm
        obtain ⟨k, hk1, hk2⟩ := (ht j' hj'W).2.2.2 j hne (by rw [hj's]; exact hsq)
        exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk2⟩, by rw [← hj's]; exact hk1⟩)
    omega
  refine ⟨?_, hread, ?_⟩
  · rw [← hW]; simpa using Finset.card_le_univ W
  · rw [wires_eq, ← hW]
    calc W.card * (m - 1) = W.card • (m - 1) := (smul_eq_mul _ _).symm
      _ ≤ ∑ j ∈ W, (univ.filter (fun i => j ∈ D i)).card :=
          Finset.card_nsmul_le_sum _ _ _ hread
      _ ≤ ∑ j, (univ.filter (fun i => j ∈ D i)).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ W)

def e {m : Nat} (r : Fin m) : Word m := Pi.single r 1

def pre {m : Nat} (b : Fin m) : Word m := fun r => if r ≤ b then 1 else 0

def gap {m : Nat} (a b : Fin m) : Word m := fun r => if r < a ∨ r = b then 1 else 0

def ones {m : Nat} (t : Word m) : Finset (Fin m) := univ.filter (fun r => t r = 1)

def Qb {m : Nat} (t : Word m) (b : Fin m) : Word m :=
  if h2 : (univ.filter (fun r => t r = 0 ∧ r < b)).Nonempty then
    e ((univ.filter (fun r => t r = 0 ∧ r < b)).min' h2) + e b
  else e b

def Qp {m : Nat} (t : Word m) : Word m :=
  if h : (ones t).Nonempty then Qb t ((ones t).max' h) else 0

lemma dot_e {m : Nat} (s : Word m) (r : Fin m) : dot s (e r) = s r := by
  rw [e, dot_single, mul_one]

lemma e_apply {m : Nat} (r c : Fin m) : e r c = if c = r then 1 else 0 := by
  simp [e, Pi.single_apply]

lemma ones_nonempty {m : Nat} (t : Word m) (ht : t ≠ 0) : (ones t).Nonempty := by
  obtain ⟨r, hr⟩ : ∃ r, t r ≠ 0 := by
    by_contra h; push Not at h; exact ht (funext h)
  exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_univ _, (z2 _).resolve_left hr⟩⟩

lemma Qp_dot {m : Nat} (t : Word m) (ht : t ≠ 0) : dot t (Qp t) = 1 := by
  have hne := ones_nonempty t ht
  rw [Qp, dif_pos hne]
  have hb : t ((ones t).max' hne) = 1 := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  generalize (ones t).max' hne = b at hb
  unfold Qb
  split_ifs with h2
  · have ha := (Finset.mem_filter.1 (Finset.min'_mem _ h2)).2.1
    rw [dot_add_right, dot_e, dot_e, ha, hb, zero_add]
  · rw [dot_e, hb]

lemma Qp_wt {m : Nat} (t : Word m) : (univ.filter (fun r => Qp t r ≠ 0)).card ≤ 2 := by
  have key : ∃ S : Finset (Fin m), S.card ≤ 2 ∧ ∀ r, Qp t r ≠ 0 → r ∈ S := by
    unfold Qp
    split_ifs with h
    · unfold Qb
      split_ifs with h2
      · refine ⟨{(univ.filter (fun r => t r = 0 ∧ r < (ones t).max' h)).min' h2,
          (ones t).max' h}, Finset.card_le_two, fun r hr => ?_⟩
        simp only [Pi.add_apply, e_apply] at hr
        by_contra hc
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
        rw [if_neg hc.1, if_neg hc.2, add_zero] at hr
        exact hr rfl
      · refine ⟨{(ones t).max' h}, by simp, fun r hr => ?_⟩
        rw [e_apply] at hr
        by_contra hc
        rw [Finset.mem_singleton] at hc
        rw [if_neg hc] at hr
        exact hr rfl
    · exact ⟨∅, by simp, fun r hr => absurd rfl hr⟩
  obtain ⟨S, hS, hsub⟩ := key
  calc (univ.filter (fun r => Qp t r ≠ 0)).card ≤ S.card := by
        apply Finset.card_le_card
        intro r hr
        exact hsub r (Finset.mem_filter.1 hr).2
    _ ≤ 2 := hS

lemma Qp_pre {m : Nat} (b : Fin m) : Qp (pre b) = e b := by
  have hbm : b ∈ ones (pre b) := Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [pre]⟩
  have hne : (ones (pre b)).Nonempty := ⟨b, hbm⟩
  have htop : (ones (pre b)).max' hne = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have := (Finset.mem_filter.1 hy).2
      simp only [pre] at this
      by_contra hc
      rw [if_neg hc] at this
      exact zero_ne_one this
    · exact Finset.le_max' _ _ hbm
  rw [Qp, dif_pos hne, htop, Qb, dif_neg]
  rintro ⟨y, hy⟩
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hy).2
  simp only [pre] at h1
  rw [if_pos (le_of_lt h2)] at h1
  exact one_ne_zero h1

lemma Qp_gap {m : Nat} (a b : Fin m) (hab : a < b) : Qp (gap a b) = e a + e b := by
  have hbm : b ∈ ones (gap a b) := Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [gap]⟩
  have hne : (ones (gap a b)).Nonempty := ⟨b, hbm⟩
  have htop : (ones (gap a b)).max' hne = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      have := (Finset.mem_filter.1 hy).2
      simp only [gap] at this
      by_contra hc
      push Not at hc
      rw [if_neg (by omega)] at this
      exact zero_ne_one this
    · exact Finset.le_max' _ _ hbm
  have ham : a ∈ univ.filter (fun r => gap a b r = 0 ∧ r < b) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      refine ⟨?_, hab⟩
      simp only [gap]
      rw [if_neg (by omega)]⟩
  have h2 : (univ.filter (fun r => gap a b r = 0 ∧ r < b)).Nonempty := ⟨a, ham⟩
  have hmin : (univ.filter (fun r => gap a b r = 0 ∧ r < b)).min' h2 = a := by
    apply le_antisymm
    · exact Finset.min'_le _ _ ham
    · apply Finset.le_min'
      intro y hy
      have := (Finset.mem_filter.1 hy).2.1
      simp only [gap] at this
      by_contra hc
      push Not at hc
      rw [if_pos (Or.inl hc)] at this
      exact one_ne_zero this
  rw [Qp, dif_pos hne, htop, Qb, dif_pos h2, hmin]

abbrev NZ (m : Nat) := {t : Word m // t ≠ 0}

def ptop {m : Nat} (t : NZ m) : Fin m := (ones t.1).max' (ones_nonempty t.1 t.2)

lemma ptop_one {m : Nat} (t : NZ m) : t.1 (ptop t) = 1 := by
  unfold ptop
  exact (Finset.mem_filter.1 (Finset.max'_mem (ones t.1) _)).2

lemma le_ptop {m : Nat} (t : NZ m) (r : Fin m) (hr : t.1 r = 1) : r ≤ ptop t :=
  Finset.le_max' (ones t.1) r (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩)

def mask {m : Nat} (t : NZ m) (r : Fin m) : Word m :=
  if t.1 r = 0 then pre r else gap r (ptop t)

lemma mask_ne {m : Nat} (t : NZ m) (r : Fin m) : mask t r ≠ 0 := by
  unfold mask
  split_ifs
  · intro h; have := congrFun h r; simp [pre] at this
  · intro h; have := congrFun h (ptop t); simp [gap] at this

def bv {m : Nat} (t : NZ m) (r : Fin m) : Word m :=
  if t.1 r = 0 then e r else e r + e (ptop t)

lemma Qp_mask {m : Nat} (t : NZ m) (r : Fin m) (hr : r ≠ ptop t) : Qp (mask t r) = bv t r := by
  unfold mask bv
  split_ifs with h
  · exact Qp_pre r
  · have h1 : t.1 r = 1 := (z2 _).resolve_left h
    exact Qp_gap r (ptop t) (lt_of_le_of_ne (le_ptop t r h1) hr)

lemma dot_bv {m : Nat} (t : NZ m) (r : Fin m) (_hr : r ≠ ptop t) : dot t.1 (bv t r) = 0 := by
  unfold bv
  split_ifs with h
  · rw [dot_e, h]
  · rw [dot_add_right, dot_e, dot_e, (z2 _).resolve_left h, ptop_one]; decide

lemma span_bv {m : Nat} (t : NZ m) (s : Word m) (hs0 : s ≠ 0) (hst : s ≠ t.1) :
    ∃ r, r ≠ ptop t ∧ dot s (bv t r) = 1 := by
  by_contra hc
  push Not at hc
  have hall : ∀ c, s c = s (ptop t) * t.1 c := by
    intro c
    by_cases hcp : c = ptop t
    · rw [hcp, ptop_one, mul_one]
    · have h0 : dot s (bv t c) = 0 := (z2 _).resolve_right (hc c hcp)
      unfold bv at h0
      split_ifs at h0 with htc
      · rw [dot_e] at h0; rw [h0, htc, mul_zero]
      · rw [dot_add_right, dot_e, dot_e] at h0
        rw [(z2 _).resolve_left htc, mul_one]
        have : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
        exact this _ _ h0
  rcases z2 (s (ptop t)) with h | h
  · exact hs0 (funext fun c => by rw [hall c, h, zero_mul]; rfl)
  · exact hst (funext fun c => by rw [hall c, h, one_mul])

lemma bv_inj {m : Nat} (t : NZ m) (r r' : Fin m) (hr : r ≠ ptop t) (_hr' : r' ≠ ptop t)
    (h : bv t r = bv t r') : r = r' := by
  have h1 : bv t r r = 1 := by
    unfold bv; split_ifs <;> simp [e_apply, hr]
  have h2 : bv t r' r = e r' r := by
    unfold bv; split_ifs <;> simp [e_apply, hr]
  rw [h, h2, e_apply] at h1
  by_contra hne
  rw [if_neg hne] at h1
  exact zero_ne_one h1

section construction
variable {m N : Nat} (σ : Fin N ≃ NZ m)

def Qs (i : Fin N) : Word m := Qp (σ i).1

def Rs (j : Fin N) : Finset (Fin N) :=
  (univ.erase (ptop (σ j))).image (fun r => σ.symm ⟨mask (σ j) r, mask_ne _ _⟩)

def Ds (i : Fin N) : Finset (Fin N) := univ.filter (fun j => i ∈ Rs σ j)

lemma Qs_R (j : Fin N) (r : Fin m) (hr : r ≠ ptop (σ j)) :
    Qs σ (σ.symm ⟨mask (σ j) r, mask_ne _ _⟩) = bv (σ j) r := by
  rw [Qs, Equiv.apply_symm_apply]
  exact Qp_mask _ r hr

lemma Rs_dot (j k : Fin N) (hk : k ∈ Rs σ j) : dot (σ j).1 (Qs σ k) = 0 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hk
  have hr' := (Finset.mem_erase.1 hr).1
  rw [Qs_R σ j r hr']
  exact dot_bv _ r hr'

lemma Rs_span (j : Fin N) (s : Word m) (hs0 : s ≠ 0) (hst : s ≠ (σ j).1) :
    ∃ k ∈ Rs σ j, dot s (Qs σ k) = 1 := by
  obtain ⟨r, hr, h1⟩ := span_bv (σ j) s hs0 hst
  refine ⟨_, Finset.mem_image.2 ⟨r, Finset.mem_erase.2 ⟨hr, Finset.mem_univ _⟩, rfl⟩, ?_⟩
  rw [Qs_R σ j r hr]; exact h1

lemma Rs_card (j : Fin N) : (Rs σ j).card = m - 1 := by
  rw [Rs, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  intro r hr r' hr' h
  have hr1 := (Finset.mem_erase.1 hr).1
  have hr1' := (Finset.mem_erase.1 hr').1
  have := congrArg (Qs σ) h
  simp only at this
  rw [Qs_R σ j r hr1, Qs_R σ j r' hr1'] at this
  exact bv_inj _ r r' hr1 hr1' this

lemma Qs_dot (j : Fin N) : dot (σ j).1 (Qs σ j) = 1 := Qp_dot _ (σ j).2

lemma cond_iff (U : Finset (Fin N)) : Cond N m (Ds σ) (Qs σ) U ↔ U = univ := by
  constructor
  · intro hC
    by_contra hU
    obtain ⟨j, hj⟩ : ∃ j, j ∉ U := by
      by_contra h; push Not at h; exact hU (Finset.eq_univ_of_forall h)
    obtain ⟨i, hi, hi1, hfree⟩ := hC (σ j).1 (σ j).2
    have hij : i ≠ j := by rintro rfl; exact hj hi
    have hne : (σ j).1 ≠ (σ i).1 := by
      intro h; exact hij (σ.injective (Subtype.ext h)).symm
    obtain ⟨k, hk, hk1⟩ := Rs_span σ i (σ j).1 (σ j).2 hne
    exact hfree k hk1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
  · rintro rfl
    intro s hs
    refine ⟨σ.symm ⟨s, hs⟩, Finset.mem_univ _, ?_, ?_⟩
    · have := Qs_dot σ (σ.symm ⟨s, hs⟩)
      rwa [Equiv.apply_symm_apply] at this
    · intro k hk1 hk
      have hk' := (Finset.mem_filter.1 hk).2
      have := Rs_dot σ _ k hk'
      rw [Equiv.apply_symm_apply] at this
      rw [this] at hk1
      exact zero_ne_one hk1

end construction

lemma part1 (m : Nat) : ∃ (D : Fin (2^m-1) → Finset (Fin (2^m-1))) (Q : Fin (2^m-1) → Word m),
    (∀ i, i ∉ D i) ∧
    (∀ i, (univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, (univ.filter (fun i => j ∈ D i)).card = m-1) ∧
    ∑ i, (D i).card = (2^m-1)*(m-1) ∧
    (∀ U, uniform (2^m-1) m D Q U ↔ U = univ) := by
  have hcard : Fintype.card (NZ m) = 2^m - 1 := by
    rw [Fintype.card_subtype, card_nz]
  let σ : Fin (2^m-1) ≃ NZ m := (Fintype.equivFinOfCardEq hcard).symm
  have hread : ∀ j, (univ.filter (fun i => j ∈ Ds σ i)).card = m - 1 := by
    intro j
    have : univ.filter (fun i => j ∈ Ds σ i) = Rs σ j := by
      ext i; simp [Ds]
    rw [this, Rs_card]
  refine ⟨Ds σ, Qs σ, ?_, fun i => Qp_wt _, hread, ?_, ?_⟩
  · intro i hi
    have := Rs_dot σ i i (Finset.mem_filter.1 hi).2
    rw [Qs_dot] at this
    exact one_ne_zero this
  · rw [wires_eq]
    simp only [hread, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  · intro U
    rw [uniform_iff, cond_iff]

end PEqualNP.Outside.L_lib_1095

theorem PEqualNP.Outside.L_lib_1095 : let Word := fun k : Nat => Fin k → ZMod 2
let localRule := fun (n : Nat) (D : Fin n → Finset (Fin n)) (T : Fin n → Word n → ZMod 2) =>
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
let observed := fun (n m : Nat) (Q : Fin n → Word m) (U : Finset (Fin n))
    (T : Fin n → Word n → ZMod 2) (b : Word n) (z : U → ZMod 2) (r : Fin m) =>
  let x := fun i : Fin n => if h : i ∈ U then z ⟨i,h⟩ else b i
  ∑ i, (x i + T i x) * Q i r
let uniform := fun (n m : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m)
    (U : Finset (Fin n)) =>
  ∀ T, localRule n D T → ∀ b v,
    2^m * Nat.card {z : U → ZMod 2 // observed n m Q U T b z = v} = 2^U.card
let readers := fun (n : Nat) (D : Fin n → Finset (Fin n)) (j : Fin n) =>
  (Finset.univ.filter (fun i => j ∈ D i)).card
let wires := fun (n : Nat) (D : Fin n → Finset (Fin n)) => ∑ i, (D i).card
∀ m : Nat, 1 ≤ m →
  let N := 2^m - 1
  (∃ (D : Fin N → Finset (Fin N)) (Q : Fin N → Word m),
    (∀ i, i ∉ D i) ∧
    (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, readers N D j = m-1) ∧ wires N D = N*(m-1) ∧
    (∀ U, uniform N m D Q U ↔ U = Finset.univ)) ∧
  (∀ (n : Nat) (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) (W : Finset (Fin n)),
    W.card = N → uniform n m D Q Finset.univ →
    (∀ j ∈ W, ¬ uniform n m D Q (Finset.univ.erase j)) →
    N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D) := by
  intro Word localRule observed uniform readers wires m hm N
  exact ⟨PEqualNP.Outside.L_lib_1095.part1 m,
    fun n D Q W hW hu hj => PEqualNP.Outside.L_lib_1095.part2 m n D Q W hW hu hj⟩
