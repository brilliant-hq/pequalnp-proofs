import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1095_aux

abbrev V (q : ℕ) : Type := Fin q → ZMod 2

def dot {q : ℕ} (a x : V q) : ZMod 2 := ∑ i, a i * x i

def chi {q : ℕ} (a x : V q) : ℚ := if dot a x = 0 then 1 else -1

lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

lemma v_add_self {q : ℕ} (a : V q) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (a i) with h | h <;> rw [h] <;> decide

lemma dot_comm {q : ℕ} (a x : V q) : dot a x = dot x a := by
  simp only [dot, mul_comm]

lemma dot_zero_left {q : ℕ} (x : V q) : dot (0 : V q) x = 0 := by
  simp [dot]

lemma dot_add_left {q : ℕ} (a b x : V q) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {q : ℕ} (a x y : V q) : dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma chi_zero {q : ℕ} (x : V q) : chi (0 : V q) x = 1 := by
  simp [chi, dot_zero_left]

lemma chi_mul_right {q : ℕ} (a x y : V q) : chi a (x + y) = chi a x * chi a y := by
  unfold chi
  rw [dot_add_right]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with hx | hx <;> rcases zmod2_cases (dot a y) with hy | hy <;>
    simp [hx, hy, h11]

lemma card_V (q : ℕ) : (Fintype.card (V q) : ℚ) = (2 : ℚ) ^ q := by
  have h : Fintype.card (V q) = 2 ^ q := by
    simp [V, ZMod.card]
  exact_mod_cast h

lemma sum_chi {q : ℕ} (a : V q) :
    ∑ x : V q, chi a x = if a = 0 then (2 : ℚ) ^ q else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ↓reduceIte]
    exact card_V q
  · simp only [ha, ↓reduceIte]
    have hex : ∃ i : Fin q, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    have hai : a i = 1 := by
      rcases zmod2_cases (a i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    let e : V q := Pi.single i (1 : ZMod 2)
    have hdot_e : dot a e = 1 := by
      unfold dot
      rw [Finset.sum_eq_single i]
      · simp [e, hai]
      · intro j _ hji
        simp [e, Pi.single_eq_of_ne hji]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have hchi_e : chi a e = -1 := by
      unfold chi
      rw [hdot_e]
      norm_num
    let eqv : V q ≃ V q :=
      { toFun := fun x => x + e
        invFun := fun x => x + e
        left_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero]
        right_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero] }
    have hsum : ∑ x : V q, chi a x = ∑ x : V q, chi a (x + e) :=
      (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : V q, chi a (x + e) = -(∑ x : V q, chi a x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_mul_right, hchi_e]
      ring
    linarith

lemma chi_comm {q : ℕ} (a x : V q) : chi a x = chi x a := by
  simp only [chi, dot_comm]

lemma inversion {X : Type} [Fintype X] {q : ℕ} (F : X → V q)
    (h : ∀ a : V q, a ≠ 0 → ∑ x, chi a (F x) = 0) (v : V q) :
    (2 : ℚ) ^ q * ((Finset.univ.filter (fun x => F x = v)).card : ℚ) = Fintype.card X := by
  have hind : ∀ x, (2 : ℚ) ^ q * (if F x = v then 1 else 0) = ∑ a : V q, chi a v * chi a (F x) := by
    intro x
    have h1 : ∀ a : V q, chi a v * chi a (F x) = chi (F x + v) a := by
      intro a
      rw [← chi_mul_right, chi_comm, add_comm]
    simp only [h1]
    rw [sum_chi]
    have h2 : F x + v = 0 ↔ F x = v := by
      constructor
      · intro hh
        have := congrArg (· + v) hh
        simpa [add_assoc, v_add_self] using this
      · intro hh; rw [hh, v_add_self]
    by_cases hx : F x = v
    · simp [hx, v_add_self]
    · simp [hx, h2]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  have h3 : ∀ x ∈ (Finset.univ : Finset X),
      (2 : ℚ) ^ q * (((if F x = v then 1 else 0 : ℕ)) : ℚ) = ∑ a : V q, chi a v * chi a (F x) := by
    intro x _
    rw [← hind x]; push_cast; rfl
  rw [Finset.sum_congr rfl h3, Finset.sum_comm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V q))]
  have h4 : ∑ a ∈ Finset.univ.erase (0 : V q), ∑ x : X, chi a v * chi a (F x) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [← Finset.mul_sum, h a (Finset.mem_erase.mp ha).1, mul_zero]
  rw [h4]
  simp [chi_zero]

lemma v_add_self' {α : Type} (a : α → ZMod 2) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (a i) with h | h <;> rw [h] <;> decide

def xOf {n : ℕ} (U : Finset (Fin n)) (b : Fin n → ZMod 2) (z : U → ZMod 2) : Fin n → ZMod 2 :=
  fun i => if h : i ∈ U then z ⟨i, h⟩ else b i

def obsF (n m : ℕ) (Q : Fin n → V m) (U : Finset (Fin n))
    (T : Fin n → (Fin n → ZMod 2) → ZMod 2) (b : Fin n → ZMod 2) (z : U → ZMod 2) : V m :=
  fun r => ∑ i, (xOf U b z i + T i (xOf U b z)) * Q i r

def Loc (n : ℕ) (D : Fin n → Finset (Fin n)) (T : Fin n → (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

def Unif (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) : Prop :=
  ∀ T, Loc n D T → ∀ b v, 2^m * Nat.card {z : U → ZMod 2 // obsF n m Q U T b z = v} = 2^U.card

def Crit (n m : ℕ) (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) : Prop :=
  ∀ a : V m, a ≠ 0 → ∃ k ∈ U, dot a (Q k) = 1 ∧ ∀ i, dot a (Q i) = 1 → k ∉ D i

lemma dot_obs {n m : ℕ} (Q : Fin n → V m) (U : Finset (Fin n))
    (T : Fin n → (Fin n → ZMod 2) → ZMod 2) (b : Fin n → ZMod 2) (z : U → ZMod 2) (a : V m) :
    dot a (obsF n m Q U T b z) = ∑ i, (xOf U b z i + T i (xOf U b z)) * dot a (Q i) := by
  simp only [dot, obsF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by ring

lemma ne_zero_one (c : ZMod 2) (h : c ≠ 1) : c = 0 := by
  rcases zmod2_cases c with h1 | h1
  · exact h1
  · exact absurd h1 h

lemma balance {n m : ℕ} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n))
    (T : Fin n → (Fin n → ZMod 2) → ZMod 2) (hT : Loc n D T) (b : Fin n → ZMod 2) (a : V m)
    (k : Fin n) (hk : k ∈ U) (hsk : dot a (Q k) = 1) (hr : ∀ i, dot a (Q i) = 1 → k ∉ D i) :
    ∑ z : U → ZMod 2, chi a (obsF n m Q U T b z) = 0 := by
  let e : U → ZMod 2 := Pi.single (⟨k, hk⟩ : U) 1
  let s : Fin n → ZMod 2 := Pi.single k 1
  have hx : ∀ z, xOf U b (z + e) = xOf U b z + s := by
    intro z
    funext i
    by_cases hi : i ∈ U
    · by_cases hik : i = k
      · subst hik
        simp [xOf, hi, e, s]
      · have hne : (⟨i, hi⟩ : U) ≠ ⟨k, hk⟩ := fun h => hik (congrArg Subtype.val h)
        simp [xOf, hi, e, s, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hik]
    · have hik : i ≠ k := fun h => hi (h ▸ hk)
      simp [xOf, hi, s, Pi.single_eq_of_ne hik]
  have hstep : ∀ z, dot a (obsF n m Q U T b (z + e)) = dot a (obsF n m Q U T b z) + 1 := by
    intro z
    rw [dot_obs, dot_obs, hx]
    have hterm : ∀ i, (((xOf U b z + s) i + T i (xOf U b z + s)) *
        dot a (Q i)) = (xOf U b z i + T i (xOf U b z)) * dot a (Q i) +
          s i * dot a (Q i) := by
      intro i
      rcases zmod2_cases (dot a (Q i)) with h0 | h1
      · rw [h0]; ring
      · have hTi : T i (xOf U b z + Pi.single k 1) = T i (xOf U b z) := by
          apply hT
          intro j hj
          have hjk : j ≠ k := fun h => hr i h1 (h ▸ hj)
          simp [Pi.single_eq_of_ne hjk]
        rw [hTi, Pi.add_apply]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single k]
    · simp [s, hsk]
    · intro i _ hik; simp [s, Pi.single_eq_of_ne hik]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hchi : ∀ z, chi a (obsF n m Q U T b (z + e)) = - chi a (obsF n m Q U T b z) := by
    intro z
    unfold chi
    rw [hstep]
    rcases zmod2_cases (dot a (obsF n m Q U T b z)) with h0 | h1
    · rw [h0]; norm_num
    · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [h1, h11]; norm_num
  have ve : ∀ w : U → ZMod 2, w + e + e = w := by
    intro w
    rw [add_assoc, v_add_self', add_zero]
  let eqv : (U → ZMod 2) ≃ (U → ZMod 2) :=
    { toFun := fun z => z + e
      invFun := fun z => z + e
      left_inv := fun z => ve z
      right_inv := fun z => ve z }
  have hsum : ∑ z : U → ZMod 2, chi a (obsF n m Q U T b z) =
      ∑ z : U → ZMod 2, chi a (obsF n m Q U T b (z + e)) :=
    (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm
  have hneg : ∑ z : U → ZMod 2, chi a (obsF n m Q U T b (z + e)) =
      -∑ z : U → ZMod 2, chi a (obsF n m Q U T b z) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => hchi z
  linarith

lemma crit_to_unif {n m : ℕ} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n))
    (h : Crit n m D Q U) : Unif n m D Q U := by
  intro T hT b v
  have hinv := inversion (fun z : U → ZMod 2 => obsF n m Q U T b z) (by
    intro a ha
    obtain ⟨k, hk, hsk, hr⟩ := h a ha
    exact balance D Q U T hT b a k hk hsk hr) v
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hc : Fintype.card (U → ZMod 2) = 2 ^ U.card := by
    simp [ZMod.card]
  rw [hc] at hinv
  exact_mod_cast hinv

lemma unif_to_crit {n m : ℕ} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n))
    (h : Unif n m D Q U) : Crit n m D Q U := by
  intro a ha
  let b : Fin n → ZMod 2 := fun _ => 0
  by_contra hcon
  push Not at hcon
  have H : ∀ k, k ∈ U ∧ dot a (Q k) = 1 → ∃ i, dot a (Q i) = 1 ∧ k ∈ D i := by
    intro k hk
    obtain ⟨i, hi1, hi2⟩ := hcon k hk.1 hk.2
    exact ⟨i, hi1, hi2⟩
  let r : Fin n → Fin n := fun k =>
    if hk : k ∈ U ∧ dot a (Q k) = 1 then Classical.choose (H k hk) else k
  have hr : ∀ k, k ∈ U ∧ dot a (Q k) = 1 → dot a (Q (r k)) = 1 ∧ k ∈ D (r k) := by
    intro k hk
    simp only [r, hk]
    exact Classical.choose_spec (H k hk)
  let T : Fin n → (Fin n → ZMod 2) → ZMod 2 := fun i x =>
    ∑ k, if (k ∈ U ∧ dot a (Q k) = 1) ∧ r k = i then x k else 0
  have hT : Loc n D T := by
    intro i x y hxy
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hc : (k ∈ U ∧ dot a (Q k) = 1) ∧ r k = i
    · rw [if_pos hc, if_pos hc]
      have := (hr k hc.1).2
      rw [hc.2] at this
      exact hxy k this
    · rw [if_neg hc, if_neg hc]
  let C : ZMod 2 := ∑ k, if k ∈ U then 0 else b k * dot a (Q k)
  have hconst : ∀ z, dot a (obsF n m Q U T b z) = C := by
    intro z
    rw [dot_obs]
    simp only [T, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i k => (if (k ∈ U ∧ dot a (Q k) = 1) ∧ r k = i
      then xOf U b z k else 0) * dot a (Q i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hin : ∑ i, (if (k ∈ U ∧ dot a (Q k) = 1) ∧ r k = i then xOf U b z k else 0) * dot a (Q i)
        = if k ∈ U ∧ dot a (Q k) = 1 then xOf U b z k else 0 := by
      by_cases hc : k ∈ U ∧ dot a (Q k) = 1
      · rw [Finset.sum_eq_single (r k)]
        · simp [hc, (hr k hc).1]
        · intro i _ hi
          have : ¬ r k = i := fun h => hi h.symm
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp [hc]
    rw [hin]
    by_cases hkU : k ∈ U
    · simp only [hkU, if_true, true_and]
      rcases zmod2_cases (dot a (Q k)) with h0 | h1
      · simp [h0]
      · simp only [h1, if_true, mul_one]
        rw [← two_mul]
        have : (2 : ZMod 2) = 0 := rfl
        rw [this, zero_mul]
    · simp [hkU, xOf]
  obtain ⟨r0, hr0⟩ : ∃ r0, a r0 = 1 := by
    by_contra hh
    push Not at hh
    exact ha (funext fun r => ne_zero_one _ (hh r))
  let v : V m := if C = 0 then Pi.single r0 1 else 0
  have hv : dot a v ≠ C := by
    by_cases hC : C = 0
    · have : dot a (Pi.single r0 1) = 1 := by
        unfold dot
        rw [Finset.sum_eq_single r0]
        · simp [hr0]
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [v, hC, if_true, this]
      decide
    · simp only [v, hC, if_false]
      rw [dot_comm, dot_zero_left]
      exact fun h => hC h.symm
  have h0 := h T hT b v
  have hempty : Nat.card {z : U → ZMod 2 // obsF n m Q U T b z = v} = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    intro ⟨z, hz⟩
    exact hv (hz ▸ hconst z)
  rw [hempty, mul_zero] at h0
  exact absurd h0.symm (by positivity)

lemma unif_iff {n m : ℕ} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) :
    Unif n m D Q U ↔ Crit n m D Q U :=
  ⟨unif_to_crit D Q U, crit_to_unif D Q U⟩

lemma zz (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with h | h <;> rw [h] <;> decide

lemma wires_eq {n : ℕ} (D : Fin n → Finset (Fin n)) :
    ∑ i, (D i).card = ∑ j, (Finset.univ.filter (fun i => j ∈ D i)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext j; simp

lemma lower {m n : ℕ} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (W : Finset (Fin n))
    (hW : W.card = 2 ^ m - 1) (hU : Unif n m D Q Finset.univ)
    (hj : ∀ j ∈ W, ¬ Unif n m D Q (Finset.univ.erase j)) :
    2 ^ m - 1 ≤ n ∧ (∀ j ∈ W, m - 1 ≤ (Finset.univ.filter (fun i => j ∈ D i)).card) ∧
      (2 ^ m - 1) * (m - 1) ≤ ∑ i, (D i).card := by
  have hall : Crit n m D Q Finset.univ := unif_to_crit _ _ _ hU
  have hP : ∀ j ∈ W, ∃ a : V m, a ≠ 0 ∧
      ∀ k, k ≠ j → dot a (Q k) = 1 → ∃ i, dot a (Q i) = 1 ∧ k ∈ D i := by
    intro j hj'
    have h := hj j hj'
    rw [unif_iff] at h
    unfold Crit at h
    push Not at h
    obtain ⟨a, ha, hk⟩ := h
    refine ⟨a, ha, fun k hkj hk1 => ?_⟩
    exact hk k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩) hk1
  choose! f hf0 hfP using hP
  have hpriv : ∀ j ∈ W, dot (f j) (Q j) = 1 ∧ ∀ i, dot (f j) (Q i) = 1 → j ∉ D i := by
    intro j hjW
    obtain ⟨k, -, hk1, hk2⟩ := hall (f j) (hf0 j hjW)
    by_cases hkj : k = j
    · subst hkj; exact ⟨hk1, hk2⟩
    · obtain ⟨i, hi1, hi2⟩ := hfP j hjW k hkj hk1
      exact absurd hi2 (hk2 i hi1)
  have huniq : ∀ j j' : Fin n, ∀ a : V m, dot a (Q j) = 1 → (∀ i, dot a (Q i) = 1 → j ∉ D i) →
      (∀ k, k ≠ j' → dot a (Q k) = 1 → ∃ i, dot a (Q i) = 1 ∧ k ∈ D i) → j = j' := by
    intro j j' a h1 h2 h3
    by_contra hne
    obtain ⟨i, hi1, hi2⟩ := h3 j hne h1
    exact h2 i hi1 hi2
  have hinj : Set.InjOn f W := by
    intro j hjW j' hj'W heq
    have hp := hpriv j hjW
    have h3 := hfP j' hj'W
    rw [← heq] at h3
    exact huniq j j' (f j) hp.1 hp.2 h3
  have himg : W.image f = Finset.univ.filter (fun a : V m => a ≠ 0) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_image] at ha
      obtain ⟨j, hjW, rfl⟩ := ha
      simp [hf0 j hjW]
    · rw [Finset.card_image_of_injOn hinj, hW, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [ZMod.card]
  have hsurj : ∀ a : V m, a ≠ 0 → ∃ j ∈ W, f j = a := by
    intro a ha
    have : a ∈ W.image f := by rw [himg]; simp [ha]
    simpa using this
  have hread : ∀ j ∈ W, m - 1 ≤ (Finset.univ.filter (fun i => j ∈ D i)).card := by
    intro j hjW
    set R := Finset.univ.filter (fun i => j ∈ D i) with hR
    obtain ⟨hj1, hj2⟩ := hpriv j hjW
    have hzero : ∀ i ∈ R, dot (f j) (Q i) = 0 := by
      intro i hi
      apply ne_zero_one
      intro h1
      exact hj2 i h1 (Finset.mem_filter.mp hi).2
    let L : V m → (R → ZMod 2) × ZMod 2 := fun a => (fun i => dot a (Q i.1), dot a (Q j))
    have hLinj : Function.Injective L := by
      intro a a' hL
      simp only [L, Prod.mk.injEq] at hL
      obtain ⟨hL1, hL2⟩ := hL
      let c := f j + (a + a')
      have hcR : ∀ i ∈ R, dot c (Q i) = dot (f j) (Q i) := by
        intro i hi
        have h := congrFun hL1 ⟨i, hi⟩
        simp only at h
        simp only [c, dot_add_left, h, zz, add_zero]
      have hcj : dot c (Q j) = 1 := by
        simp only [c, dot_add_left, hL2, zz, add_zero, hj1]
      have hc0 : c ≠ 0 := fun h => by
        rw [h, dot_zero_left] at hcj
        exact absurd hcj (by decide)
      obtain ⟨j', hj'W, hfj'⟩ := hsurj c hc0
      have hjj : j' = j := by
        by_contra hne
        obtain ⟨i, hi1, hi2⟩ := hfP j' hj'W j (Ne.symm hne) (hfj' ▸ hcj)
        rw [hfj'] at hi1
        have hiR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi2⟩
        rw [hcR i hiR, hzero i hiR] at hi1
        exact absurd hi1 (by decide)
      rw [hjj] at hfj'
      have hsum : a + a' = 0 := by
        have h2 : f j + (a + a') = f j + 0 := by rw [add_zero]; exact hfj'.symm
        exact add_left_cancel h2
      calc a = a + 0 := (add_zero a).symm
        _ = a + (a' + a') := by rw [v_add_self]
        _ = (a + a') + a' := by rw [add_assoc]
        _ = a' := by rw [hsum, zero_add]
    have hcard := Fintype.card_le_of_injective L hLinj
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_coe,
      Fintype.card_fin] at hcard
    have h2 : 2 ^ m ≤ 2 ^ (R.card + 1) := by rw [pow_succ]; exact hcard
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  refine ⟨?_, hread, ?_⟩
  · have := Finset.card_le_univ W
    simp only [Fintype.card_fin] at this
    omega
  · rw [wires_eq]
    calc (2 ^ m - 1) * (m - 1) = ∑ _j ∈ W, (m - 1) := by simp [hW]
      _ ≤ ∑ j ∈ W, (Finset.univ.filter (fun i => j ∈ D i)).card := Finset.sum_le_sum hread
      _ ≤ ∑ j, (Finset.univ.filter (fun i => j ∈ D i)).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma h10 : (1 : ZMod 2) ≠ 0 := by decide

def ev {m : ℕ} (q : Fin m) : V m := fun r => if r = q then 1 else 0
def uM {m : ℕ} (q : Fin m) : V m := fun r => if r ≤ q then 1 else 0
def hM {m : ℕ} (p q : Fin m) : V m := fun r => if r ≤ q ∧ r ≠ p then 1 else 0

noncomputable def Qm {m : ℕ} (c : V m) : V m := by
  classical
  exact (if h : ∃ q, uM q = c then ev (Classical.choose h)
    else if h2 : ∃ pq : Fin m × Fin m, pq.1 < pq.2 ∧ hM pq.1 pq.2 = c then
      ev (Classical.choose h2).1 + ev (Classical.choose h2).2
    else if h3 : ∃ r, c r = 1 then ev (Classical.choose h3) else 0)

def gam {m : ℕ} (c : V m) (p r : Fin m) : V m :=
  if c r = 0 ∨ r = p then uM r else hM (min p r) (max p r)

def bet {m : ℕ} (c : V m) (p r : Fin m) : V m :=
  if c r = 0 then ev r else ev p + ev r

lemma ite_key {P R : Prop} [Decidable P] [Decidable R]
    (h : (if P then (1 : ZMod 2) else 0) = if R then 1 else 0) : P ↔ R := by
  by_cases hp : P <;> by_cases hq : R <;> simp_all [h10.symm]

lemma dot_ev {m : ℕ} (c : V m) (q : Fin m) : dot c (ev q) = c q := by
  simp [dot, ev]

lemma uM_inj {m : ℕ} {q q' : Fin m} (H : uM q = uM q') : q = q' := by
  have key : ∀ x, (x ≤ q ↔ x ≤ q') := fun x => ite_key (congrFun H x)
  exact le_antisymm ((key q).mp le_rfl) ((key q').mpr le_rfl)

lemma hM_inj {m : ℕ} {p q p' q' : Fin m} (hpq : p < q) (hpq' : p' < q')
    (H : hM p q = hM p' q') : p = p' ∧ q = q' := by
  have key : ∀ x, (x ≤ q ∧ x ≠ p ↔ x ≤ q' ∧ x ≠ p') := fun x => ite_key (congrFun H x)
  have h1 : q' ≤ q := ((key q').mpr ⟨le_rfl, ne_of_gt hpq'⟩).1
  have h2 : q ≤ q' := ((key q).mp ⟨le_rfl, ne_of_gt hpq⟩).1
  have hq : q = q' := le_antisymm h2 h1
  refine ⟨?_, hq⟩
  by_contra hne
  have := (key p).mpr ⟨hq ▸ le_of_lt hpq, hne⟩
  exact this.2 rfl

lemma uM_ne_hM {m : ℕ} {p q q' : Fin m} (hpq : p < q) : uM q' ≠ hM p q := by
  intro H
  have key : ∀ x, (x ≤ q' ↔ x ≤ q ∧ x ≠ p) := fun x => ite_key (congrFun H x)
  have h1 : q ≤ q' := (key q).mpr ⟨le_rfl, ne_of_gt hpq⟩
  have := (key p).mp (le_trans (le_of_lt hpq) h1)
  exact this.2 rfl

lemma Q3 {m : ℕ} (q : Fin m) : Qm (uM q) = ev q := by
  have h : ∃ q', uM q' = uM q := ⟨q, rfl⟩
  unfold Qm
  rw [dif_pos h]
  rw [uM_inj (Classical.choose_spec h)]

lemma Q4 {m : ℕ} {p q : Fin m} (hpq : p < q) : Qm (hM p q) = ev p + ev q := by
  have hn : ¬ ∃ q', uM q' = hM p q := fun ⟨q', h⟩ => uM_ne_hM hpq h
  have h : ∃ pq : Fin m × Fin m, pq.1 < pq.2 ∧ hM pq.1 pq.2 = hM p q := ⟨(p, q), hpq, rfl⟩
  unfold Qm
  rw [dif_neg hn, dif_pos h]
  obtain ⟨hlt, heq⟩ := Classical.choose_spec h
  obtain ⟨e1, e2⟩ := hM_inj hlt hpq heq
  rw [e1, e2]

lemma Q1 {m : ℕ} (c : V m) (hc : c ≠ 0) : dot c (Qm c) = 1 := by
  unfold Qm
  split_ifs with h1 h2 h3
  · rw [dot_ev]
    have hs := Classical.choose_spec h1
    generalize Classical.choose h1 = q at hs ⊢
    rw [← hs]
    simp [uM]
  · obtain ⟨hlt, hs⟩ := Classical.choose_spec h2
    rw [dot_add_right, dot_ev, dot_ev]
    generalize Classical.choose h2 = pq at hlt hs ⊢
    rw [← hs]
    simp [hM, (ne_of_lt hlt).symm]
  · rw [dot_ev]; exact Classical.choose_spec h3
  · exfalso
    apply hc
    funext r
    have := not_exists.mp h3 r
    exact ne_zero_one _ this

lemma card_le2 {m : ℕ} (f : V m) (a b : Fin m) (h : ∀ r, f r ≠ 0 → r = a ∨ r = b) :
    (Finset.univ.filter (fun r => f r ≠ 0)).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {a, b}) ?_) Finset.card_le_two
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  simpa using h r hr

lemma Q2 {m : ℕ} (c : V m) : (Finset.univ.filter (fun r => Qm c r ≠ 0)).card ≤ 2 := by
  unfold Qm
  split_ifs with h1 h2 h3
  · refine card_le2 _ (Classical.choose h1) (Classical.choose h1) fun r hr => ?_
    left; by_contra hne; exact hr (by simp [ev, hne])
  · refine card_le2 _ (Classical.choose h2).1 (Classical.choose h2).2 fun r hr => ?_
    by_contra hne
    push Not at hne
    exact hr (by simp [ev, hne.1, hne.2])
  · refine card_le2 _ (Classical.choose h3) (Classical.choose h3) fun r hr => ?_
    left; by_contra hne; exact hr (by simp [ev, hne])
  · simp

lemma gam_ne {m : ℕ} (c : V m) (p r : Fin m) : gam c p r ≠ 0 := by
  unfold gam
  split_ifs with h
  · intro h0
    have := congrFun h0 r
    simp [uM] at this
  · have hr : r ≠ p := fun hh => h (Or.inr hh)
    intro h0
    rcases lt_or_gt_of_ne hr with hl | hl
    · rw [min_eq_right (le_of_lt hl), max_eq_left (le_of_lt hl)] at h0
      have := congrFun h0 p
      simp [hM, (ne_of_lt hl).symm] at this
    · rw [min_eq_left (le_of_lt hl), max_eq_right (le_of_lt hl)] at h0
      have := congrFun h0 r
      simp [hM, hr] at this

lemma Qm_gam {m : ℕ} (c : V m) {p r : Fin m} (hr : r ≠ p) : Qm (gam c p r) = bet c p r := by
  unfold gam bet
  by_cases hcr : c r = 0
  · simp only [hcr, true_or, if_true]
    exact Q3 r
  · have hn : ¬ (c r = 0 ∨ r = p) := fun hh => hh.elim hcr hr
    rw [if_neg hn, if_neg hcr]
    rcases lt_or_gt_of_ne hr with hl | hl
    · rw [min_eq_right (le_of_lt hl), max_eq_left (le_of_lt hl), Q4 hl, add_comm]
    · rw [min_eq_left (le_of_lt hl), max_eq_right (le_of_lt hl), Q4 hl]

lemma bet_inj {m : ℕ} (c : V m) {p r r' : Fin m} (hr : r ≠ p) (H : bet c p r = bet c p r') :
    r = r' := by
  by_contra hne
  have v1 : bet c p r r = 1 := by
    unfold bet; split_ifs <;> simp [ev, hr]
  have v2 : bet c p r' r = 0 := by
    unfold bet; split_ifs <;> simp [ev, hr, hne]
  rw [H, v2] at v1
  exact h10 v1.symm

lemma dot_bet_self {m : ℕ} (c : V m) {p r : Fin m} (hcp : c p = 1) : dot c (bet c p r) = 0 := by
  unfold bet
  split_ifs with hcr
  · rw [dot_ev]; exact hcr
  · rw [dot_add_right, dot_ev, dot_ev, hcp]
    rcases zmod2_cases (c r) with h | h
    · exact absurd h hcr
    · rw [h]; rfl

lemma exists_r {m : ℕ} {a c : V m} {p : Fin m} (ha : a ≠ 0) (hac : a ≠ c) (hcp : c p = 1) :
    ∃ r, r ≠ p ∧ dot a (bet c p r) = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ r, r ≠ p → dot a (bet c p r) = 0 := fun r hr => ne_zero_one _ (hcon r hr)
  rcases zmod2_cases (a p) with hap | hap
  · apply ha
    funext r
    by_cases hr : r = p
    · subst hr; simp [hap]
    · have h := h0 r hr
      unfold bet at h
      split_ifs at h with hcr
      · rw [dot_ev] at h; exact h
      · rw [dot_add_right, dot_ev, dot_ev, hap, zero_add] at h; exact h
  · apply hac
    funext r
    by_cases hr : r = p
    · subst hr; rw [hap, hcp]
    · have h := h0 r hr
      unfold bet at h
      split_ifs at h with hcr
      · rw [dot_ev] at h; rw [h, hcr]
      · rw [dot_add_right, dot_ev, dot_ev, hap] at h
        have hc1 : c r = 1 := by
          rcases zmod2_cases (c r) with h' | h'
          · exact absurd h' hcr
          · exact h'
        rw [hc1]
        rcases zmod2_cases (a r) with h' | h'
        · rw [h'] at h; exact absurd h (by decide)
        · exact h'

lemma construct (m : ℕ) : ∃ (D : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1)))
    (Q : Fin (2 ^ m - 1) → V m),
    (∀ i, i ∉ D i) ∧ (∀ i, (Finset.univ.filter (fun r => Q i r ≠ 0)).card ≤ 2) ∧
    (∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card = m - 1) ∧
    ∑ i, (D i).card = (2 ^ m - 1) * (m - 1) ∧
    (∀ U, Unif (2 ^ m - 1) m D Q U ↔ U = Finset.univ) := by
  have hcard : Fintype.card {a : V m // a ≠ 0} = 2 ^ m - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    simp [ZMod.card]
  let e : Fin (2 ^ m - 1) ≃ {a : V m // a ≠ 0} := (Fintype.equivFinOfCardEq hcard).symm
  let μ : Fin (2 ^ m - 1) → V m := fun i => (e i).1
  have hμ0 : ∀ i, μ i ≠ 0 := fun i => (e i).2
  have hμe : ∀ v (h : v ≠ 0), μ (e.symm ⟨v, h⟩) = v := by
    intro v h; simp [μ]
  have hex : ∀ i, ∃ p, μ i p = 1 := by
    intro i
    by_contra hh
    push Not at hh
    exact hμ0 i (funext fun r => ne_zero_one _ (hh r))
  choose p hp using hex
  let R : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1)) := fun j =>
    (Finset.univ.erase (p j)).image (fun r => e.symm ⟨gam (μ j) (p j) r, gam_ne _ _ _⟩)
  have hmemR : ∀ i j, i ∈ R j ↔ ∃ r, r ≠ p j ∧ e.symm ⟨gam (μ j) (p j) r, gam_ne _ _ _⟩ = i := by
    intro i j
    simp [R]
  let D : Fin (2 ^ m - 1) → Finset (Fin (2 ^ m - 1)) := fun i =>
    Finset.univ.filter (fun j => i ∈ R j)
  have hD : ∀ i j, j ∈ D i ↔ i ∈ R j := by intro i j; simp [D]
  let Q : Fin (2 ^ m - 1) → V m := fun i => Qm (μ i)

  have hQR : ∀ i j, i ∈ R j → ∃ r, r ≠ p j ∧ Q i = bet (μ j) (p j) r := by
    intro i j hi
    obtain ⟨r, hr, rfl⟩ := (hmemR i j).mp hi
    exact ⟨r, hr, by simp only [Q]; rw [hμe, Qm_gam _ hr]⟩
  have hreaders : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card = m - 1 := by
    intro j
    have hfe : Finset.univ.filter (fun i => j ∈ D i) = R j := by
      ext i; simp [hD]
    rw [hfe]
    simp only [R]
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    intro r hr r' hr' heq
    have hr1 : r ≠ p j := (Finset.mem_erase.mp hr).1
    have h1 := congrArg Subtype.val (e.symm.injective heq)
    simp only at h1
    have h2 := congrArg Qm h1
    rw [Qm_gam _ hr1, Qm_gam _ (Finset.mem_erase.mp hr').1] at h2
    exact bet_inj _ hr1 h2
  refine ⟨D, Q, ?_, ?_, hreaders, ?_, ?_⟩
  · intro i hi
    rw [hD] at hi
    obtain ⟨r, hr, hQ⟩ := hQR i i hi
    have h1 := Q1 (μ i) (hμ0 i)
    have h2 : Qm (μ i) = Q i := rfl
    rw [h2, hQ, dot_bet_self _ (hp i)] at h1
    exact h10 h1.symm
  · intro i; exact Q2 _
  · rw [wires_eq]
    simp [hreaders]
  · intro U
    rw [unif_iff]
    constructor
    · intro hc
      by_contra hne
      obtain ⟨j, hj⟩ : ∃ j, j ∉ U := by
        by_contra hh
        push Not at hh
        exact hne (Finset.eq_univ_iff_forall.mpr hh)
      obtain ⟨k, hkU, _, hk2⟩ := hc (μ j) (hμ0 j)
      have hkj : k ≠ j := fun h => hj (h ▸ hkU)
      have hne' : μ j ≠ μ k := fun h => hkj (e.injective (Subtype.ext h.symm))
      obtain ⟨r, hr, hdot⟩ := exists_r (hμ0 j) hne' (hp k)
      let i := e.symm ⟨gam (μ k) (p k) r, gam_ne _ _ _⟩
      have hiR : i ∈ R k := (hmemR i k).mpr ⟨r, hr, rfl⟩
      have hQi : Q i = bet (μ k) (p k) r := by
        simp only [Q, i]; rw [hμe, Qm_gam _ hr]
      apply hk2 i (by rw [hQi]; exact hdot)
      rw [hD]; exact hiR
    · rintro rfl
      intro a ha
      refine ⟨e.symm ⟨a, ha⟩, Finset.mem_univ _, ?_, ?_⟩
      · simp only [Q]; rw [hμe]; exact Q1 a ha
      · intro i hi hk
        rw [hD] at hk
        obtain ⟨r, _, hQ⟩ := hQR _ _ hk
        rw [hQ, hμe] at hi
        have := dot_bet_self a (r := r) (by have := hp (e.symm ⟨a, ha⟩); rwa [hμe] at this)
        rw [hi] at this
        exact h10 this

end PEqualNP.Outside.L_lib_1095_aux

theorem PEqualNP.Outside.L_lib_1095 : (let Word := fun k : Nat => Fin k → ZMod 2
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
    N ≤ n ∧ (∀ j ∈ W, m-1 ≤ readers n D j) ∧ N*(m-1) ≤ wires n D)) := by
  intro Word localRule observed uniform readers wires m _hm N
  obtain ⟨D, Q, h1, h2, h3, h4, h5⟩ := PEqualNP.Outside.L_lib_1095_aux.construct m
  refine ⟨⟨D, Q, h1, h2, h3, h4, h5⟩, ?_⟩
  intro n D' Q' W hW hU hj
  exact PEqualNP.Outside.L_lib_1095_aux.lower D' Q' W hW hU hj
