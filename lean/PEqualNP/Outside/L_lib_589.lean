import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_589

open Classical

abbrev W (n : ℕ) := Fin n → Bool
abbrev Lit (n : ℕ) := Fin n × Bool
abbrev Formula (n : ℕ) := Finset (Lit n × Lit n)
abbrev Vec (d : ℕ) := Fin d → Bool

def sat {n : ℕ} (C : Formula n) (w : W n) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

def sol {n : ℕ} (G : Formula n) : Finset (W n) :=
  Finset.univ.filter (fun x => sat G x = true)

def high {n : ℕ} (s : ℕ) (G : Formula n) : Prop :=
  2 ^ n * (2 ^ (s - 1) + 1) ≤ 2 ^ s * (sol G).card

abbrev q1 (n : ℕ) : ℕ := 16 * (1 + 4 * (1 + Nat.clog 2 (n + 1)))
abbrev tBlocks (n s : ℕ) : ℕ := 8 + Nat.clog 2 (n - s + 1)
abbrev mSeeds (n s : ℕ) : ℕ := 2 ^ Nat.clog 2 (4 + (s + 4) * (1 + Nat.clog 2 (n + 1)))

lemma sat_eq_true_iff {n : ℕ} {C : Formula n} {w : W n} :
    sat C w = true ↔ ∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  simp only [sat, decide_eq_true_eq]

lemma sat_eq_false_iff {n : ℕ} {C : Formula n} {w : W n} :
    sat C w = false ↔ ∃ c ∈ C, w c.1.1 = c.1.2 ∧ w c.2.1 = c.2.2 := by
  rw [Bool.eq_false_iff, ne_eq, sat_eq_true_iff]
  push Not
  rfl

lemma bool_ne_or_ne (x a b : Bool) (h : a ≠ b) : x ≠ a ∨ x ≠ b := by
  cases x <;> cases a <;> cases b <;> simp_all

lemma bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

lemma bool_eq_of_ne_not {x y : Bool} (h : x ≠ !y) : x = y := by
  cases x <;> cases y <;> simp_all

lemma decide_eq_true_bool (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

lemma card_filter_add_card_filter_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hx : p x <;> simp [hx]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    exact hx2.2 hx1.2

lemma card_subcube {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Bool) :
    (Finset.univ.filter (fun w : W n => ∀ i ∈ S, w i = f i)).card = 2 ^ (n - S.card) := by
  have heq : (Finset.univ.filter (fun w : W n => ∀ i ∈ S, w i = f i)).card =
      Fintype.card {w : W n // ∀ i ∈ S, w i = f i} := by
    rw [Fintype.card_subtype]
  rw [heq]
  let e : {w : W n // ∀ i ∈ S, w i = f i} ≃ ({i : Fin n // i ∉ S} → Bool) :=
    { toFun := fun w i => w.1 i.1
      invFun := fun g =>
        ⟨fun i => if h : i ∈ S then f i else g ⟨i, h⟩, by
          intro i hi
          simp [hi]⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi, w.2 i hi]
        · simp [hi]
      right_inv := fun g => by
        funext i
        simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype]
  have hcompl : (Finset.univ.filter (fun i : Fin n => i ∉ S)) = Sᶜ := by
    ext i
    simp
  rw [hcompl, Finset.card_compl, Fintype.card_fin]

lemma card_sol_gt_half_of_high {n s : ℕ} (hs : 3 ≤ s) {G : Formula n} (h : high s G) :
    2 ^ n < 2 * (sol G).card := by
  unfold high at h
  have hs1 : s = (s - 1) + 1 := by omega
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    conv_lhs => rw [hs1, pow_succ]
  rw [hpow, mul_add, mul_one, mul_assoc] at h
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlt : 2 ^ n * 2 ^ (s - 1) < 2 ^ (s - 1) * (2 * (sol G).card) := by omega
  rw [mul_comm (2 ^ n) (2 ^ (s - 1))] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma high_of_sol_subset {n s : ℕ} {H A : Formula n}
    (hsub : ∀ z, sat H z = true → sat A z = true) (hH : high s H) : high s A := by
  unfold high at hH ⊢
  have hcard : (sol H).card ≤ (sol A).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hsub x hx
  exact le_trans hH (Nat.mul_le_mul_left _ hcard)

lemma high_congr {n s : ℕ} {A B : Formula n} (h : ∀ z, sat B z = sat A z) :
    high s B ↔ high s A := by
  have hsol : sol B = sol A := by
    ext x
    simp [sol, h x]
  simp [high, hsol]

lemma card_sol_le_of_proj_pol {n k : ℕ} (G : Formula n) (f : Fin k → Fin n)
    (hf : Function.Injective f) (pol : Fin k → Bool)
    (P : (Fin k → Bool) → Prop) [DecidablePred P]
    (hP : ∀ w : W n, sat G w = true → P (fun i => decide (w (f i) = pol i))) :
    2 ^ k * (sol G).card ≤ (Finset.univ.filter P).card * 2 ^ n := by
  let proj : W n → (Fin k → Bool) := fun w i => decide (w (f i) = pol i)
  let fiber : (Fin k → Bool) → Finset (W n) :=
    fun v => Finset.univ.filter (fun w => proj w = v)
  have hsub : sol G ⊆ (Finset.univ.filter P).biUnion fiber := by
    intro w hw
    rw [Finset.mem_biUnion]
    refine ⟨proj w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hP w hw
    · simp [fiber]
  have hfiber : ∀ v : Fin k → Bool, (fiber v).card = 2 ^ (n - k) := by
    intro v
    let S : Finset (Fin n) := Finset.univ.image f
    have hScard : S.card = k := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let g : Fin n → Bool := fun j =>
      if h : ∃ i : Fin k, f i = j then
        let i := Classical.choose h
        if v i then pol i else !pol i
      else false
    have hfeq : fiber v = Finset.univ.filter (fun w : W n => ∀ j ∈ S, w j = g j) := by
      ext w
      simp only [fiber, proj, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hproj j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        have h1 : decide (w (f i) = pol i) = v i := congrFun hproj i
        have hex : ∃ i' : Fin k, f i' = f i := ⟨i, rfl⟩
        have hch : Classical.choose hex = i := hf (Classical.choose_spec hex)
        simp only [g, dif_pos hex, hch]
        cases hw : w (f i) <;> cases hp : pol i <;> cases hv : v i <;> simp_all
      · intro hall
        funext i
        have hj : f i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        have h1 := hall (f i) hj
        have hex : ∃ i' : Fin k, f i' = f i := ⟨i, rfl⟩
        have hch : Classical.choose hex = i := hf (Classical.choose_spec hex)
        simp only [g, dif_pos hex, hch] at h1
        cases hw : w (f i) <;> cases hp : pol i <;> cases hv : v i <;> simp_all
    rw [hfeq, card_subcube S g, hScard]
  have hle1 : (sol G).card ≤ (Finset.univ.filter P).card * 2 ^ (n - k) := by
    calc (sol G).card
        ≤ ((Finset.univ.filter P).biUnion fiber).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ Finset.univ.filter P, (fiber v).card := Finset.card_biUnion_le
      _ = ∑ _v ∈ Finset.univ.filter P, 2 ^ (n - k) := Finset.sum_congr rfl (fun v _ => hfiber v)
      _ = (Finset.univ.filter P).card * 2 ^ (n - k) := by simp
  have hkn : k ≤ n := by
    have := Fintype.card_le_of_injective f hf
    simpa using this
  have hpow : 2 ^ k * 2 ^ (n - k) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  calc 2 ^ k * (sol G).card
      ≤ 2 ^ k * ((Finset.univ.filter P).card * 2 ^ (n - k)) := Nat.mul_le_mul_left _ hle1
    _ = (Finset.univ.filter P).card * (2 ^ k * 2 ^ (n - k)) := by ring
    _ = (Finset.univ.filter P).card * 2 ^ n := by rw [hpow]

def Consistent4 {n : ℕ} (t : Fin 4 → Lit n) : Prop :=
  ∀ a b : Fin 4, (t a).1 = (t b).1 → (t a).2 = (t b).2

def Matches4 {n : ℕ} (t : Fin 4 → Lit n) (w : W n) : Prop :=
  ∀ a : Fin 4, w (t a).1 = (t a).2

def IsStrength4Pool {n m : ℕ} (P : Fin m → W n) : Prop :=
  ∀ t : Fin 4 → Lit n, Consistent4 t → ∃ r : Fin m, Matches4 t (P r)

lemma card_not_matches4_le {n : ℕ} (t : Fin 4 → Lit n) (ht : Consistent4 t) :
    16 * (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card ≤ 15 * 2 ^ n := by
  let S : Finset (Fin n) := Finset.univ.image (fun a : Fin 4 => (t a).1)
  have hScard : S.card ≤ 4 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by simp
  let f : Fin n → Bool := fun j =>
    if h : ∃ a : Fin 4, (t a).1 = j then (t (Classical.choose h)).2 else false
  have hmeq : Finset.univ.filter (fun w : W n => Matches4 t w) =
      Finset.univ.filter (fun w : W n => ∀ j ∈ S, w j = f j) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hw j hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      have hex : ∃ a' : Fin 4, (t a').1 = (t a).1 := ⟨a, rfl⟩
      simp only [f, dif_pos hex]
      rw [hw a]
      exact ht a (Classical.choose hex) (Classical.choose_spec hex).symm
    · intro hall a
      have hj : (t a).1 ∈ S := Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      have h1 := hall (t a).1 hj
      have hex : ∃ a' : Fin 4, (t a').1 = (t a).1 := ⟨a, rfl⟩
      simp only [f, dif_pos hex] at h1
      rw [h1]
      exact ht (Classical.choose hex) a (Classical.choose_spec hex)
  have hgood : (Finset.univ.filter (fun w : W n => Matches4 t w)).card = 2 ^ (n - S.card) := by
    rw [hmeq, card_subcube]
  have hgood16 : 2 ^ n ≤ 16 * (Finset.univ.filter (fun w : W n => Matches4 t w)).card := by
    rw [hgood]
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (Finset.univ.filter (fun w : W n => Matches4 t w)).card +
      (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card = 2 ^ n := by
    rw [card_filter_add_card_filter_not]
    simp [W]
  omega

lemma exists_strength4_pool (n : ℕ) :
    ∃ P : Fin (q1 n) → W n, IsStrength4Pool P := by
  let q := q1 n
  let badPools : Finset (Fin q → W n) :=
    Finset.univ.filter (fun P => ¬ IsStrength4Pool P)
  let miss (t : Fin 4 → Lit n) : Finset (Fin q → W n) :=
    Finset.univ.filter (fun P => ∀ r : Fin q, ¬ Matches4 t (P r))
  have hsub : badPools ⊆
      (Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).biUnion miss := by
    intro P hP
    simp only [badPools, Finset.mem_filter, Finset.mem_univ, true_and, IsStrength4Pool,
      not_forall, not_exists] at hP
    obtain ⟨t, ht, hmiss⟩ := hP
    rw [Finset.mem_biUnion]
    exact ⟨t, by simp [ht], by simp [miss, hmiss]⟩
  have hmiss_card : ∀ t : Fin 4 → Lit n,
      (miss t).card = (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card ^ q := by
    intro t
    rw [show (miss t).card = Fintype.card {P : Fin q → W n // ∀ r : Fin q, ¬ Matches4 t (P r)} by
      rw [Fintype.card_subtype]]
    let e : {P : Fin q → W n // ∀ r : Fin q, ¬ Matches4 t (P r)} ≃
        (Fin q → {w : W n // ¬ Matches4 t w}) :=
      { toFun := fun P r => ⟨P.1 r, P.2 r⟩
        invFun := fun f => ⟨fun r => (f r).1, fun r => (f r).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_subtype, Fintype.card_fin]
  have hmiss_bound : ∀ t : Fin 4 → Lit n, Consistent4 t →
      16 ^ q * (miss t).card ≤ 15 ^ q * (2 ^ n) ^ q := by
    intro t ht
    rw [hmiss_card t, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (card_not_matches4_le t ht) q
  have hbad_bound : 16 ^ q * badPools.card ≤ (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := by
    calc 16 ^ q * badPools.card
        ≤ 16 ^ q * ((Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).biUnion miss).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ 16 ^ q * ∑ t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), (miss t).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), 16 ^ q * (miss t).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), (15 ^ q * (2 ^ n) ^ q) := by
          apply Finset.sum_le_sum
          intro t ht
          exact hmiss_bound t (Finset.mem_filter.mp ht).2
      _ = (Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).card * (15 ^ q * (2 ^ n) ^ q) := by
          simp
      _ ≤ Fintype.card (Fin 4 → Lit n) * (15 ^ q * (2 ^ n) ^ q) := by
          apply Nat.mul_le_mul_right
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin 4 → Lit n)) _
      _ = (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := by
          have hcard4 : Fintype.card (Fin 4 → Lit n) = 16 * n ^ 4 := by
            simp [Lit, mul_pow]
            ring
          rw [hcard4]
  let m := 1 + 4 * (1 + Nat.clog 2 (n + 1))
  have hqm : q = 16 * m := rfl
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) (n + 1)
  have h2m : 16 * n ^ 4 < 2 ^ m := by
    have hm_eq : m = 5 + 4 * Nat.clog 2 (n + 1) := by omega
    rw [hm_eq, pow_add, mul_comm 4 _, pow_mul]
    have hpow4 : (n + 1) ^ 4 ≤ (2 ^ Nat.clog 2 (n + 1)) ^ 4 := Nat.pow_le_pow_left hclog 4
    have hlt1 : n ^ 4 < (n + 1) ^ 4 := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by norm_num)
    have h32 : 2 ^ 5 = 32 := by norm_num
    rw [h32]
    have : 16 * n ^ 4 < 32 * (n + 1) ^ 4 := by
      have : n ^ 4 + 1 ≤ (n + 1) ^ 4 := hlt1
      omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_left 32 hpow4)
  have h1516 : 2 * 15 ^ 16 ≤ 16 ^ 16 := by norm_num
  have hstrict : (16 * n ^ 4) * 15 ^ q < 16 ^ q := by
    rw [hqm, pow_mul 15 16 m, pow_mul 16 16 m]
    have h1 : (16 * n ^ 4) * (15 ^ 16) ^ m < 2 ^ m * (15 ^ 16) ^ m :=
      Nat.mul_lt_mul_of_pos_right h2m (by positivity)
    have h2 : 2 ^ m * (15 ^ 16) ^ m ≤ (16 ^ 16) ^ m := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h1516 m
    exact lt_of_lt_of_le h1 h2
  have hlt_all : badPools.card < (Finset.univ : Finset (Fin q → W n)).card := by
    have hcard_univ : (Finset.univ : Finset (Fin q → W n)).card = (2 ^ n) ^ q := by
      simp [W]
    rw [hcard_univ]
    have h1 : 16 ^ q * badPools.card < 16 ^ q * (2 ^ n) ^ q := by
      calc 16 ^ q * badPools.card
          ≤ (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := hbad_bound
        _ = ((16 * n ^ 4) * 15 ^ q) * (2 ^ n) ^ q := by ring
        _ < 16 ^ q * (2 ^ n) ^ q := Nat.mul_lt_mul_of_pos_right hstrict (by positivity)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hne : (Finset.univ \ badPools).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle : (Finset.univ : Finset (Fin q → W n)).card ≤ badPools.card := by
      have hsub2 : (Finset.univ : Finset (Fin q → W n)) ⊆ badPools :=
        Finset.sdiff_eq_empty_iff_subset.mp hemp
      exact Finset.card_le_card hsub2
    omega
  obtain ⟨P, hP⟩ := hne
  rw [Finset.mem_sdiff] at hP
  simp only [badPools, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hP
  exact ⟨P, hP⟩

def posHull {n m : ℕ} (P : Fin m → W n) (ans : Fin m → Bool) : Formula n :=
  Finset.univ.filter (fun c : Lit n × Lit n =>
    ∀ r : Fin m, ans r = true → P r c.1.1 ≠ c.1.2 ∨ P r c.2.1 ≠ c.2.2)

lemma subset_posHull {n m : ℕ} (P : Fin m → W n) (A : Formula n) :
    A ⊆ posHull P (fun r => sat A (P r)) := by
  intro c hc
  simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r hr
  exact (sat_eq_true_iff.mp hr) c hc

lemma sat_of_sat_posHull {n m : ℕ} (P : Fin m → W n) (A : Formula n) (z : W n)
    (hz : sat (posHull P (fun r => sat A (P r))) z = true) : sat A z = true := by
  rw [sat_eq_true_iff] at hz ⊢
  intro c hc
  exact hz c (subset_posHull P A hc)

def IsLitHalf {n : ℕ} (G : Formula n) (l : Lit n) : Prop :=
  ∀ w : W n, w l.1 = l.2 → sat G w = true

lemma isLitHalf_iff_clauses {n : ℕ} (G : Formula n) (l : Lit n) :
    IsLitHalf G l ↔
      ∀ c ∈ G, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨ c.1 = (l.1, !l.2) ∨ c.2 = (l.1, !l.2) := by
  constructor
  · intro hG c hc
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hnt, hc1, hc2⟩
    let w : W n := fun j =>
      if j = c.1.1 then c.1.2
      else if j = c.2.1 then c.2.2
      else l.2
    have hwl : w l.1 = l.2 := by
      simp only [w]
      by_cases h1 : l.1 = c.1.1
      · rw [if_pos h1]
        by_contra hne
        exact hc1 (Prod.ext h1.symm (bool_eq_not_of_ne hne))
      · rw [if_neg h1]
        by_cases h2 : l.1 = c.2.1
        · rw [if_pos h2]
          by_contra hne
          exact hc2 (Prod.ext h2.symm (bool_eq_not_of_ne hne))
        · rw [if_neg h2]
    have hwc1 : w c.1.1 = c.1.2 := by simp [w]
    have hwc2 : w c.2.1 = c.2.2 := by
      simp only [w]
      by_cases h12 : c.2.1 = c.1.1
      · rw [if_pos h12]
        exact hnt h12.symm
      · simp [h12]
    have hsat := sat_eq_true_iff.mp (hG w hwl)
    rcases hsat c hc with h | h
    · exact h hwc1
    · exact h hwc2
  · intro hall w hwl
    rw [sat_eq_true_iff]
    intro c hc
    rcases hall c hc with ⟨h1, h2⟩ | h1 | h2
    · rw [← h1]
      exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 h2
    · left
      rw [h1]
      simp [hwl]
    · right
      rw [h2]
      simp [hwl]

lemma isLitHalf_hull_iff {n m : ℕ} {P : Fin m → W n} (hP : IsStrength4Pool P)
    (A : Formula n) (l : Lit n) :
    IsLitHalf (posHull P (fun r => sat A (P r))) l ↔ IsLitHalf A l := by
  constructor
  · intro hH w hw
    exact sat_of_sat_posHull P A w (hH w hw)
  · intro hA
    rw [isLitHalf_iff_clauses]
    intro c hc
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hnt, hc1, hc2⟩
    let w : W n := fun j =>
      if j = c.1.1 then c.1.2
      else if j = c.2.1 then c.2.2
      else l.2
    have hwl : w l.1 = l.2 := by
      simp only [w]
      by_cases h1 : l.1 = c.1.1
      · rw [if_pos h1]
        by_contra hne
        exact hc1 (Prod.ext h1.symm (bool_eq_not_of_ne hne))
      · rw [if_neg h1]
        by_cases h2 : l.1 = c.2.1
        · rw [if_pos h2]
          by_contra hne
          exact hc2 (Prod.ext h2.symm (bool_eq_not_of_ne hne))
        · rw [if_neg h2]
    have hwc1 : w c.1.1 = c.1.2 := by simp [w]
    have hwc2 : w c.2.1 = c.2.2 := by
      simp only [w]
      by_cases h12 : c.2.1 = c.1.1
      · rw [if_pos h12]
        exact hnt h12.symm
      · simp [h12]
    let t : Fin 4 → Lit n := ![l, c.1, c.2, l]
    have hmt : Matches4 t w := by
      intro a
      fin_cases a <;> simp [t, hwl, hwc1, hwc2]
    have hcons : Consistent4 t := by
      intro a b hab
      rw [← hmt a, ← hmt b, hab]
    obtain ⟨r, hr⟩ := hP t hcons
    have hr0 : P r l.1 = l.2 := hr 0
    have hr1 : P r c.1.1 = c.1.2 := hr 1
    have hr2 : P r c.2.1 = c.2.2 := hr 2
    have hsatA : sat A (P r) = true := hA (P r) hr0
    simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc r hsatA with h | h
    · exact h hr1
    · exact h hr2

lemma card_filter_fin_zero (P : (Fin 0 → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = if P Fin.elim0 then 1 else 0 := by
  have heq : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
    ext f
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim f Fin.elim0
  rw [heq, Finset.filter_singleton]
  split_ifs <;> simp

lemma card_filter_fin_succ {k : ℕ} (P : (Fin (k + 1) → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun v : Fin k → Bool => P (Fin.cons false v))).card +
      (Finset.univ.filter (fun v : Fin k → Bool => P (Fin.cons true v))).card := by
  rw [show (Finset.univ.filter P).card = Fintype.card {v : Fin (k + 1) → Bool // P v} by
    rw [Fintype.card_subtype]]
  let e : {v : Fin (k + 1) → Bool // P v} ≃
      {v : Fin k → Bool // P (Fin.cons false v)} ⊕ {v : Fin k → Bool // P (Fin.cons true v)} :=
    { toFun := fun v =>
        if h : v.1 0 = false then
          Sum.inl ⟨Fin.tail v.1, by
            have : Fin.cons false (Fin.tail v.1) = v.1 := by
              funext i; refine Fin.cases ?_ ?_ i
              · simp [h]
              · intro j; simp [Fin.tail]
            rw [this]; exact v.2⟩
        else
          Sum.inr ⟨Fin.tail v.1, by
            have ht : v.1 0 = true := by cases h0 : v.1 0 <;> simp_all
            have : Fin.cons true (Fin.tail v.1) = v.1 := by
              funext i; refine Fin.cases ?_ ?_ i
              · simp [ht]
              · intro j; simp [Fin.tail]
            rw [this]; exact v.2⟩
      invFun := fun s =>
        match s with
        | Sum.inl v => ⟨Fin.cons false v.1, v.2⟩
        | Sum.inr v => ⟨Fin.cons true v.1, v.2⟩
      left_inv := fun v => by
        dsimp only
        split_ifs with h
        · apply Subtype.ext; funext i; refine Fin.cases ?_ ?_ i <;> simp [h, Fin.tail]
        · have ht : v.1 0 = true := by cases h0 : v.1 0 <;> simp_all
          apply Subtype.ext; funext i; refine Fin.cases ?_ ?_ i <;> simp [ht, Fin.tail]
      right_inv := fun s => by
        cases s with
        | inl v =>
            dsimp only
            rw [dif_pos (by simp)]
            apply congrArg Sum.inl
            apply Subtype.ext; funext j; simp [Fin.tail]
        | inr v =>
            dsimp only
            rw [dif_neg (by simp)]
            apply congrArg Sum.inr
            apply Subtype.ext; funext j; simp [Fin.tail] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]

lemma card_filter_prod {a b : ℕ}
    (P : (Fin a → Bool) → Prop) [DecidablePred P]
    (Q : (Fin b → Bool) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun v : Fin (a + b) → Bool =>
      P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))).card =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [show (Finset.univ.filter fun v : Fin (a + b) → Bool =>
        P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))).card =
      Fintype.card {v : Fin (a + b) → Bool //
        P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))} by
    rw [Fintype.card_subtype]]
  let e : {v : Fin (a + b) → Bool //
      P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))} ≃
      {u : Fin a → Bool // P u} × {w : Fin b → Bool // Q w} :=
    { toFun := fun v =>
        (⟨fun i => v.1 (Fin.castAdd b i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd a j), v.2.2⟩)
      invFun := fun p =>
        ⟨Fin.append p.1.1 p.2.1, by
          constructor
          · convert p.1.2 using 1; funext i; exact Fin.append_left _ _ i
          · convert p.2.2 using 1; funext j; exact Fin.append_right _ _ j⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro i; exact Fin.append_left _ _ i
        · intro j; exact Fin.append_right _ _ j
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext; funext i; exact Fin.append_left _ _ i
        · apply Subtype.ext; funext j; exact Fin.append_right _ _ j }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype, Fintype.card_subtype]

lemma card_K2_eq :
    (Finset.univ.filter fun v : Fin 2 → Bool => v 0 = false ∨ v 1 = false).card = 3 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P3_eq :
    (Finset.univ.filter fun v : Fin 3 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false)).card = 5 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_triangle_le :
    (Finset.univ.filter fun v : Fin 3 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 0 = false ∨ v 2 = false)).card = 4 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P4_le :
    (Finset.univ.filter fun v : Fin 4 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 2 = false ∨ v 3 = false)).card = 8 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P3K2_le :
    (Finset.univ.filter fun v : Fin 5 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 3 = false ∨ v 4 = false)).card = 15 := by
  have h := card_filter_prod (a := 3) (b := 2)
    (fun v => (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false))
    (fun v => v 0 = false ∨ v 1 = false)
  rw [card_P3_eq, card_K2_eq] at h
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h0 : (Fin.castAdd 2 (0 : Fin 3)) = (0 : Fin 5) := rfl
  have h1 : (Fin.castAdd 2 (1 : Fin 3)) = (1 : Fin 5) := rfl
  have h2 : (Fin.castAdd 2 (2 : Fin 3)) = (2 : Fin 5) := rfl
  have h3 : (Fin.natAdd 3 (0 : Fin 2)) = (3 : Fin 5) := rfl
  have h4 : (Fin.natAdd 3 (1 : Fin 2)) = (4 : Fin 5) := rfl
  simp only [h0, h1, h2, h3, h4, and_assoc]

lemma card_3K2_le :
    (Finset.univ.filter fun v : Fin 6 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false) ∧
      (v 4 = false ∨ v 5 = false)).card = 27 := by
  have h22 : (Finset.univ.filter fun v : Fin 4 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false)).card = 9 := by
    have h := card_filter_prod (a := 2) (b := 2)
      (fun v => v 0 = false ∨ v 1 = false)
      (fun v => v 0 = false ∨ v 1 = false)
    rw [card_K2_eq] at h
    convert h using 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have h := card_filter_prod (a := 2) (b := 4)
    (fun v => v 0 = false ∨ v 1 = false)
    (fun v => (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false))
  rw [card_K2_eq, h22] at h
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

lemma card_opp2_le :
    ∀ c1 c2 : Bool,
      (Finset.univ.filter fun v : Fin 2 → Bool =>
        (v 0 = false ∨ v 1 ≠ c1) ∧ (v 0 = true ∨ v 1 ≠ c2)).card ≤ 2 := by
  intro c1 c2
  cases c1 <;> cases c2 <;>
    simp only [card_filter_fin_succ, card_filter_fin_zero] <;>
    decide

lemma card_opp3_le :
    ∀ c1 c2 : Bool,
      (Finset.univ.filter fun v : Fin 3 → Bool =>
        (v 0 = false ∨ v 1 ≠ c1) ∧ (v 0 = true ∨ v 2 ≠ c2)).card ≤ 4 := by
  intro c1 c2
  cases c1 <;> cases c2 <;>
    simp only [card_filter_fin_succ, card_filter_fin_zero] <;>
    decide

lemma two_disjoint_clauses_of_no_litHalf {n : ℕ} (hn : 1 ≤ n) (A : Formula n)
    (hgt : 2 ^ n < 2 * (sol A).card) (hno : ∀ l : Lit n, ¬ IsLitHalf A l) :
    ∃ (u1 v1 u2 v2 : Fin n) (bu1 bv1 bu2 bv2 : Bool),
      ∀ w : W n, sat A w = true ↔
        (w u1 ≠ bu1 ∨ w v1 ≠ bv1) ∧ (w u2 ≠ bu2 ∨ w v2 ≠ bv2) := by
  have hno_unit : ∀ c ∈ A, c.1.1 = c.2.1 → c.1.2 ≠ c.2.2 := by
    intro c hc h12 heq
    have hsub : sol A ⊆ Finset.univ.filter (fun w : W n => ∀ j ∈ ({c.1.1} : Finset (Fin n)), w j = !c.1.2) := by
      intro w hw
      simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      intro j hj
      subst hj
      rcases (sat_eq_true_iff.mp hw) c hc with h | h
      · exact bool_eq_not_of_ne h
      · rw [← h12, ← heq] at h
        exact bool_eq_not_of_ne h
    have hcard : (sol A).card ≤ 2 ^ (n - 1) := by
      calc (sol A).card ≤ _ := Finset.card_le_card hsub
        _ = 2 ^ (n - ({c.1.1} : Finset (Fin n)).card) := card_subcube _ _
        _ = 2 ^ (n - 1) := by simp
    have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
      have : n = (n - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ, mul_comm]
    omega
  let act : Lit n → Lit n → Prop := fun l1 l2 =>
    l1.1 ≠ l2.1 ∧ ((l1, l2) ∈ A ∨ (l2, l1) ∈ A)
  have hact_symm : ∀ {l1 l2}, act l1 l2 → act l2 l1 := by
    intro l1 l2 ⟨hne, hmem⟩
    exact ⟨hne.symm, hmem.symm⟩
  have hact_sat : ∀ {l1 l2 w}, act l1 l2 → sat A w = true → w l1.1 ≠ l1.2 ∨ w l2.1 ≠ l2.2 := by
    intro l1 l2 w ⟨_, hmem⟩ hw
    have hw' := sat_eq_true_iff.mp hw
    rcases hmem with h | h
    · exact hw' (l1, l2) h
    · exact (hw' (l2, l1) h).symm
  have hpol_cons : ∀ {i b1 b2 l1 l2}, act (i, b1) l1 → act (i, b2) l2 → b1 = b2 := by
    intro i b1 b2 l1 l2 h1 h2
    by_contra hne_b
    have hb2 : b2 = !b1 := bool_eq_not_of_ne (Ne.symm hne_b)
    subst hb2
    by_cases hj : l1.1 = l2.1
    · let f : Fin 2 → Fin n := ![i, l1.1]
      have hf : Function.Injective f := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
        · exact absurd hab h1.1
        · exact absurd hab.symm h1.1
      let pol : Fin 2 → Bool := ![b1, true]
      have hf0 : f 0 = i := rfl
      have hf1 : f 1 = l1.1 := rfl
      have hp0 : pol 0 = b1 := rfl
      have hp1 : pol 1 = true := rfl
      let P : (Fin 2 → Bool) → Prop := fun v =>
        (v 0 = false ∨ v 1 ≠ l1.2) ∧ (v 0 = true ∨ v 1 ≠ l2.2)
      have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol k)) := by
        intro w hw
        have s1 := hact_sat h1 hw
        have s2 := hact_sat h2 hw
        rw [← hj] at s2
        constructor
        · rcases s1 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_false h
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
        · rcases s2 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_true (bool_eq_of_ne_not h)
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
      have hbound := card_sol_le_of_proj_pol A f hf pol P hP
      have hcnt := card_opp2_le l1.2 l2.2
      have : 4 * (sol A).card ≤ 2 * 2 ^ n := by
        calc 4 * (sol A).card = 2 ^ 2 * (sol A).card := by norm_num
          _ ≤ (Finset.univ.filter P).card * 2 ^ n := hbound
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ hcnt
      omega
    · let f : Fin 3 → Fin n := ![i, l1.1, l2.1]
      have hf : Function.Injective f := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
        · exact absurd hab h1.1
        · exact absurd hab h2.1
        · exact absurd hab.symm h1.1
        · exact absurd hab hj
        · exact absurd hab.symm h2.1
        · exact absurd hab.symm hj
      let pol : Fin 3 → Bool := ![b1, true, true]
      have hf0 : f 0 = i := rfl
      have hf1 : f 1 = l1.1 := rfl
      have hf2 : f 2 = l2.1 := rfl
      have hp0 : pol 0 = b1 := rfl
      have hp1 : pol 1 = true := rfl
      have hp2 : pol 2 = true := rfl
      let P : (Fin 3 → Bool) → Prop := fun v =>
        (v 0 = false ∨ v 1 ≠ l1.2) ∧ (v 0 = true ∨ v 2 ≠ l2.2)
      have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol k)) := by
        intro w hw
        have s1 := hact_sat h1 hw
        have s2 := hact_sat h2 hw
        constructor
        · rcases s1 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_false h
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
        · rcases s2 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_true (bool_eq_of_ne_not h)
          · right; dsimp only; rw [hf2, hp2, decide_eq_true_bool]; exact h
      have hbound := card_sol_le_of_proj_pol A f hf pol P hP
      have hcnt := card_opp3_le l1.2 l2.2
      have : 8 * (sol A).card ≤ 4 * 2 ^ n := by
        calc 8 * (sol A).card = 2 ^ 3 * (sol A).card := by norm_num
          _ ≤ (Finset.univ.filter P).card * 2 ^ n := hbound
          _ ≤ 4 * 2 ^ n := Nat.mul_le_mul_right _ hcnt
      omega
  let pol : Fin n → Bool := fun i =>
    if h : ∃ b : Bool, ∃ l : Lit n, act (i, b) l then Classical.choose h else false
  have hpol_eq : ∀ {l1 l2}, act l1 l2 → l1.2 = pol l1.1 := by
    intro l1 l2 h
    have hex : ∃ b : Bool, ∃ l : Lit n, act (l1.1, b) l := ⟨l1.2, l2, h⟩
    simp only [pol, dif_pos hex]
    obtain ⟨l', hl'⟩ := Classical.choose_spec hex
    exact hpol_cons h hl'
  let E : Fin n → Fin n → Prop := fun i j => act (i, pol i) (j, pol j)
  have hE_ne : ∀ {i j}, E i j → i ≠ j := fun h => h.1
  have hE_symm : ∀ {i j}, E i j → E j i := fun h => hact_symm h
  have hE_sat : ∀ w : W n, sat A w = true ↔ ∀ i j, E i j → w i ≠ pol i ∨ w j ≠ pol j := by
    intro w
    constructor
    · intro hw i j hij
      exact hact_sat hij hw
    · intro hall
      rw [sat_eq_true_iff]
      intro c hc
      by_cases h12 : c.1.1 = c.2.1
      · have hne := hno_unit c hc h12
        rw [← h12]
        exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 hne
      · have ha : act c.1 c.2 := ⟨h12, Or.inl hc⟩
        have hp1 : c.1.2 = pol c.1.1 := hpol_eq ha
        have hp2 : c.2.2 = pol c.2.1 := hpol_eq (hact_symm ha)
        have hE : E c.1.1 c.2.1 := by
          dsimp only [E]
          rwa [← hp1, ← hp2]
        have hres := hall c.1.1 c.2.1 hE
        rwa [← hp1, ← hp2] at hres
  have hno_cover : ∀ i : Fin n, ∃ u v : Fin n, E u v ∧ u ≠ i ∧ v ≠ i := by
    intro i
    by_contra hall
    push Not at hall
    apply hno (i, !pol i)
    intro w hw
    rw [hE_sat]
    intro u v huv
    by_cases hu : u = i
    · left; subst hu; simp [hw]
    · right
      have hv : v = i := by
        by_contra hv'
        exact hv' (hall u v huv hu)
      subst hv; simp [hw]
  have hno_tri : ∀ a b c : Fin n, E a b → E b c → E a c → False := by
    intro a b c hab hbc hac
    let f : Fin 3 → Fin n := ![a, b, c]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢
      · exact absurd hxy (hE_ne hab)
      · exact absurd hxy (hE_ne hac)
      · exact absurd hxy.symm (hE_ne hab)
      · exact absurd hxy (hE_ne hbc)
      · exact absurd hxy.symm (hE_ne hac)
      · exact absurd hxy.symm (hE_ne hbc)
    let P : (Fin 3 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 0 = false ∨ v 2 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw a c hac with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_triangle_le] at hb
    have : 8 * (sol A).card ≤ 4 * 2 ^ n := by simpa using hb
    omega
  have hno_P4 : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      E a b → E b c → E c d → False := by
    intro a b c d hab' hac' had' hbc' hbd' hcd' hab hbc hcd
    let f : Fin 4 → Fin n := ![a, b, c, d]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy hab' | exact absurd hxy hac' | exact absurd hxy had'
              | exact absurd hxy hbc' | exact absurd hxy hbd' | exact absurd hxy hcd'
              | exact absurd hxy.symm hab' | exact absurd hxy.symm hac' | exact absurd hxy.symm had'
              | exact absurd hxy.symm hbc' | exact absurd hxy.symm hbd' | exact absurd hxy.symm hcd'
    let P : (Fin 4 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 2 = false ∨ v 3 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw c d hcd with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_P4_le] at hb
    have : 16 * (sol A).card ≤ 8 * 2 ^ n := by simpa using hb
    omega
  have hno_P3K2 : ∀ a b c d e : Fin n,
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      E a b → E b c → E d e → False := by
    intro a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hab hbc hde
    let f : Fin 5 → Fin n := ![a, b, c, d, e]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy h1 | exact absurd hxy h2 | exact absurd hxy h3
              | exact absurd hxy h4 | exact absurd hxy h5 | exact absurd hxy h6
              | exact absurd hxy h7 | exact absurd hxy h8 | exact absurd hxy h9
              | exact absurd hxy h10 | exact absurd hxy.symm h1 | exact absurd hxy.symm h2
              | exact absurd hxy.symm h3 | exact absurd hxy.symm h4 | exact absurd hxy.symm h5
              | exact absurd hxy.symm h6 | exact absurd hxy.symm h7 | exact absurd hxy.symm h8
              | exact absurd hxy.symm h9 | exact absurd hxy.symm h10
    let P : (Fin 5 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 3 = false ∨ v 4 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw d e hde with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_P3K2_le] at hb
    have : 32 * (sol A).card ≤ 15 * 2 ^ n := by simpa using hb
    omega
  have hno_3K2 : ∀ a b c d e g : Fin n,
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ g →
      b ≠ c → b ≠ d → b ≠ e → b ≠ g →
      c ≠ d → c ≠ e → c ≠ g →
      d ≠ e → d ≠ g → e ≠ g →
      E a b → E c d → E e g → False := by
    intro a b c d e g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hab hcd heg
    let f : Fin 6 → Fin n := ![a, b, c, d, e, g]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy h1 | exact absurd hxy h2 | exact absurd hxy h3
              | exact absurd hxy h4 | exact absurd hxy h5 | exact absurd hxy h6
              | exact absurd hxy h7 | exact absurd hxy h8 | exact absurd hxy h9
              | exact absurd hxy h10 | exact absurd hxy h11 | exact absurd hxy h12
              | exact absurd hxy h13 | exact absurd hxy h14 | exact absurd hxy h15
              | exact absurd hxy.symm h1 | exact absurd hxy.symm h2 | exact absurd hxy.symm h3
              | exact absurd hxy.symm h4 | exact absurd hxy.symm h5 | exact absurd hxy.symm h6
              | exact absurd hxy.symm h7 | exact absurd hxy.symm h8 | exact absurd hxy.symm h9
              | exact absurd hxy.symm h10 | exact absurd hxy.symm h11 | exact absurd hxy.symm h12
              | exact absurd hxy.symm h13 | exact absurd hxy.symm h14 | exact absurd hxy.symm h15
    let P : (Fin 6 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false) ∧ (v 4 = false ∨ v 5 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw c d hcd with h | h <;> simp [f, h]
      · rcases hw e g heg with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_3K2_le] at hb
    have : 64 * (sol A).card ≤ 27 * 2 ^ n := by simpa using hb
    omega
  have h2disj : ∃ u1 v1 u2 v2 : Fin n,
      E u1 v1 ∧ E u2 v2 ∧ u1 ≠ v1 ∧ u2 ≠ v2 ∧ u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2 := by
    obtain ⟨u1, v1, he1, _, _⟩ := hno_cover ⟨0, hn⟩
    obtain ⟨a, b, hab, hau1, hbu1⟩ := hno_cover u1
    by_cases hav1 : a = v1
    · subst hav1
      obtain ⟨x, y, hxy, hxv1, hyv1⟩ := hno_cover a
      by_cases hxu1 : x = u1
      · subst hxu1
        by_cases hyb : y = b
        · subst hyb; exact absurd (hno_tri x a y he1 hab hxy) id
        · exact ⟨a, b, x, y, hab, hxy, hE_ne hab, hE_ne hxy, hxv1.symm, hyv1.symm, hbu1, Ne.symm hyb⟩
      · by_cases hyu1 : y = u1
        · subst hyu1
          by_cases hxb : x = b
          · subst hxb; exact absurd (hno_tri y a x he1 hab (hE_symm hxy)) id
          · exact ⟨a, b, x, y, hab, hxy, hE_ne hab, hE_ne hxy, hxv1.symm, hyv1.symm, Ne.symm hxb, hbu1⟩
        · exact ⟨u1, a, x, y, he1, hxy, hE_ne he1, hE_ne hxy, Ne.symm hxu1, Ne.symm hyu1, Ne.symm hxv1, Ne.symm hyv1⟩
    · by_cases hbv1 : b = v1
      · subst hbv1
        have hba : E b a := hE_symm hab
        obtain ⟨x, y, hxy, hxv1, hyv1⟩ := hno_cover b
        by_cases hxu1 : x = u1
        · subst hxu1
          by_cases hya : y = a
          · subst hya; exact absurd (hno_tri x b y he1 hba hxy) id
          · exact ⟨b, a, x, y, hba, hxy, hE_ne hba, hE_ne hxy, hxv1.symm, hyv1.symm, hau1, Ne.symm hya⟩
        · by_cases hyu1 : y = u1
          · subst hyu1
            by_cases hxa : x = a
            · subst hxa; exact absurd (hno_tri y b x he1 hba (hE_symm hxy)) id
            · exact ⟨b, a, x, y, hba, hxy, hE_ne hba, hE_ne hxy, hxv1.symm, hyv1.symm, Ne.symm hxa, hau1⟩
          · exact ⟨u1, b, x, y, he1, hxy, hE_ne he1, hE_ne hxy, Ne.symm hxu1, Ne.symm hyu1, Ne.symm hxv1, Ne.symm hyv1⟩
      · exact ⟨u1, v1, a, b, he1, hab, hE_ne he1, hE_ne hab, Ne.symm hau1, Ne.symm hbu1, Ne.symm hav1, Ne.symm hbv1⟩
  obtain ⟨u1, v1, u2, v2, he1, he2, huv1, huv2, hu12, hu1v2, hv1u2, hv12⟩ := h2disj
  have honly : ∀ x y : Fin n, E x y →
      (x = u1 ∧ y = v1) ∨ (x = v1 ∧ y = u1) ∨ (x = u2 ∧ y = v2) ∨ (x = v2 ∧ y = u2) := by
    intro x y hxy
    have hxy_ne : x ≠ y := hE_ne hxy
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hn1, hn2, hn3, hn4⟩
    by_cases hxu1 : x = u1
    · subst hxu1
      have hyv1 : y ≠ v1 := hn1 rfl
      by_cases hyu2 : y = u2
      · subst hyu2; exact hno_P4 v1 x y v2 huv1.symm hv1u2 hv12 hu12 hu1v2 huv2 (hE_symm he1) hxy he2
      · by_cases hyv2 : y = v2
        · subst hyv2; exact hno_P4 v1 x y u2 huv1.symm hv12 hv1u2 hu1v2 hu12 huv2.symm (hE_symm he1) hxy (hE_symm he2)
        · exact hno_P3K2 v1 x y u2 v2 huv1.symm hyv1.symm hv1u2 hv12 hxy_ne hu12 hu1v2 hyu2 hyv2 huv2 (hE_symm he1) hxy he2
    · by_cases hxv1 : x = v1
      · subst hxv1
        have hyu1 : y ≠ u1 := hn2 rfl
        by_cases hyu2 : y = u2
        · subst hyu2; exact hno_P4 u1 x y v2 huv1 hu12 hu1v2 hv1u2 hv12 huv2 he1 hxy he2
        · by_cases hyv2 : y = v2
          · subst hyv2; exact hno_P4 u1 x y u2 huv1 hu1v2 hu12 hv12 hv1u2 huv2.symm he1 hxy (hE_symm he2)
          · exact hno_P3K2 u1 x y u2 v2 huv1 hyu1.symm hu12 hu1v2 hxy_ne hv1u2 hv12 hyu2 hyv2 huv2 he1 hxy he2
      · by_cases hxu2 : x = u2
        · subst hxu2
          have hyv2 : y ≠ v2 := hn3 rfl
          by_cases hyu1 : y = u1
          · subst hyu1; exact hno_P4 v2 x y v1 huv2.symm hu1v2.symm hv12.symm hu12.symm hv1u2.symm huv1 (hE_symm he2) hxy he1
          · by_cases hyv1 : y = v1
            · subst hyv1; exact hno_P4 v2 x y u1 huv2.symm hv12.symm hu1v2.symm hv1u2.symm hu12.symm huv1.symm (hE_symm he2) hxy (hE_symm he1)
            · exact hno_P3K2 v2 x y u1 v1 huv2.symm hyv2.symm hu1v2.symm hv12.symm hxy_ne hu12.symm hv1u2.symm hyu1 hyv1 huv1 (hE_symm he2) hxy he1
        · by_cases hxv2 : x = v2
          · subst hxv2
            have hyu2 : y ≠ u2 := hn4 rfl
            by_cases hyu1 : y = u1
            · subst hyu1; exact hno_P4 u2 x y v1 huv2 hu12.symm hv1u2.symm hu1v2.symm hv12.symm huv1 he2 hxy he1
            · by_cases hyv1 : y = v1
              · subst hyv1; exact hno_P4 u2 x y u1 huv2 hv1u2.symm hu12.symm hv12.symm hu1v2.symm huv1.symm he2 hxy (hE_symm he1)
              · exact hno_P3K2 u2 x y u1 v1 huv2 hyu2.symm hu12.symm hv1u2.symm hxy_ne hu1v2.symm hv12.symm hyu1 hyv1 huv1 he2 hxy he1
          · by_cases hyu1 : y = u1
            · subst hyu1; exact hno_P3K2 v1 y x u2 v2 huv1.symm (Ne.symm hxv1) hv1u2 hv12 hxy_ne.symm hu12 hu1v2 hxu2 hxv2 huv2 (hE_symm he1) (hE_symm hxy) he2
            · by_cases hyv1 : y = v1
              · subst hyv1; exact hno_P3K2 u1 y x u2 v2 huv1 (Ne.symm hxu1) hu12 hu1v2 hxy_ne.symm hv1u2 hv12 hxu2 hxv2 huv2 he1 (hE_symm hxy) he2
              · by_cases hyu2 : y = u2
                · subst hyu2; exact hno_P3K2 v2 y x u1 v1 huv2.symm (Ne.symm hxv2) hu1v2.symm hv12.symm hxy_ne.symm hu12.symm hv1u2.symm hxu1 hxv1 huv1 (hE_symm he2) (hE_symm hxy) he1
                · by_cases hyv2 : y = v2
                  · subst hyv2; exact hno_P3K2 u2 y x u1 v1 huv2 (Ne.symm hxu2) hu12.symm hv1u2.symm hxy_ne.symm hu1v2.symm hv12.symm hxu1 hxv1 huv1 he2 (hE_symm hxy) he1
                  · exact hno_3K2 u1 v1 u2 v2 x y huv1 hu12 hu1v2 (Ne.symm hxu1) (Ne.symm hyu1) hv1u2 hv12 (Ne.symm hxv1) (Ne.symm hyv1) huv2 (Ne.symm hxu2) (Ne.symm hyu2) (Ne.symm hxv2) (Ne.symm hyv2) hxy_ne he1 he2 hxy
  refine ⟨u1, v1, u2, v2, pol u1, pol v1, pol u2, pol v2, fun w => ?_⟩
  rw [hE_sat]
  constructor
  · intro h
    exact ⟨h u1 v1 he1, h u2 v2 he2⟩
  · rintro ⟨h1, h2⟩ x y hxy
    rcases honly x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · exact h1.symm
    · exact h2
    · exact h2.symm

lemma hull_exact_of_no_litHalf {n s m : ℕ} (hs : 3 ≤ s)
    {P : Fin m → W n} (hP : IsStrength4Pool P) (A : Formula n)
    (hhigh : high s A)
    (hno : ∀ l : Lit n, ¬ IsLitHalf (posHull P (fun r => sat A (P r))) l)
    (hn : 1 ≤ n) :
    ∀ z : W n, sat (posHull P (fun r => sat A (P r))) z = sat A z := by
  have hnoA : ∀ l : Lit n, ¬ IsLitHalf A l := by
    intro l hl
    exact hno l ((isLitHalf_hull_iff hP A l).mpr hl)
  have hgt : 2 ^ n < 2 * (sol A).card := card_sol_gt_half_of_high hs hhigh
  obtain ⟨u1, v1, u2, v2, bu1, bv1, bu2, bv2, hchar⟩ :=
    two_disjoint_clauses_of_no_litHalf hn A hgt hnoA
  intro z
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact sat_of_sat_posHull P A z
  · intro hzA
    rw [sat_eq_true_iff]
    intro c hc
    by_contra hviol
    push Not at hviol
    rcases hviol with ⟨hc1, hc2⟩
    rcases (hchar z).mp hzA with ⟨h1, h2⟩
    have hm1 : ∃ m1 : Lit n, z m1.1 = m1.2 ∧
        (∀ w : W n, w m1.1 = m1.2 → w u1 ≠ bu1 ∨ w v1 ≠ bv1) := by
      rcases h1 with h | h
      · exact ⟨(u1, !bu1), bool_eq_not_of_ne h, fun w hw => Or.inl (by simp [hw])⟩
      · exact ⟨(v1, !bv1), bool_eq_not_of_ne h, fun w hw => Or.inr (by simp [hw])⟩
    have hm2 : ∃ m2 : Lit n, z m2.1 = m2.2 ∧
        (∀ w : W n, w m2.1 = m2.2 → w u2 ≠ bu2 ∨ w v2 ≠ bv2) := by
      rcases h2 with h | h
      · exact ⟨(u2, !bu2), bool_eq_not_of_ne h, fun w hw => Or.inl (by simp [hw])⟩
      · exact ⟨(v2, !bv2), bool_eq_not_of_ne h, fun w hw => Or.inr (by simp [hw])⟩
    obtain ⟨m1, hzm1, hsat1⟩ := hm1
    obtain ⟨m2, hzm2, hsat2⟩ := hm2
    let t : Fin 4 → Lit n := ![c.1, c.2, m1, m2]
    have hmt : Matches4 t z := by
      intro a
      fin_cases a <;> simp [t, hc1, hc2, hzm1, hzm2]
    have hcons : Consistent4 t := by
      intro a b hab
      rw [← hmt a, ← hmt b, hab]
    obtain ⟨r, hr⟩ := hP t hcons
    have hrA : sat A (P r) = true := (hchar (P r)).mpr ⟨hsat1 (P r) (hr 2), hsat2 (P r) (hr 3)⟩
    simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc r hrA with h | h
    · exact h (hr 0)
    · exact h (hr 1)

def flipList {n : ℕ} (w : W n) (S : List (Fin n)) : W n :=
  fun j => if j ∈ S then !w j else w j

def forcedSet {n : ℕ} (A : Formula n) (i : Fin n) (w0 : W n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ sat A (flipList w0 [j]) = false)

lemma mem_forcedSet_iff {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) (j : Fin n) :
    j ∈ forcedSet A i w0 ↔
      j ≠ i ∧ ∃ c ∈ A, c = ((i, !a), (j, !w0 j)) ∨ c = ((j, !w0 j), (i, !a)) := by
  simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcl := (isLitHalf_iff_clauses A (i, a)).mp hlit
  have hw0sat' := sat_eq_true_iff.mp hw0sat
  constructor
  · rintro ⟨hji, hfl⟩
    refine ⟨hji, ?_⟩
    obtain ⟨c, hc, h1, h2⟩ := sat_eq_false_iff.mp hfl
    rcases hcl c hc with ⟨ht1, ht2⟩ | hc1 | hc2
    · exfalso
      rw [← ht1] at h2
      rw [h1] at h2
      exact ht2 h2
    · refine ⟨c, hc, Or.inl ?_⟩
      have hw0c := hw0sat' c hc
      have hne2 : w0 c.2.1 ≠ c.2.2 := by
        rcases hw0c with h | h
        · rw [hc1] at h; exact absurd hw0i h
        · exact h
      have h2j : c.2.1 = j := by
        by_contra hne
        simp only [flipList, List.mem_singleton, if_neg hne] at h2
        exact hne2 h2
      have h2b : c.2.2 = !w0 j := by
        rw [h2j] at hne2
        exact bool_eq_not_of_ne hne2.symm
      exact Prod.ext hc1 (Prod.ext h2j h2b)
    · refine ⟨c, hc, Or.inr ?_⟩
      have hw0c := hw0sat' c hc
      have hne1 : w0 c.1.1 ≠ c.1.2 := by
        rcases hw0c with h | h
        · exact h
        · rw [hc2] at h; exact absurd hw0i h
      have h1j : c.1.1 = j := by
        by_contra hne
        simp only [flipList, List.mem_singleton, if_neg hne] at h1
        exact hne1 h1
      have h1b : c.1.2 = !w0 j := by
        rw [h1j] at hne1
        exact bool_eq_not_of_ne hne1.symm
      exact Prod.ext (Prod.ext h1j h1b) hc2
  · rintro ⟨hji, c, hc, rfl | rfl⟩
    · refine ⟨hji, sat_eq_false_iff.mpr ⟨_, hc, ?_, ?_⟩⟩
      · simp [flipList, Ne.symm hji, hw0i]
      · simp [flipList]
    · refine ⟨hji, sat_eq_false_iff.mpr ⟨_, hc, ?_, ?_⟩⟩
      · simp [flipList]
      · simp [flipList, Ne.symm hji, hw0i]

lemma sat_opposite_iff {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true)
    (w : W n) (hwi : w i = !a) :
    sat A w = true ↔ ∀ j ∈ forcedSet A i w0, w j = w0 j := by
  have hcl := (isLitHalf_iff_clauses A (i, a)).mp hlit
  have hw0sat' := sat_eq_true_iff.mp hw0sat
  constructor
  · intro hwsat j hj
    obtain ⟨_, c, hc, rfl | rfl⟩ := (mem_forcedSet_iff hlit hw0i hw0sat j).mp hj
    · rcases (sat_eq_true_iff.mp hwsat) _ hc with h | h
      · exact absurd hwi h
      · exact bool_eq_of_ne_not h
    · rcases (sat_eq_true_iff.mp hwsat) _ hc with h | h
      · exact bool_eq_of_ne_not h
      · exact absurd hwi h
  · intro hall
    rw [sat_eq_true_iff]
    intro c hc
    rcases hcl c hc with ⟨ht1, ht2⟩ | hc1 | hc2
    · rw [← ht1]
      exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 ht2
    · have hw0c := hw0sat' c hc
      have hne2 : w0 c.2.1 ≠ c.2.2 := by
        rcases hw0c with h | h
        · rw [hc1] at h; exact absurd hw0i h
        · exact h
      by_cases h2i : c.2.1 = i
      · right
        rw [h2i] at hne2 ⊢
        rw [hwi, ← hw0i]
        exact hne2
      · have h2b : c.2.2 = !w0 c.2.1 := bool_eq_not_of_ne hne2.symm
        have hmem : c.2.1 ∈ forcedSet A i w0 := by
          rw [mem_forcedSet_iff hlit hw0i hw0sat]
          exact ⟨h2i, c, hc, Or.inl (Prod.ext hc1 (Prod.ext rfl h2b))⟩
        right
        rw [hall c.2.1 hmem]
        exact hne2
    · have hw0c := hw0sat' c hc
      have hne1 : w0 c.1.1 ≠ c.1.2 := by
        rcases hw0c with h | h
        · exact h
        · rw [hc2] at h; exact absurd hw0i h
      by_cases h1i : c.1.1 = i
      · left
        rw [h1i] at hne1 ⊢
        rw [hwi, ← hw0i]
        exact hne1
      · have h1b : c.1.2 = !w0 c.1.1 := bool_eq_not_of_ne hne1.symm
        have hmem : c.1.1 ∈ forcedSet A i w0 := by
          rw [mem_forcedSet_iff hlit hw0i hw0sat]
          exact ⟨h1i, c, hc, Or.inr (Prod.ext (Prod.ext rfl h1b) hc2)⟩
        left
        rw [hall c.1.1 hmem]
        exact hne1

lemma card_sol_of_litHalf_witness {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) :
    (sol A).card = 2 ^ (n - 1) + 2 ^ (n - 1 - (forcedSet A i w0).card) := by
  let S1 := (sol A).filter (fun w => w i = a)
  let S2 := (sol A).filter (fun w => w i ≠ a)
  have hpart : (sol A).card = S1.card + S2.card := by
    exact (card_filter_add_card_filter_not (s := sol A) (p := fun w => w i = a)).symm
  have hS1 : S1 = Finset.univ.filter (fun w : W n => ∀ j ∈ ({i} : Finset (Fin n)), w j = a) := by
    ext w
    simp only [S1, sol, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hw⟩ j rfl; exact hw
    · intro h; exact ⟨hlit w (h i rfl), h i rfl⟩
  have hS1_card : S1.card = 2 ^ (n - 1) := by
    rw [hS1, card_subcube ({i}) (fun _ => a)]
    simp
  have hiK : i ∉ forcedSet A i w0 := by
    simp [forcedSet]
  have hS2 : S2 = Finset.univ.filter
      (fun w : W n => ∀ j ∈ insert i (forcedSet A i w0), w j = w0 j) := by
    ext w
    simp only [S2, sol, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨hwsat, hne⟩ j (rfl | hjK)
      · rw [hw0i]; exact bool_eq_not_of_ne hne
      · have hwi : w i = !a := bool_eq_not_of_ne hne
        exact (sat_opposite_iff hlit hw0i hw0sat w hwi).mp hwsat j hjK
    · intro hall
      have hwi : w i = !a := by rw [hall i (Or.inl rfl), hw0i]
      have hne : w i ≠ a := by rw [hwi]; cases a <;> decide
      exact ⟨(sat_opposite_iff hlit hw0i hw0sat w hwi).mpr (fun j hj => hall j (Or.inr hj)), hne⟩
  have hS2_card : S2.card = 2 ^ (n - 1 - (forcedSet A i w0).card) := by
    rw [hS2, card_subcube (insert i (forcedSet A i w0)) w0, Finset.card_insert_of_notMem hiK]
    congr 1
    omega
  rw [hpart, hS1_card, hS2_card]

lemma high_iff_card_forcedSet {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) :
    high s A ↔ (forcedSet A i w0).card ≤ s - 1 := by
  unfold high
  rw [card_sol_of_litHalf_witness hlit hw0i hw0sat]
  have hK_le : (forcedSet A i w0).card ≤ n - 1 := by
    have hsub : forcedSet A i w0 ⊆ Finset.univ.erase i := by
      intro j hj
      simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_erase.mpr ⟨hj.1, Finset.mem_univ j⟩
    have := Finset.card_le_card hsub
    simpa [Finset.card_erase_of_mem] using this
  have h1 : 2 ^ s * 2 ^ (n - 1) = 2 ^ n * 2 ^ (s - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : 2 ^ s * 2 ^ (n - 1 - (forcedSet A i w0).card) =
      2 ^ (s + (n - 1 - (forcedSet A i w0).card)) := by
    rw [← pow_add]
  rw [mul_add, mul_one, mul_add, h1, h2]
  constructor
  · intro h
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - (forcedSet A i w0).card)) := by omega
    have hexp : n ≤ s + (n - 1 - (forcedSet A i w0).card) :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · intro h
    have hexp : n ≤ s + (n - 1 - (forcedSet A i w0).card) := by omega
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - (forcedSet A i w0).card)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega

def mkBranchFormulaS {n : ℕ} (i : Fin n) (a : Bool) (w0 : W n) (S : Finset (Fin n)) :
    Formula n :=
  S.image (fun j => ((i, !a), (j, !w0 j)))

lemma sat_mkBranchFormulaS {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true)
    (S : Finset (Fin n)) (hS : S = forcedSet A i w0) :
    ∀ z : W n, sat (mkBranchFormulaS i a w0 S) z = sat A z := by
  intro z
  apply Bool.eq_iff_iff.mpr
  by_cases hzi : z i = a
  · constructor
    · intro _; exact hlit z hzi
    · intro _
      rw [sat_eq_true_iff]
      intro c hc
      simp only [mkBranchFormulaS, Finset.mem_image] at hc
      rcases hc with ⟨j, _, rfl⟩
      left
      simp [hzi]
  · have hzi' : z i = !a := bool_eq_not_of_ne hzi
    rw [sat_opposite_iff hlit hw0i hw0sat z hzi', sat_eq_true_iff]
    constructor
    · intro h j hjK
      have hmem : ((i, !a), (j, !w0 j)) ∈ mkBranchFormulaS i a w0 S := by
        simp only [mkBranchFormulaS, Finset.mem_image]
        exact ⟨j, hS ▸ hjK, rfl⟩
      rcases h _ hmem with h1 | h1
      · exact absurd hzi' h1
      · exact bool_eq_of_ne_not h1
    · intro h c hc
      simp only [mkBranchFormulaS, Finset.mem_image] at hc
      rcases hc with ⟨j, hjS, rfl⟩
      right
      have hzj := h j (hS ▸ hjS)
      rw [hzj]
      cases w0 j <;> simp

lemma exists_opposite_witness_of_high {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {A : Formula n} (hhigh : high s A) (l : Lit n) :
    ∃ w0 : W n, w0 l.1 = !l.2 ∧ sat A w0 = true := by
  by_contra hnone
  push Not at hnone
  have hsub : sol A ⊆ Finset.univ.filter (fun w : W n => ∀ j ∈ ({l.1} : Finset (Fin n)), w j = l.2) := by
    intro w hw
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro j hj
    subst hj
    by_contra hne
    exact (hnone w (bool_eq_not_of_ne hne)) hw
  have hcard : (sol A).card ≤ 2 ^ (n - 1) := by
    calc (sol A).card ≤ _ := Finset.card_le_card hsub
      _ = 2 ^ (n - ({l.1} : Finset (Fin n)).card) := card_subcube _ _
      _ = 2 ^ (n - 1) := by simp
  have hgt := card_sol_gt_half_of_high hs hhigh
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have : n = (n - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ, mul_comm]
  omega

def dotBool {d : ℕ} (v u : Vec d) : Bool :=
  (∑ l : Fin d, (v l && u l).toNat) % 2 == 1

def xorV {d : ℕ} (x y : Vec d) : Vec d :=
  fun l => xor (x l) (y l)

def linComb {r d : ℕ} (vecs : Fin r → Vec d) (c : Fin r → Bool) : Vec d :=
  fun l => (∑ a : Fin r, (c a && vecs a l).toNat) % 2 == 1

def evalVecs {r d : ℕ} (vecs : Fin r → Vec d) (u : Vec d) : Fin r → Bool :=
  fun a => dotBool (vecs a) u

def spanSet {r d : ℕ} (vecs : Fin r → Vec d) : Finset (Vec d) :=
  Finset.univ.image (linComb vecs)

def Indep : ∀ {r d : ℕ}, (Fin r → Vec d) → Prop
  | 0, _, _ => True
  | r + 1, _, vecs =>
      Indep (Fin.init vecs) ∧ vecs (Fin.last r) ∉ spanSet (Fin.init vecs)

def boolZ (b : Bool) : ZMod 2 := b.toNat

lemma boolZ_inj : Function.Injective boolZ := by
  intro a b hab
  cases a <;> cases b <;> revert hab <;> decide

lemma boolZ_xor (x y : Bool) : boolZ (xor x y) = boolZ x + boolZ y := by
  cases x <;> cases y <;> decide

lemma boolZ_and (x y : Bool) : boolZ (x && y) = boolZ x * boolZ y := by
  cases x <;> cases y <;> decide

lemma boolZ_mod2 (k : ℕ) : boolZ (k % 2 == 1) = (k : ZMod 2) := by
  have hdiv : (k : ℕ) = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
  have hcast : (k : ZMod 2) = ((2 * (k / 2) + k % 2 : ℕ) : ZMod 2) := congrArg Nat.cast hdiv
  have htwo : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [Nat.cast_add, Nat.cast_mul, htwo, zero_mul, zero_add] at hcast
  rcases Nat.mod_two_eq_zero_or_one k with hm | hm
  · simp [hm, hcast, boolZ]
  · simp [hm, hcast, boolZ]

lemma boolZ_dotBool {d : ℕ} (v u : Vec d) :
    boolZ (dotBool v u) = ∑ l : Fin d, boolZ (v l) * boolZ (u l) := by
  unfold dotBool
  rw [boolZ_mod2, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact boolZ_and (v l) (u l)

lemma boolZ_linComb {r d : ℕ} (vecs : Fin r → Vec d) (c : Fin r → Bool) (l : Fin d) :
    boolZ (linComb vecs c l) = ∑ a : Fin r, boolZ (c a) * boolZ (vecs a l) := by
  unfold linComb
  rw [boolZ_mod2, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact boolZ_and (c a) (vecs a l)

lemma dotBool_comm {d : ℕ} (v u : Vec d) : dotBool v u = dotBool u v := by
  apply boolZ_inj
  rw [boolZ_dotBool, boolZ_dotBool]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma dotBool_xorV_right {d : ℕ} (v u1 u2 : Vec d) :
    dotBool v (xorV u1 u2) = xor (dotBool v u1) (dotBool v u2) := by
  apply boolZ_inj
  rw [boolZ_xor, boolZ_dotBool, boolZ_dotBool, boolZ_dotBool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [xorV, boolZ_xor, mul_add]

lemma dotBool_linComb {r d : ℕ} (vecs : Fin r → Vec d) (c : Fin r → Bool) (u : Vec d) :
    dotBool (linComb vecs c) u = dotBool c (evalVecs vecs u) := by
  apply boolZ_inj
  rw [boolZ_dotBool, boolZ_dotBool]
  have h1 : ∑ l : Fin d, boolZ (linComb vecs c l) * boolZ (u l) =
      ∑ l : Fin d, ∑ a : Fin r, boolZ (c a) * (boolZ (vecs a l) * boolZ (u l)) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [boolZ_linComb, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h2 : ∑ a : Fin r, boolZ (c a) * boolZ (evalVecs vecs u a) =
      ∑ a : Fin r, ∑ l : Fin d, boolZ (c a) * (boolZ (vecs a l) * boolZ (u l)) := by
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [evalVecs]
    rw [boolZ_dotBool, Finset.mul_sum]
  rw [h1, h2, Finset.sum_comm]

lemma dotBool_basis_right {d : ℕ} (v : Vec d) (l : Fin d) :
    dotBool v (fun k => decide (k = l)) = v l := by
  apply boolZ_inj
  rw [boolZ_dotBool]
  have hsum : (∑ k : Fin d, boolZ (v k) * boolZ (decide (k = l))) =
      ∑ k : Fin d, if k = l then boolZ (v l) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = l
    · subst hk; simp [boolZ]
    · simp [hk, boolZ]
  rw [hsum, Finset.sum_ite_eq']
  simp

lemma dotBool_basis_left {r : ℕ} (y : Fin r → Bool) (b : Fin r) :
    dotBool y (fun a => decide (b = a)) = y b := by
  apply boolZ_inj
  rw [boolZ_dotBool]
  have hsum : (∑ a : Fin r, boolZ (y a) * boolZ (decide (b = a))) =
      ∑ a : Fin r, if a = b then boolZ (y b) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = b
    · subst ha; simp [boolZ]
    · simp [Ne.symm ha, ha, boolZ]
  rw [hsum, Finset.sum_ite_eq']
  simp

lemma indep_surjective : ∀ {r d : ℕ} (vecs : Fin r → Vec d),
    Indep vecs → Function.Surjective (evalVecs vecs)
  | 0, _, _, _ => fun y => ⟨fun _ => false, funext (fun a => Fin.elim0 a)⟩
  | r + 1, d, vecs, h => by
      rcases h with ⟨hinit, hnot⟩
      have ih := indep_surjective (Fin.init vecs) hinit
      have hex_u0 : ∃ u0 : Vec d,
          evalVecs (Fin.init vecs) u0 = (fun _ => false) ∧
          dotBool (vecs (Fin.last r)) u0 = true := by
        by_contra hnone
        push Not at hnone
        have hzero : ∀ w : Vec d,
            evalVecs (Fin.init vecs) w = (fun _ => false) →
            dotBool (vecs (Fin.last r)) w = false := by
          intro w hw
          cases hval : dotBool (vecs (Fin.last r)) w
          · rfl
          · exact absurd hval (hnone w hw)
        have hbasis : ∀ a : Fin r, ∃ ba : Vec d,
            evalVecs (Fin.init vecs) ba = (fun b => decide (b = a)) :=
          fun a => ih (fun b => decide (b = a))
        let basisU : Fin r → Vec d := fun a => Classical.choose (hbasis a)
        have hbasisU : ∀ a b : Fin r,
            dotBool (Fin.init vecs b) (basisU a) = decide (b = a) := by
          intro a b
          exact congrFun (Classical.choose_spec (hbasis a)) b
        let c : Fin r → Bool := fun a => dotBool (vecs (Fin.last r)) (basisU a)
        have hlin : ∀ u : Vec d,
            dotBool (vecs (Fin.last r)) u = dotBool (linComb (Fin.init vecs) c) u := by
          intro u
          let y : Fin r → Bool := evalVecs (Fin.init vecs) u
          let ucorr : Vec d := linComb basisU y
          let w : Vec d := xorV u ucorr
          have hw_zero : evalVecs (Fin.init vecs) w = (fun _ => false) := by
            funext b
            dsimp only [evalVecs, w]
            rw [dotBool_xorV_right]
            have hucorr : dotBool (Fin.init vecs b) ucorr = y b := by
              dsimp only [ucorr]
              rw [dotBool_comm, dotBool_linComb]
              have hfun : evalVecs basisU (Fin.init vecs b) = (fun a => decide (b = a)) := by
                funext a
                dsimp only [evalVecs]
                rw [dotBool_comm, hbasisU a b]
              rw [hfun, dotBool_basis_left]
            rw [hucorr]
            change xor (y b) (y b) = false
            cases y b <;> rfl
          have hw_val := hzero w hw_zero
          dsimp only [w] at hw_val
          rw [dotBool_xorV_right] at hw_val
          have heq_ucorr : dotBool (vecs (Fin.last r)) u =
              dotBool (vecs (Fin.last r)) ucorr := by
            cases h1 : dotBool (vecs (Fin.last r)) u <;>
              cases h2 : dotBool (vecs (Fin.last r)) ucorr <;>
              simp_all
          rw [heq_ucorr]
          dsimp only [ucorr]
          rw [dotBool_comm (vecs (Fin.last r)), dotBool_linComb, dotBool_linComb]
          have hc_eq : evalVecs basisU (vecs (Fin.last r)) = c := by
            funext a
            dsimp only [evalVecs, c]
            exact dotBool_comm (basisU a) (vecs (Fin.last r))
          rw [hc_eq, dotBool_comm]
        have hvec_eq : vecs (Fin.last r) = linComb (Fin.init vecs) c := by
          funext l
          have hl := hlin (fun k => decide (k = l))
          rwa [dotBool_basis_right, dotBool_basis_right] at hl
        exact hnot (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hvec_eq.symm⟩)
      obtain ⟨u0, hu0_init, hu0_last⟩ := hex_u0
      intro y
      obtain ⟨u1, hu1⟩ := ih (Fin.init y)
      by_cases hmatch : dotBool (vecs (Fin.last r)) u1 = y (Fin.last r)
      · refine ⟨u1, funext (Fin.lastCases hmatch (fun i => congrFun hu1 i))⟩
      · refine ⟨xorV u1 u0, funext (Fin.lastCases ?_ ?_)⟩
        · change dotBool (vecs (Fin.last r)) (xorV u1 u0) = y (Fin.last r)
          rw [dotBool_xorV_right, hu0_last]
          cases hdot : dotBool (vecs (Fin.last r)) u1 <;> cases hy : y (Fin.last r) <;>
            simp_all
        · intro i
          have h1 : dotBool (Fin.init vecs i) u1 = Fin.init y i := congrFun hu1 i
          have h0 : dotBool (Fin.init vecs i) u0 = false := congrFun hu0_init i
          change dotBool (Fin.init vecs i) (xorV u1 u0) = y i.castSucc
          rw [dotBool_xorV_right, h1, h0]
          have hiy : Fin.init y i = y i.castSucc := rfl
          rw [hiy]
          cases y i.castSucc <;> rfl

lemma card_spanSet_le {r d : ℕ} (vecs : Fin r → Vec d) : (spanSet vecs).card ≤ 2 ^ r := by
  calc (spanSet vecs).card
      ≤ (Finset.univ : Finset (Fin r → Bool)).card := Finset.card_image_le
    _ = 2 ^ r := by simp

lemma card_not_indep_le : ∀ (r d : ℕ),
    (Finset.univ.filter (fun vecs : Fin r → Vec d => ¬ Indep vecs)).card * 2 ^ d ≤
      (2 ^ r - 1) * (2 ^ d) ^ r
  | 0, d => by simp [Indep]
  | r + 1, d => by
      let badPrev : Finset (Fin r → Vec d) :=
        Finset.univ.filter (fun v => ¬ Indep v)
      let badAll : Finset (Fin (r + 1) → Vec d) :=
        Finset.univ.filter (fun v => ¬ Indep v)
      let part1 : Finset ((Fin r → Vec d) × Vec d) :=
        Finset.univ.filter (fun p => ¬ Indep p.1)
      let part2 : Finset ((Fin r → Vec d) × Vec d) :=
        Finset.univ.filter (fun p => p.2 ∈ spanSet p.1)
      let e : (Fin (r + 1) → Vec d) ≃ (Fin r → Vec d) × Vec d :=
        { toFun := fun v => (Fin.init v, v (Fin.last r))
          invFun := fun p => Fin.snoc p.1 p.2
          left_inv := fun v => by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simp
            · intro j; simp [Fin.init]
          right_inv := fun p => by
            apply Prod.ext
            · funext j; simp [Fin.init]
            · simp }
      have hbad_eq : badAll.card =
          (Finset.univ.filter (fun p : (Fin r → Vec d) × Vec d =>
            ¬ (Indep p.1 ∧ p.2 ∉ spanSet p.1))).card := by
        rw [show badAll.card = Fintype.card {v : Fin (r + 1) → Vec d // ¬ Indep v} by
          rw [Fintype.card_subtype]]
        let eSub : {v : Fin (r + 1) → Vec d // ¬ Indep v} ≃
            {p : (Fin r → Vec d) × Vec d // ¬ (Indep p.1 ∧ p.2 ∉ spanSet p.1)} :=
          { toFun := fun v => ⟨e v.1, v.2⟩
            invFun := fun p => ⟨e.symm p.1, by
              have h1 : Fin.init (e.symm p.1) = p.1.1 := by funext j; simp [e, Fin.init]
              have h2 : e.symm p.1 (Fin.last r) = p.1.2 := by simp [e]
              change ¬ (Indep (Fin.init (e.symm p.1)) ∧
                e.symm p.1 (Fin.last r) ∉ spanSet (Fin.init (e.symm p.1)))
              rw [h1, h2]
              exact p.2⟩
            left_inv := fun v => by apply Subtype.ext; exact e.left_inv v.1
            right_inv := fun p => by apply Subtype.ext; exact e.right_inv p.1 }
        rw [Fintype.card_congr eSub, Fintype.card_subtype]
      have hsub : Finset.univ.filter (fun p : (Fin r → Vec d) × Vec d =>
          ¬ (Indep p.1 ∧ p.2 ∉ spanSet p.1)) ⊆ part1 ∪ part2 := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hp
        rw [Finset.mem_union]
        rcases hp with h1 | h2
        · left; simpa [part1] using h1
        · right; simpa [part2] using h2
      have hpart1 : part1.card = badPrev.card * 2 ^ d := by
        rw [show part1 = badPrev ×ˢ (Finset.univ : Finset (Vec d)) by
          ext p; simp [part1, badPrev]]
        rw [Finset.card_product, Finset.card_univ]
        simp [Vec]
      have hpart2_sub : part2 ⊆ (Finset.univ : Finset (Fin r → Vec d)).biUnion
          (fun v => (spanSet v).image (fun w => (v, w))) := by
        intro p hp
        simp only [part2, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ p.1, Finset.mem_image.mpr ⟨p.2, hp, rfl⟩⟩
      have hpart2 : part2.card ≤ (2 ^ d) ^ r * 2 ^ r := by
        calc part2.card
            ≤ ((Finset.univ : Finset (Fin r → Vec d)).biUnion
                (fun v => (spanSet v).image (fun w => (v, w)))).card :=
              Finset.card_le_card hpart2_sub
          _ ≤ ∑ v : Fin r → Vec d, ((spanSet v).image (fun w => (v, w))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ v : Fin r → Vec d, (spanSet v).card :=
              Finset.sum_le_sum (fun v _ => Finset.card_image_le)
          _ ≤ ∑ _v : Fin r → Vec d, 2 ^ r :=
              Finset.sum_le_sum (fun v _ => card_spanSet_le v)
          _ = (Finset.univ : Finset (Fin r → Vec d)).card * 2 ^ r := by simp
          _ = (2 ^ d) ^ r * 2 ^ r := by simp [Vec]
      have hle_sum : badAll.card ≤ badPrev.card * 2 ^ d + (2 ^ d) ^ r * 2 ^ r := by
        rw [hbad_eq]
        calc _ ≤ (part1 ∪ part2).card := Finset.card_le_card hsub
          _ ≤ part1.card + part2.card := Finset.card_union_le _ _
          _ ≤ badPrev.card * 2 ^ d + (2 ^ d) ^ r * 2 ^ r := Nat.add_le_add hpart1.le hpart2
      have ih := card_not_indep_le r d
      have h2r_pos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      have hpow_succ2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
      calc badAll.card * 2 ^ d
          ≤ (badPrev.card * 2 ^ d + (2 ^ d) ^ r * 2 ^ r) * 2 ^ d := Nat.mul_le_mul_right _ hle_sum
        _ = (badPrev.card * 2 ^ d) * 2 ^ d + 2 ^ r * (2 ^ d) ^ (r + 1) := by
            rw [Nat.add_mul, pow_succ]; ring
        _ ≤ ((2 ^ r - 1) * (2 ^ d) ^ r) * 2 ^ d + 2 ^ r * (2 ^ d) ^ (r + 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ ih) _
        _ = ((2 ^ r - 1) + 2 ^ r) * (2 ^ d) ^ (r + 1) := by rw [pow_succ]; ring
        _ = (2 ^ (r + 1) - 1) * (2 ^ d) ^ (r + 1) := by
            congr 1
            omega

def GoodSet {n d : ℕ} (I : Finset (Fin n)) (B : Fin n → Vec d) : Prop :=
  Indep (fun t : Fin (Fintype.card I) => B ((Fintype.equivFin I).symm t).1)

lemma surj_of_goodSet {n d : ℕ} {I : Finset (Fin n)} {B : Fin n → Vec d}
    (hB : GoodSet I B) :
    ∀ y : I → Bool, ∃ u : Vec d, ∀ x : I, dotBool (B x.1) u = y x := by
  intro y
  let vecs : Fin (Fintype.card I) → Vec d :=
    fun t => B ((Fintype.equivFin I).symm t).1
  obtain ⟨u, hu⟩ := indep_surjective vecs hB (fun t => y ((Fintype.equivFin I).symm t))
  refine ⟨u, fun x => ?_⟩
  have h1 := congrFun hu ((Fintype.equivFin I) x)
  simpa [evalVecs, vecs] using h1

lemma card_not_goodSet_le {n d : ℕ} (I : Finset (Fin n)) :
    (Finset.univ.filter (fun B : Fin n → Vec d => ¬ GoodSet I B)).card * 2 ^ d ≤
      (2 ^ I.card - 1) * (2 ^ d) ^ n := by
  let R := {j : Fin n // j ∉ I}
  let eSplit : (Fin n → Vec d) ≃ (Fin (Fintype.card I) → Vec d) × (R → Vec d) :=
    { toFun := fun B =>
        (fun t => B ((Fintype.equivFin I).symm t).1, fun j => B j.1)
      invFun := fun p j =>
        if hj : j ∈ I then p.1 ((Fintype.equivFin I) ⟨j, hj⟩) else p.2 ⟨j, hj⟩
      left_inv := fun B => by
        funext j
        by_cases hj : j ∈ I <;> simp [hj]
      right_inv := fun p => by
        apply Prod.ext
        · funext t
          have hm : ((Fintype.equivFin I).symm t).1 ∈ I := ((Fintype.equivFin I).symm t).2
          simp [hm]
        · funext j
          simp [j.2] }
  let badI := Finset.univ.filter (fun v : Fin (Fintype.card I) → Vec d => ¬ Indep v)
  have heq : (Finset.univ.filter (fun B : Fin n → Vec d => ¬ GoodSet I B)).card =
      badI.card * Fintype.card (R → Vec d) := by
    rw [show (Finset.univ.filter (fun B : Fin n → Vec d => ¬ GoodSet I B)).card =
        Fintype.card {B : Fin n → Vec d // ¬ GoodSet I B} by rw [Fintype.card_subtype]]
    let eSub : {B : Fin n → Vec d // ¬ GoodSet I B} ≃ {v : Fin (Fintype.card I) → Vec d // ¬ Indep v} × (R → Vec d) :=
      { toFun := fun B => (⟨(eSplit B.1).1, B.2⟩, (eSplit B.1).2)
        invFun := fun p => ⟨eSplit.symm (p.1.1, p.2), by
          change ¬ Indep (eSplit (eSplit.symm (p.1.1, p.2))).1
          rw [Equiv.apply_symm_apply eSplit (p.1.1, p.2)]
          exact p.1.2⟩
        left_inv := fun B => by apply Subtype.ext; exact eSplit.left_inv B.1
        right_inv := fun p => by
          apply Prod.ext
          · apply Subtype.ext; exact congrArg Prod.fst (Equiv.apply_symm_apply eSplit (p.1.1, p.2))
          · dsimp only; rw [Equiv.apply_symm_apply eSplit (p.1.1, p.2)] }
    rw [Fintype.card_congr eSub, Fintype.card_prod, Fintype.card_subtype]
  have hR : Fintype.card R = n - I.card := by
    rw [Fintype.card_subtype]
    have hcompl : Finset.univ.filter (fun j : Fin n => j ∉ I) = Iᶜ := by ext j; simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin]
  have hI : Fintype.card I = I.card := Fintype.card_coe I
  have hbad := card_not_indep_le (Fintype.card I) d
  rw [heq, Fintype.card_fun, hR]
  have hVcard : Fintype.card (Vec d) = 2 ^ d := by simp [Vec]
  rw [hVcard]
  calc (badI.card * (2 ^ d) ^ (n - I.card)) * 2 ^ d
      = (badI.card * 2 ^ d) * (2 ^ d) ^ (n - I.card) := by ring
    _ ≤ ((2 ^ Fintype.card I - 1) * (2 ^ d) ^ Fintype.card I) * (2 ^ d) ^ (n - I.card) :=
        Nat.mul_le_mul_right _ hbad
    _ = (2 ^ I.card - 1) * ((2 ^ d) ^ I.card * (2 ^ d) ^ (n - I.card)) := by rw [hI]; ring
    _ = (2 ^ I.card - 1) * (2 ^ d) ^ n := by
        rw [← pow_add]
        congr 2
        have := Finset.card_le_univ I
        simp only [Fintype.card_fin] at this
        omega

abbrev Desc (n : ℕ) := Lit n × (Fin n → Option Bool)

def KOf {n : ℕ} (p : Desc n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (p.2 j).isSome = true)

def goodStars (n s : ℕ) : Finset (Desc n) :=
  Finset.univ.filter (fun p => (KOf p).card ≤ s - 1 ∧ p.2 p.1.1 = none)

lemma card_goodStars_le {n s : ℕ} (hs : 3 ≤ s) :
    (goodStars n s).card ≤ 2 ^ (s * (1 + Nat.clog 2 (n + 1))) := by
  let L := Nat.clog 2 (n + 1)
  let Target := Lit n × (Fin (s - 1) → Option (Lit n))
  let enc (p : Desc n) : Target :=
    (p.1, fun t : Fin (s - 1) =>
      if h : t.val < Fintype.card (KOf p) then
        let x := (Fintype.equivFin (KOf p)).symm ⟨t.val, h⟩
        match p.2 x.1 with
        | some b => some (x.1, b)
        | none => none
      else none)
  have hinj : Set.InjOn enc (goodStars n s : Set (Desc n)) := by
    intro p1 hp1m p2 hp2m heq
    have hp1_first : p1.1 = p2.1 := congrArg (fun x : Target => x.1) heq
    have hf_eq : (enc p1).2 = (enc p2).2 := congrArg (fun x : Target => x.2) heq
    have hmem : ∀ (p q : Desc n), p ∈ goodStars n s →
        (enc p).2 = (enc q).2 → ∀ (j : Fin n) (b : Bool), p.2 j = some b → q.2 j = some b := by
      intro p q hpg hpq j b hpj
      have hjK : j ∈ KOf p := by simp [KOf, hpj]
      let idx := (Fintype.equivFin (KOf p)) ⟨j, hjK⟩
      have hcard_le : (KOf p).card ≤ s - 1 := by
        simp only [goodStars, Finset.mem_filter, Finset.mem_univ, true_and] at hpg
        exact hpg.1
      have hlt_card : idx.val < (KOf p).card := by
        simpa [Fintype.card_coe] using idx.isLt
      have hlt_s : idx.val < s - 1 := lt_of_lt_of_le hlt_card hcard_le
      let t : Fin (s - 1) := ⟨idx.val, hlt_s⟩
      have ht := congrFun hpq t
      have hx_eq : ((Fintype.equivFin (KOf p)).symm ⟨t.val, idx.isLt⟩) = ⟨j, hjK⟩ := by
        simp [t, idx]
      have h1 : (enc p).2 t = some (j, b) := by
        dsimp only [enc]
        rw [dif_pos idx.isLt, hx_eq, hpj]
      rw [h1] at ht
      dsimp only [enc] at ht
      split_ifs at ht with hq
      · cases hqx : q.2 ((Fintype.equivFin (KOf q)).symm ⟨t.val, hq⟩).1 with
        | none => simp [hqx] at ht
        | some b' =>
            simp only [hqx, Option.some.injEq, Prod.mk.injEq] at ht
            rw [← ht.1] at hqx
            rw [← ht.2] at hqx
            exact hqx
    have hp1g : p1 ∈ goodStars n s := Finset.mem_coe.mp hp1m
    have hp2g : p2 ∈ goodStars n s := Finset.mem_coe.mp hp2m
    have hfun : ∀ j : Fin n, p1.2 j = p2.2 j := by
      intro j
      cases h1 : p1.2 j with
      | some b => exact (hmem p1 p2 hp1g hf_eq j b h1).symm
      | none =>
          cases h2 : p2.2 j with
          | none => rfl
          | some b => exact absurd (hmem p2 p1 hp2g hf_eq.symm j b h2) (by simp [h1])
    exact Prod.ext hp1_first (funext hfun)
  have hle_target : (goodStars n s).card ≤ Fintype.card Target := by
    calc (goodStars n s).card
        = ((goodStars n s).image enc).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card Target := Finset.card_le_univ _
  have hcard_target : Fintype.card Target = (2 * n) * (2 * n + 1) ^ (s - 1) := by
    simp [Target, Lit, mul_comm]
  have hclog : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) (n + 1)
  have h2n : 2 * n ≤ 2 ^ (1 + L) := by
    rw [pow_add, pow_one]
    omega
  have h2n1 : 2 * n + 1 ≤ 2 ^ (1 + L) := by
    rw [pow_add, pow_one]
    omega
  calc (goodStars n s).card
      ≤ (2 * n) * (2 * n + 1) ^ (s - 1) := hle_target.trans_eq hcard_target
    _ ≤ 2 ^ (1 + L) * (2 ^ (1 + L)) ^ (s - 1) :=
        Nat.mul_le_mul h2n (Nat.pow_le_pow_left h2n1 (s - 1))
    _ = 2 ^ ((1 + L) * (1 + (s - 1))) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
    _ = 2 ^ (s * (1 + L)) := by
        congr 1
        have : 1 + (s - 1) = s := by omega
        rw [this, mul_comm]

lemma card_all_bad_blocks_le {α : Type*} [Fintype α] [DecidableEq α]
    (BadB : Finset α) (T c : ℕ) (hc : c * BadB.card ≤ Fintype.card α) :
    c ^ T * (Finset.univ.filter (fun S : Fin T → α => ∀ b : Fin T, S b ∈ BadB)).card ≤
      (Fintype.card α) ^ T := by
  have heq : (Finset.univ.filter (fun S : Fin T → α => ∀ b : Fin T, S b ∈ BadB)).card =
      BadB.card ^ T := by
    rw [show (Finset.univ.filter (fun S : Fin T → α => ∀ b : Fin T, S b ∈ BadB)).card =
        Fintype.card {S : Fin T → α // ∀ b : Fin T, S b ∈ BadB} by rw [Fintype.card_subtype]]
    let e : {S : Fin T → α // ∀ b : Fin T, S b ∈ BadB} ≃ (Fin T → {x : α // x ∈ BadB}) :=
      { toFun := fun S b => ⟨S.1 b, S.2 b⟩
        invFun := fun f => ⟨fun b => (f b).1, fun b => (f b).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  rw [heq, ← mul_pow]
  exact Nat.pow_le_pow_left hc T

noncomputable def FailCenter (n s : ℕ) (p : Desc n) : Finset (Fin (tBlocks n s) → Fin n → Vec (s + 2)) :=
  Finset.univ.filter (fun S => ∀ b : Fin (tBlocks n s), ¬ GoodSet (insert p.1.1 (KOf p)) (S b))

noncomputable def FailBit (n s : ℕ) (p : Desc n) (j : Fin n) :
    Finset (Fin (tBlocks n s) → Fin n → Vec (s + 2)) :=
  Finset.univ.filter (fun S =>
    ∀ b : Fin (tBlocks n s), ¬ GoodSet (insert j (insert p.1.1 (KOf p))) (S b))

noncomputable def BadSeed (n s : ℕ) (p : Desc n) : Finset (Fin (tBlocks n s) → Fin n → Vec (s + 2)) :=
  FailCenter n s p ∪ (Finset.univ.filter (fun j : Fin n => j ∉ insert p.1.1 (KOf p))).biUnion
    (FailBit n s p)

lemma badSeed_card_bound {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {p : Desc n} (hp : p ∈ goodStars n s) :
    192 * (BadSeed n s p).card ≤ Fintype.card (Fin (tBlocks n s) → Fin n → Vec (s + 2)) := by
  let T := tBlocks n s
  let d := s + 2
  let Block := Fin n → Vec d
  let Seed := Fin T → Block
  let N_block := Fintype.card Block
  let N_seed := Fintype.card Seed
  have hN_block : N_block = (2 ^ d) ^ n := by simp [N_block, Block, Vec]
  have hN_seed : N_seed = N_block ^ T := by simp [N_seed, Seed, N_block]
  have hp_mem : (KOf p).card ≤ s - 1 ∧ p.2 p.1.1 = none := by
    simpa [goodStars] using hp
  have hi_not_K : p.1.1 ∉ KOf p := by
    simp [KOf, hp_mem.2]
  let S0 := insert p.1.1 (KOf p)
  have hS0_card : S0.card = (KOf p).card + 1 := Finset.card_insert_of_notMem hi_not_K
  let badC := Finset.univ.filter (fun B : Block => ¬ GoodSet S0 B)
  have hbadC_le : 4 * badC.card ≤ N_block := by
    have h1 := card_not_goodSet_le S0 (d := d)
    have hS0_le : S0.card ≤ s := by omega
    have hpow1 : 2 ^ S0.card - 1 ≤ 2 ^ s := le_trans (Nat.sub_le _ 1) (Nat.pow_le_pow_right (by norm_num) hS0_le)
    have hd_eq : 2 ^ d = 4 * 2 ^ s := by
      dsimp only [d]
      rw [pow_add]
      norm_num
      ring
    have h2 : (4 * badC.card) * 2 ^ s ≤ 2 ^ s * (2 ^ d) ^ n := by
      calc (4 * badC.card) * 2 ^ s
          = badC.card * (4 * 2 ^ s) := by ring
        _ = badC.card * 2 ^ d := by rw [← hd_eq]
        _ ≤ (2 ^ S0.card - 1) * (2 ^ d) ^ n := h1
        _ ≤ 2 ^ s * (2 ^ d) ^ n := Nat.mul_le_mul_right _ hpow1
    have h3 : 4 * badC.card ≤ (2 ^ d) ^ n := by
      have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
      rw [mul_comm (2 ^ s)] at h2
      exact Nat.le_of_mul_le_mul_right h2 hpos
    simpa [hN_block] using h3
  have hfailC : 65536 * (FailCenter n s p).card ≤ N_seed := by
    have hfc_eq : FailCenter n s p =
        Finset.univ.filter (fun S : Fin T → Block => ∀ b : Fin T, S b ∈ badC) := by
      ext S
      simp [FailCenter, badC, S0, T]
    have hT : 4 ^ T * (FailCenter n s p).card ≤ N_block ^ T := by
      rw [hfc_eq]
      exact card_all_bad_blocks_le badC T 4 hbadC_le
    have h8 : 8 ≤ T := by dsimp [T, tBlocks]; omega
    have hpow : (65536 : ℕ) ≤ 4 ^ T := by
      calc (65536 : ℕ) = 4 ^ 8 := by norm_num
        _ ≤ 4 ^ T := Nat.pow_le_pow_right (by norm_num) h8
    calc 65536 * (FailCenter n s p).card
        ≤ 4 ^ T * (FailCenter n s p).card := Nat.mul_le_mul_right _ hpow
      _ ≤ N_block ^ T := hT
      _ = N_seed := hN_seed.symm
  let Free := Finset.univ.filter (fun j : Fin n => j ∉ S0)
  let m := (s - 1) - (KOf p).card
  have hm_eq : (KOf p).card + m = s - 1 := Nat.add_sub_of_le hp_mem.1
  have hfree_card : Free.card = (n - s) + m := by
    have hcompl : Free = S0ᶜ := by ext j; simp [Free]
    have hle_n : S0.card ≤ n := by omega
    rw [hcompl, Finset.card_compl, Fintype.card_fin, hS0_card]
    omega
  have hfailB_each : ∀ j ∈ Free, (2 ^ (m + 1)) ^ T * (FailBit n s p j).card ≤ N_seed := by
    intro j hj
    have hj_not : j ∉ S0 := (Finset.mem_filter.mp hj).2
    let S1 := insert j S0
    have hS1_card : S1.card = (KOf p).card + 2 := by
      rw [Finset.card_insert_of_notMem hj_not, hS0_card]
    let badJ := Finset.univ.filter (fun B : Block => ¬ GoodSet S1 B)
    have hbadJ_le : 2 ^ (m + 1) * badJ.card ≤ N_block := by
      have h1 := card_not_goodSet_le S1 (d := d)
      have hd_eq : 2 ^ d = 2 ^ (m + 1) * 2 ^ S1.card := by
        rw [← pow_add]
        congr 1
        dsimp only [d]
        omega
      have hpow1 : 2 ^ S1.card - 1 ≤ 2 ^ S1.card := Nat.sub_le _ 1
      have h2 : (2 ^ (m + 1) * badJ.card) * 2 ^ S1.card ≤ (2 ^ d) ^ n * 2 ^ S1.card := by
        calc (2 ^ (m + 1) * badJ.card) * 2 ^ S1.card
            = badJ.card * (2 ^ (m + 1) * 2 ^ S1.card) := by ring
          _ = badJ.card * 2 ^ d := by rw [← hd_eq]
          _ ≤ (2 ^ S1.card - 1) * (2 ^ d) ^ n := h1
          _ ≤ 2 ^ S1.card * (2 ^ d) ^ n := Nat.mul_le_mul_right _ hpow1
          _ = (2 ^ d) ^ n * 2 ^ S1.card := by ring
      have h3 : 2 ^ (m + 1) * badJ.card ≤ (2 ^ d) ^ n :=
        Nat.le_of_mul_le_mul_right h2 (Nat.two_pow_pos S1.card)
      simpa [hN_block] using h3
    have hfb_eq : FailBit n s p j =
        Finset.univ.filter (fun S : Fin T → Block => ∀ b : Fin T, S b ∈ badJ) := by
      ext S
      simp [FailBit, badJ, S1, S0, T]
    have hT : (2 ^ (m + 1)) ^ T * (FailBit n s p j).card ≤ N_seed := by
      rw [hfb_eq]
      simpa [N_seed, Seed, N_block] using card_all_bad_blocks_le badJ T (2 ^ (m + 1)) hbadJ_le
    exact hT
  have hfree_pow : 256 * Free.card ≤ (2 ^ (m + 1)) ^ T := by
    let dn := Nat.clog 2 (n - s + 1)
    have hT_eq : T = 8 + dn := rfl
    have hclog : n - s + 1 ≤ 2 ^ dn := Nat.le_pow_clog (by norm_num) (n - s + 1)
    have hm_le_pow : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
    have hpos_2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hfree_bound : Free.card ≤ 2 ^ dn * 2 ^ m := by
      calc Free.card = (n - s) + m := hfree_card
        _ ≤ (n - s) * 2 ^ m + 2 ^ m := Nat.add_le_add (Nat.le_mul_of_pos_right _ hpos_2m) hm_le_pow
        _ = (n - s + 1) * 2 ^ m := by ring
        _ ≤ 2 ^ dn * 2 ^ m := Nat.mul_le_mul_right _ hclog
    have hexp : 8 + dn + m ≤ (m + 1) * T := by
      have : (m + 1) * (8 + dn) = 8 + dn + 8 * m + m * dn := by ring
      rw [hT_eq, this]
      omega
    calc 256 * Free.card
        ≤ 2 ^ 8 * (2 ^ dn * 2 ^ m) := Nat.mul_le_mul_left 256 hfree_bound
      _ = 2 ^ (8 + dn + m) := by rw [← pow_add, ← pow_add, add_assoc]
      _ ≤ 2 ^ ((m + 1) * T) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ (m + 1)) ^ T := by rw [pow_mul]
  have hfail_union : 256 * (Free.biUnion (FailBit n s p)).card ≤ N_seed := by
    have hpos_den : 0 < (2 ^ (m + 1)) ^ T := pow_pos (Nat.two_pow_pos (m + 1)) T
    have hsum : (2 ^ (m + 1)) ^ T * ∑ j ∈ Free, (FailBit n s p j).card ≤ Free.card * N_seed := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ Free, (2 ^ (m + 1)) ^ T * (FailBit n s p j).card
          ≤ ∑ _j ∈ Free, N_seed := Finset.sum_le_sum (fun j hj => hfailB_each j hj)
        _ = Free.card * N_seed := by simp
    have hcomb : (2 ^ (m + 1)) ^ T * (256 * (Free.biUnion (FailBit n s p)).card) ≤
        (2 ^ (m + 1)) ^ T * N_seed := by
      calc (2 ^ (m + 1)) ^ T * (256 * (Free.biUnion (FailBit n s p)).card)
          = 256 * ((2 ^ (m + 1)) ^ T * (Free.biUnion (FailBit n s p)).card) := by ring
        _ ≤ 256 * ((2 ^ (m + 1)) ^ T * ∑ j ∈ Free, (FailBit n s p j).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ Finset.card_biUnion_le)
        _ ≤ 256 * (Free.card * N_seed) := Nat.mul_le_mul_left 256 hsum
        _ = (256 * Free.card) * N_seed := by ring
        _ ≤ (2 ^ (m + 1)) ^ T * N_seed := Nat.mul_le_mul_right N_seed hfree_pow
    exact Nat.le_of_mul_le_mul_left hcomb hpos_den
  have hbad_sum : (BadSeed n s p).card ≤
      (FailCenter n s p).card + (Free.biUnion (FailBit n s p)).card := by
    exact Finset.card_union_le _ _
  have h65536 : 65536 * (BadSeed n s p).card ≤ 257 * N_seed := by
    calc 65536 * (BadSeed n s p).card
        ≤ 65536 * (FailCenter n s p).card + 256 * (256 * (Free.biUnion (FailBit n s p)).card) := by
          omega
      _ ≤ N_seed + 256 * N_seed := Nat.add_le_add hfailC (Nat.mul_le_mul_left 256 hfail_union)
      _ = 257 * N_seed := by ring
  change 192 * (BadSeed n s p).card ≤ N_seed
  omega

lemma sum_prod_eq_pow {α : Type*} [Fintype α] (w : α → ℕ) :
    ∀ k : ℕ, (∑ f : Fin k → α, ∏ i : Fin k, w (f i)) = (∑ x : α, w x) ^ k
  | 0 => by simp
  | k + 1 => by
      let e : (Fin (k + 1) → α) ≃ (Fin k → α) × α :=
        { toFun := fun f => (Fin.init f, f (Fin.last k))
          invFun := fun p => Fin.snoc p.1 p.2
          left_inv := fun f => by
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simp
            · intro j; simp [Fin.init]
          right_inv := fun p => by
            apply Prod.ext
            · funext j; simp [Fin.init]
            · simp }
      rw [Fintype.sum_equiv e _ (fun p => (∏ i : Fin k, w (p.1 i)) * w p.2) (fun f => by
        rw [Fin.prod_univ_castSucc]
        simp [e, Fin.init])]
      rw [Fintype.sum_prod_type]
      have hinner : ∀ f : Fin k → α,
          (∑ x : α, (∏ i : Fin k, w (f i)) * w x) = (∏ i : Fin k, w (f i)) * (∑ x : α, w x) :=
        fun f => (Finset.mul_sum Finset.univ w (∏ i : Fin k, w (f i))).symm
      simp_rw [hinner, ← Finset.sum_mul, sum_prod_eq_pow w k, pow_succ]

lemma exists_good_row {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n) :
    ∃ row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2),
      ∀ p ∈ goodStars n s,
        3 * mSeeds n s ≤
          4 * (Finset.univ.filter (fun u : Fin (mSeeds n s) => row u ∉ BadSeed n s p)).card := by
  let L := Nat.clog 2 (n + 1)
  let M := mSeeds n s
  let Seed := Fin (tBlocks n s) → Fin n → Vec (s + 2)
  let N_seed := Fintype.card Seed
  let Row := Fin M → Seed
  have hM_ge : 4 + (s + 4) * (1 + L) ≤ M := Nat.le_pow_clog (by norm_num) _
  have hL_ge : 1 ≤ L := by
    have : 2 ≤ n + 1 := by omega
    exact Nat.clog_pos (by norm_num) this
  have hclog_ge : 4 ≤ Nat.clog 2 (4 + (s + 4) * (1 + L)) := by
    by_contra hlt
    have hle3 : Nat.clog 2 (4 + (s + 4) * (1 + L)) ≤ 3 := by omega
    have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) (4 + (s + 4) * (1 + L))
    have hpow3 : 2 ^ Nat.clog 2 (4 + (s + 4) * (1 + L)) ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by norm_num) hle3
    have hmul : 7 * 2 ≤ (s + 4) * (1 + L) := Nat.mul_le_mul (by omega) (by omega)
    omega
  let eM := Nat.clog 2 (4 + (s + 4) * (1 + L))
  have heM : 2 ≤ eM := by omega
  let r := 2 ^ (eM - 2)
  have hM4r : M = 4 * r := by
    have heq : eM = 2 + (eM - 2) := by omega
    change 2 ^ eM = 4 * 2 ^ (eM - 2)
    rw [heq, pow_add]
    norm_num
  have hr_pos : 1 ≤ r := Nat.one_le_two_pow
  let BadRow (p : Desc n) : Finset Row :=
    Finset.univ.filter (fun row =>
      4 * (Finset.univ.filter (fun u : Fin M => row u ∉ BadSeed n s p)).card < 3 * M)
  have hbadRow_bound : ∀ p ∈ goodStars n s,
      2 ^ M * (BadRow p).card ≤ N_seed ^ M := by
    intro p hp
    let wt : Seed → ℕ := fun x => if x ∈ BadSeed n s p then 64 else 1
    have hbadS : 192 * (BadSeed n s p).card ≤ N_seed := badSeed_card_bound hs hsn hp
    have hsum_wt : 3 * ∑ x : Seed, wt x ≤ 4 * N_seed := by
      have hsplit : ∑ x : Seed, wt x =
          ∑ x ∈ BadSeed n s p, 64 + ∑ x ∈ (BadSeed n s p)ᶜ, 1 := by
        rw [← Finset.sum_add_sum_compl (BadSeed n s p) wt]
        congr 1
        · exact Finset.sum_congr rfl (fun x hx => by simp [wt, hx])
        · exact Finset.sum_congr rfl (fun x hx => by
            have hxn : x ∉ BadSeed n s p := Finset.mem_compl.mp hx
            simp [wt, hxn])
      have hcard_c : (BadSeed n s p)ᶜ.card + (BadSeed n s p).card = N_seed := by
        rw [Finset.card_compl, add_comm]
        exact Nat.add_sub_of_le (Finset.card_le_univ _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsplit
      omega
    have hrow_wt : ∀ row ∈ BadRow p, 64 ^ r ≤ ∏ u : Fin M, wt (row u) := by
      intro row hrow
      simp only [BadRow, Finset.mem_filter, Finset.mem_univ, true_and] at hrow
      let G := Finset.univ.filter (fun u : Fin M => row u ∈ BadSeed n s p)
      have hpart : G.card + (Finset.univ.filter (fun u : Fin M => row u ∉ BadSeed n s p)).card = M := by
        have h1 := card_filter_add_card_filter_not (Finset.univ : Finset (Fin M))
          (fun u => row u ∈ BadSeed n s p)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      have hr_le_G : r ≤ G.card := by omega
      have hprod : ∏ u : Fin M, wt (row u) = 64 ^ G.card := by
        have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun u : Fin M => row u ∈ BadSeed n s p) (fun u => wt (row u))
        have hp1 : ∏ u ∈ G, wt (row u) = 64 ^ G.card := by
          calc ∏ u ∈ G, wt (row u)
              = ∏ _u ∈ G, 64 := Finset.prod_congr rfl (fun u hu => by
                  have := (Finset.mem_filter.mp hu).2; simp [wt, this])
            _ = 64 ^ G.card := by simp
        have hp2 : ∏ u ∈ Finset.univ.filter (fun u : Fin M => row u ∉ BadSeed n s p), wt (row u) = 1 := by
          calc ∏ u ∈ Finset.univ.filter (fun u : Fin M => row u ∉ BadSeed n s p), wt (row u)
              = ∏ _u ∈ Finset.univ.filter (fun u : Fin M => row u ∉ BadSeed n s p), 1 :=
                Finset.prod_congr rfl (fun u hu => by
                  have := (Finset.mem_filter.mp hu).2; simp [wt, this])
            _ = 1 := by simp
        rw [← hsplit, show G = Finset.univ.filter (fun u : Fin M => row u ∈ BadSeed n s p) from rfl,
          hp1, hp2, mul_one]
      rw [hprod]
      exact Nat.pow_le_pow_right (by norm_num) hr_le_G
    have hsum_all : 64 ^ r * (BadRow p).card ≤ (∑ x : Seed, wt x) ^ M := by
      calc 64 ^ r * (BadRow p).card
          = ∑ _row ∈ BadRow p, 64 ^ r := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ row ∈ BadRow p, ∏ u : Fin M, wt (row u) := Finset.sum_le_sum hrow_wt
        _ ≤ ∑ row : Row, ∏ u : Fin M, wt (row u) :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        _ = (∑ x : Seed, wt x) ^ M := sum_prod_eq_pow wt M
    have h3M : 3 ^ M * (64 ^ r * (BadRow p).card) ≤ 4 ^ M * N_seed ^ M := by
      calc 3 ^ M * (64 ^ r * (BadRow p).card)
          ≤ 3 ^ M * (∑ x : Seed, wt x) ^ M := Nat.mul_le_mul_left _ hsum_all
        _ = (3 * ∑ x : Seed, wt x) ^ M := (mul_pow _ _ _).symm
        _ ≤ (4 * N_seed) ^ M := Nat.pow_le_pow_left hsum_wt M
        _ = 4 ^ M * N_seed ^ M := mul_pow _ _ _
    have h5184 : 5184 ^ r * (BadRow p).card ≤ 256 ^ r * N_seed ^ M := by
      have h3e : 3 ^ M = 81 ^ r := by rw [hM4r, pow_mul]; norm_num
      have h4e : 4 ^ M = 256 ^ r := by rw [hM4r, pow_mul]; norm_num
      rw [h3e, h4e] at h3M
      calc 5184 ^ r * (BadRow p).card
          = (81 ^ r * 64 ^ r) * (BadRow p).card := by
            rw [← mul_pow]; norm_num
        _ = 81 ^ r * (64 ^ r * (BadRow p).card) := by ring
        _ ≤ 256 ^ r * N_seed ^ M := h3M
    have h2e : 2 ^ M = 16 ^ r := by rw [hM4r, pow_mul]; norm_num
    have h4096 : 4096 ^ r ≤ 5184 ^ r := Nat.pow_le_pow_left (by norm_num) r
    have hfin : 5184 ^ r * (2 ^ M * (BadRow p).card) ≤ 5184 ^ r * N_seed ^ M := by
      calc 5184 ^ r * (2 ^ M * (BadRow p).card)
          = 16 ^ r * (5184 ^ r * (BadRow p).card) := by rw [h2e]; ring
        _ ≤ 16 ^ r * (256 ^ r * N_seed ^ M) := Nat.mul_le_mul_left _ h5184
        _ = 4096 ^ r * N_seed ^ M := by rw [← mul_assoc, ← mul_pow]; norm_num
        _ ≤ 5184 ^ r * N_seed ^ M := Nat.mul_le_mul_right _ h4096
    exact Nat.le_of_mul_le_mul_left hfin (pow_pos (by norm_num) r)
  let BadAll := (goodStars n s).biUnion BadRow
  have hstars_lt : (goodStars n s).card < 2 ^ M := by
    have h1 := card_goodStars_le (n := n) hs
    have hle_mul : s * (1 + L) ≤ (s + 4) * (1 + L) := Nat.mul_le_mul_right _ (by omega)
    have h2 : s * (1 + L) < M := by omega
    exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) h2)
  have hbadAll_lt : BadAll.card < N_seed ^ M := by
    have h1 : 2 ^ M * BadAll.card < 2 ^ M * N_seed ^ M := by
      calc 2 ^ M * BadAll.card
          ≤ 2 ^ M * ∑ p ∈ goodStars n s, (BadRow p).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ p ∈ goodStars n s, 2 ^ M * (BadRow p).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _p ∈ goodStars n s, N_seed ^ M := Finset.sum_le_sum hbadRow_bound
        _ = (goodStars n s).card * N_seed ^ M := by simp
        _ < 2 ^ M * N_seed ^ M := Nat.mul_lt_mul_of_pos_right hstars_lt (by
            dsimp [N_seed, Seed, Vec]; positivity)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hcardRow : Fintype.card Row = N_seed ^ M := by simp [Row, N_seed]
  have hne : (Finset.univ \ BadAll).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle : Fintype.card Row ≤ BadAll.card := by
      simpa using Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
    omega
  obtain ⟨row, hrow⟩ := hne
  rw [Finset.mem_sdiff] at hrow
  refine ⟨row, fun p hp => ?_⟩
  have hnot : row ∉ BadRow p := fun h => hrow.2 (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  simp only [BadRow, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  exact hnot

def reportWord {n s : ℕ}
    (row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
    (seed : Fin (mSeeds n s)) (b : Fin (tBlocks n s)) (u : Vec (s + 2)) : W n :=
  fun bit => dotBool (row seed b bit) u

noncomputable def reportPos (n s : ℕ)
    (row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
    (seed : Fin (mSeeds n s)) (l : Lit n)
    (ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool) :
    Finset (Fin (tBlocks n s) × Vec (s + 2)) :=
  Finset.univ.filter (fun p =>
    reportWord row seed p.1 p.2 l.1 = !l.2 ∧ ans2 p.1 p.2 = true)

noncomputable def reportS (n s : ℕ)
    (row : Fin (mSeeds n s)) (l : Lit n) (w0 : W n)
    (rowAll : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
    (Pos : Finset (Fin (tBlocks n s) × Vec (s + 2))) : Finset (Fin n) :=
  (Finset.univ.erase l.1).filter (fun j =>
    ∀ p ∈ Pos, reportWord rowAll row p.1 p.2 j = w0 j)

noncomputable def myReportCase2 (n s : ℕ)
    (row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
    (seed : Fin (mSeeds n s)) (l : Lit n)
    (ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool) : Option (Formula n) :=
  if hPos : (reportPos n s row seed l ans2).Nonempty then
    let p0 := Classical.choose hPos
    let w0 := reportWord row seed p0.1 p0.2
    let S := reportS n s seed l w0 row (reportPos n s row seed l ans2)
    if _hcert : S.card ≤ s - 1 ∧
        ∀ j ∈ S, ∃ q : Fin (tBlocks n s) × Vec (s + 2),
          ans2 q.1 q.2 = false ∧
          reportWord row seed q.1 q.2 l.1 = !l.2 ∧
          ∀ k ∈ S, k ≠ j → reportWord row seed q.1 q.2 k = w0 k then
      some (mkBranchFormulaS l.1 l.2 w0 S)
    else none
  else none

lemma myReportCase2_isSome {n s : ℕ}
    {row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2)}
    {seed : Fin (mSeeds n s)} {l : Lit n}
    {ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool}
    (hPos : (reportPos n s row seed l ans2).Nonempty)
    (hcert : let p0 := Classical.choose hPos
      let w0 := reportWord row seed p0.1 p0.2
      let S := reportS n s seed l w0 row (reportPos n s row seed l ans2)
      S.card ≤ s - 1 ∧ ∀ j ∈ S, ∃ q : Fin (tBlocks n s) × Vec (s + 2),
        ans2 q.1 q.2 = false ∧
        reportWord row seed q.1 q.2 l.1 = !l.2 ∧
        ∀ k ∈ S, k ≠ j → reportWord row seed q.1 q.2 k = w0 k) :
    (myReportCase2 n s row seed l ans2).isSome = true := by
  unfold myReportCase2
  rw [dif_pos hPos, dif_pos hcert]
  rfl

noncomputable def myReport (n s : ℕ) (cal : Fin (q1 n) → W n)
    (row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
    (seed : Fin (mSeeds n s)) (ans1 : Fin (q1 n) → Bool)
    (ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool) : Option (Formula n) :=
  let H := posHull cal ans1
  if hlit : ∃ l : Lit n, IsLitHalf H l then
    myReportCase2 n s row seed (Classical.choose hlit) ans2
  else
    if high s H then some H else none

lemma main_thm : ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
    ∃ (cal : Fin (q1 n) → W n)
      (row : Fin (mSeeds n s) → Fin (tBlocks n s) → Fin n → Vec (s + 2))
      (report : Fin (mSeeds n s) → (Fin (q1 n) → Bool) → (Fin (tBlocks n s) → Vec (s + 2) → Bool) → Option (Formula n)),
      ∀ C : Formula n,
        let result := fun seed : Fin (mSeeds n s) =>
          report seed (fun slot => sat C (cal slot)) (fun block input => sat C (fun bit =>
            dotBool (row seed block bit) input))
        (∀ trial B, result trial = some B → high s C ∧ ∀ z, sat B z = sat C z) ∧
        (high s C → 3 * mSeeds n s ≤ 4 * (Finset.univ.filter
          (fun u : Fin (mSeeds n s) => (result u).isSome = true)).card) := by
  intro n s hs hsn
  obtain ⟨cal, hcal⟩ := exists_strength4_pool n
  obtain ⟨row, hrow⟩ := exists_good_row hs hsn
  refine ⟨cal, row, myReport n s cal row, ?_⟩
  intro C
  let H := posHull cal (fun slot => sat C (cal slot))
  by_cases hlit : ∃ l : Lit n, IsLitHalf H l
  · let l := Classical.choose hlit
    have hlH : IsLitHalf H l := Classical.choose_spec hlit
    have hlC : IsLitHalf C l := (isLitHalf_hull_iff hcal C l).mp hlH
    constructor
    · intro trial B hB
      unfold myReport at hB
      dsimp only at hB
      rw [dif_pos hlit] at hB
      unfold myReportCase2 at hB
      split_ifs at hB with hPos
      dsimp only at hB
      split_ifs at hB with hcert
      · simp only [Option.some.injEq] at hB
        subst hB
        let ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool :=
          fun block input => sat C (reportWord row trial block input)
        let Pos := reportPos n s row trial l ans2
        let p0 := Classical.choose hPos
        have hp0 : p0 ∈ Pos := Classical.choose_spec hPos
        let w0 := reportWord row trial p0.1 p0.2
        have hw0i : w0 l.1 = !l.2 := (Finset.mem_filter.mp hp0).2.1
        have hw0sat : sat C w0 = true := (Finset.mem_filter.mp hp0).2.2
        let K := forcedSet C l.1 w0
        let S := reportS n s trial l w0 row Pos
        have hK_sub_S : K ⊆ S := by
          intro k hk
          have hki : k ≠ l.1 := (mem_forcedSet_iff hlC hw0i hw0sat k).mp hk |>.1
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩, ?_⟩
          intro p hp
          have hpi : reportWord row trial p.1 p.2 l.1 = !l.2 := (Finset.mem_filter.mp hp).2.1
          have hpsat : sat C (reportWord row trial p.1 p.2) = true := (Finset.mem_filter.mp hp).2.2
          exact (sat_opposite_iff hlC hw0i hw0sat (reportWord row trial p.1 p.2) hpi).mp hpsat k hk
        have hS_sub_K : S ⊆ K := by
          intro j hj
          obtain ⟨q, hqsat, hqi, hqmatch⟩ := hcert.2 j hj
          by_contra hjK
          have hallK : ∀ k ∈ K, reportWord row trial q.1 q.2 k = w0 k := by
            intro k hk
            exact hqmatch k (hK_sub_S hk) (fun heq => hjK (heq ▸ hk))
          have htrue : sat C (reportWord row trial q.1 q.2) = true :=
            (sat_opposite_iff hlC hw0i hw0sat (reportWord row trial q.1 q.2) hqi).mpr hallK
          change sat C (reportWord row trial q.1 q.2) = false at hqsat
          rw [htrue] at hqsat
          simp at hqsat
        have hSK : S = K := Finset.Subset.antisymm hS_sub_K hK_sub_S
        have hK_le : K.card ≤ s - 1 := by
          rw [← hSK]
          exact hcert.1
        exact ⟨(high_iff_card_forcedSet hs hsn hlC hw0i hw0sat).mpr hK_le,
          sat_mkBranchFormulaS hlC hw0i hw0sat S hSK⟩
    · intro hhighC
      obtain ⟨w0, hw0i, hw0sat⟩ := exists_opposite_witness_of_high hs hsn hhighC l
      let K := forcedSet C l.1 w0
      have hK_le : K.card ≤ s - 1 := (high_iff_card_forcedSet hs hsn hlC hw0i hw0sat).mp hhighC
      let p : Desc n := (l, fun j => if j ∈ K then some (w0 j) else none)
      have hKOf : KOf p = K := by
        ext j
        simp only [KOf, p, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hj <;> simp [hj]
      have hlK : l.1 ∉ K := by simp [K, forcedSet]
      have hp_good : p ∈ goodStars n s := by
        simp only [goodStars, Finset.mem_filter, Finset.mem_univ, true_and, hKOf, p]
        exact ⟨hK_le, if_neg hlK⟩
      have hgood_seeds := hrow p hp_good
      refine le_trans hgood_seeds (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      have hnotC : row u ∉ FailCenter n s p := fun h => hu (Finset.mem_union_left _ h)
      simp only [FailCenter, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hnotC
      obtain ⟨b0, hb0⟩ := hnotC
      rw [hKOf] at hb0
      have hnotB : ∀ j ∈ Finset.univ.filter (fun j : Fin n => j ∉ insert l.1 K),
          ∃ b : Fin (tBlocks n s), GoodSet (insert j (insert l.1 K)) (row u b) := by
        intro j hj
        have hj' : j ∈ Finset.univ.filter (fun j : Fin n => j ∉ insert p.1.1 (KOf p)) := by
          simpa [p, hKOf] using hj
        have hnot := fun h => hu (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj', h⟩))
        simp only [FailBit, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        simpa [p, hKOf] using hnot
      let ans2 : Fin (tBlocks n s) → Vec (s + 2) → Bool :=
        fun block input => sat C (reportWord row u block input)
      let Pos := reportPos n s row u l ans2
      have hPos : Pos.Nonempty := by
        obtain ⟨inp0, hinp0⟩ := surj_of_goodSet hb0 (fun x => w0 x.1)
        have hi0 : reportWord row u b0 inp0 l.1 = !l.2 := by
          have h1 := hinp0 ⟨l.1, Finset.mem_insert_self _ _⟩
          simpa [reportWord, hw0i] using h1
        have hsat0 : ans2 b0 inp0 = true := by
          change sat C (reportWord row u b0 inp0) = true
          rw [sat_opposite_iff hlC hw0i hw0sat _ hi0]
          intro k hk
          exact hinp0 ⟨k, Finset.mem_insert_of_mem hk⟩
        exact ⟨(b0, inp0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hsat0⟩⟩
      let p0 := Classical.choose hPos
      have hp0 : p0 ∈ Pos := Classical.choose_spec hPos
      let w_pick := reportWord row u p0.1 p0.2
      have hwp_i : w_pick l.1 = !l.2 := (Finset.mem_filter.mp hp0).2.1
      have hwp_sat : sat C w_pick = true := (Finset.mem_filter.mp hp0).2.2
      have hwp_K : ∀ k ∈ K, w_pick k = w0 k :=
        (sat_opposite_iff hlC hw0i hw0sat w_pick hwp_i).mp hwp_sat
      let S := reportS n s u l w_pick row Pos
      have hSK : S = K := by
        ext j
        constructor
        · intro hj
          by_contra hjK
          have hji : j ≠ l.1 := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
          have hjFree : j ∈ Finset.univ.filter (fun x : Fin n => x ∉ insert l.1 K) := by
            simp [hji, hjK]
          obtain ⟨bj, hbj⟩ := hnotB j hjFree
          obtain ⟨inpT, hinpT⟩ := surj_of_goodSet hbj (fun x => if x.1 = j then true else w0 x.1)
          obtain ⟨inpF, hinpF⟩ := surj_of_goodSet hbj (fun x => if x.1 = j then false else w0 x.1)
          have hmemT : (bj, inpT) ∈ Pos := by
            have hT_i : reportWord row u bj inpT l.1 = !l.2 := by
              have h1' := hinpT ⟨l.1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
              simpa [reportWord, hji.symm, hw0i] using h1'
            have hT_sat : ans2 bj inpT = true := by
              change sat C (reportWord row u bj inpT) = true
              rw [sat_opposite_iff hlC hw0i hw0sat _ hT_i]
              intro k hk
              have hkj : k ≠ j := fun heq => hjK (heq ▸ hk)
              have h1' := hinpT ⟨k, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)⟩
              simpa [reportWord, hkj] using h1'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT_i, hT_sat⟩
          have hmemF : (bj, inpF) ∈ Pos := by
            have hF_i : reportWord row u bj inpF l.1 = !l.2 := by
              have h1' := hinpF ⟨l.1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
              simpa [reportWord, hji.symm, hw0i] using h1'
            have hF_sat : ans2 bj inpF = true := by
              change sat C (reportWord row u bj inpF) = true
              rw [sat_opposite_iff hlC hw0i hw0sat _ hF_i]
              intro k hk
              have hkj : k ≠ j := fun heq => hjK (heq ▸ hk)
              have h1' := hinpF ⟨k, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)⟩
              simpa [reportWord, hkj] using h1'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF_i, hF_sat⟩
          have h1' := (Finset.mem_filter.mp hj).2 (bj, inpT) hmemT
          have h2' := (Finset.mem_filter.mp hj).2 (bj, inpF) hmemF
          have hvalT : reportWord row u bj inpT j = true := by
            simpa [reportWord] using hinpT ⟨j, Finset.mem_insert_self _ _⟩
          have hvalF : reportWord row u bj inpF j = false := by
            simpa [reportWord] using hinpF ⟨j, Finset.mem_insert_self _ _⟩
          rw [hvalT] at h1'
          rw [hvalF] at h2'
          rw [← h1'] at h2'
          simp at h2'
        · intro hjK
          have hji : j ≠ l.1 := fun heq => hlK (heq ▸ hjK)
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, ?_⟩
          intro pr hpr
          have hpi : reportWord row u pr.1 pr.2 l.1 = !l.2 := (Finset.mem_filter.mp hpr).2.1
          have hpsat : sat C (reportWord row u pr.1 pr.2) = true := (Finset.mem_filter.mp hpr).2.2
          rw [(sat_opposite_iff hlC hw0i hw0sat _ hpi).mp hpsat j hjK, hwp_K j hjK]
      have hcert : S.card ≤ s - 1 ∧ ∀ j ∈ S, ∃ q : Fin (tBlocks n s) × Vec (s + 2),
          ans2 q.1 q.2 = false ∧ reportWord row u q.1 q.2 l.1 = !l.2 ∧
          ∀ k ∈ S, k ≠ j → reportWord row u q.1 q.2 k = w_pick k := by
        refine ⟨by rw [hSK]; exact hK_le, ?_⟩
        intro j hjS
        have hjK : j ∈ K := hSK ▸ hjS
        have hji : j ≠ l.1 := fun heq => hlK (heq ▸ hjK)
        obtain ⟨inpN, hinpN⟩ := surj_of_goodSet hb0 (fun x => if x.1 = j then !(w0 j) else w0 x.1)
        refine ⟨(b0, inpN), ?_, ?_, ?_⟩
        · change sat C (reportWord row u b0 inpN) = false
          by_contra hnt
          have hsatN : sat C (reportWord row u b0 inpN) = true := by
            cases h : sat C (reportWord row u b0 inpN) <;> simp_all
          have hNi : reportWord row u b0 inpN l.1 = !l.2 := by
            have h1' := hinpN ⟨l.1, Finset.mem_insert_self _ _⟩
            simpa [reportWord, hji.symm, hw0i] using h1'
          have hNj := (sat_opposite_iff hlC hw0i hw0sat _ hNi).mp hsatN j hjK
          have hflip : reportWord row u b0 inpN j = !(w0 j) := by
            simpa [reportWord] using hinpN ⟨j, Finset.mem_insert_of_mem hjK⟩
          rw [hNj] at hflip
          cases w0 j <;> simp at hflip
        · have h1' := hinpN ⟨l.1, Finset.mem_insert_self _ _⟩
          simpa [reportWord, hji.symm, hw0i] using h1'
        · intro k hkS hkj
          have hkK : k ∈ K := hSK ▸ hkS
          have h1' := hinpN ⟨k, Finset.mem_insert_of_mem hkK⟩
          have h1'' : reportWord row u b0 inpN k = w0 k := by simpa [reportWord, hkj] using h1'
          rw [h1'', hwp_K k hkK]
      have hrep : myReport n s cal row u (fun slot => sat C (cal slot)) ans2 =
          myReportCase2 n s row u l ans2 := by
        unfold myReport
        dsimp only
        rw [dif_pos hlit]
      change (myReport n s cal row u (fun slot => sat C (cal slot)) ans2).isSome = true
      rw [hrep]
      exact myReportCase2_isSome hPos hcert
  · have hnoH : ∀ l : Lit n, ¬ IsLitHalf H l := fun l hl => hlit ⟨l, hl⟩
    constructor
    · intro trial B hB
      unfold myReport at hB
      dsimp only at hB
      rw [dif_neg hlit] at hB
      split_ifs at hB with hH
      · simp only [Option.some.injEq] at hB
        subst hB
        have hhighC : high s C := high_of_sol_subset (sat_of_sat_posHull cal C) hH
        exact ⟨hhighC, hull_exact_of_no_litHalf hs hcal C hhighC hnoH (by omega)⟩
    · intro hhighC
      have hexact : ∀ z : W n, sat H z = sat C z :=
        hull_exact_of_no_litHalf hs hcal C hhighC hnoH (by omega)
      have hhighH : high s H := (high_congr hexact).mpr hhighC
      have heq : Finset.univ.filter (fun u : Fin (mSeeds n s) =>
          (myReport n s cal row u (fun slot => sat C (cal slot))
            (fun block input => sat C (fun bit => dotBool (row u block bit) input))).isSome = true) =
          Finset.univ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold myReport
        dsimp only
        rw [dif_neg hlit, if_pos hhighH]
        simp
      rw [heq, Finset.card_univ, Fintype.card_fin]
      omega

end PEqualNP.Outside.L_lib_589

theorem PEqualNP.Outside.L_lib_589 : (∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let high := fun (C : F) =>
    2 ^ n * (2 ^ (s - 1) + 1) ≤
      2 ^ s * (Finset.univ.filter (fun word => sat C word = true)).card
  let L := Nat.clog 2 (n + 1)
  let a := 16 * (1 + 4 * (1 + L))
  let T := 8 + Nat.clog 2 (n - s + 1)
  let M := 2 ^ Nat.clog 2 (4 + (s + 4) * (1 + L))
  let V := Fin (s + 2) → Bool
  ∃ (cal : Fin a → W) (row : Fin M → Fin T → Fin n → V)
    (report : Fin M → (Fin a → Bool) → (Fin T → V → Bool) → Option F),
    ∀ C : F,
      let result := fun seed : Fin M =>
        report seed (fun slot => sat C (cal slot)) (fun block input => sat C (fun bit =>
          (∑ l : Fin (s + 2), ((row seed block bit l) && input l).toNat) % 2 == 1))
      (∀ trial B, result trial = some B → high C ∧ ∀ z, sat B z = sat C z) ∧
      (high C → 3 * M ≤ 4 * (Finset.univ.filter
        (fun u : Fin M => (result u).isSome = true)).card)) :=
  PEqualNP.Outside.L_lib_589.main_thm
