import Mathlib.Tactic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerSeries.Inverse
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_920

open Finset Polynomial

lemma nilpotent_slice {Ring : Type*} [CommRing Ring] (base delta : Ring)
    (degree total red : ℕ) (bounded : red ≤ total) (nil : delta ^ (degree + 1) = 0) :
    (delta + base) ^ red * base ^ (total - red) =
      ∑ order ∈ range (degree + 1), delta ^ order * base ^ (total - order) * red.choose order := by
  rw [add_pow, Finset.sum_mul]
  let term := fun order => delta ^ order * base ^ (total - order) * red.choose order
  have change_range : ∑ order ∈ range (red + 1), term order =
      ∑ order ∈ range (degree + 1), term order := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro order _ outside
      have bound : degree + 1 ≤ order := by simpa using outside
      obtain ⟨more, eqn⟩ := Nat.exists_eq_add_of_le bound
      simp [term, eqn, pow_add, nil]
    · intro order _ outside
      have bound : red < order := by simpa using outside
      simp [term, Nat.choose_eq_zero_of_lt bound]
    · intro order _ _; rfl
  rw [← change_range]
  refine Finset.sum_congr rfl fun order member => ?_
  have exp : red - order + (total - red) = total - order := by
    have := Finset.mem_range.mp member
    omega
  simp only [term, ← exp, pow_add]
  ring

lemma slice_transport {Ring : Type*} [CommRing Ring] (base delta : Ring)
    (degree total : ℕ) (points : Finset ℕ) (weight : ℕ → ℤ)
    (bounded : ∀ red ∈ points, red ≤ total) (nil : delta ^ (degree + 1) = 0)
    (moments : ∀ order ≤ degree, ∑ point ∈ points, weight point * point.choose order = 0) :
    ∑ red ∈ points, (weight red : Ring) * ((delta + base) ^ red * base ^ (total - red)) = 0 := by
  trans ∑ red ∈ points, ∑ order ∈ range (degree + 1),
    (delta ^ order * base ^ (total - order)) * ((weight red : Ring) * red.choose order)
  · refine Finset.sum_congr rfl fun red member => ?_
    rw [nilpotent_slice base delta degree total red (bounded red member) nil, Finset.mul_sum]
    exact Finset.sum_congr rfl fun order _ => by ring
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun order member => ?_
  rw [← Finset.mul_sum]
  have hz := congrArg (fun number : ℤ => (number : Ring)) (moments order (by
    have := Finset.mem_range.mp member; omega))
  push_cast at hz
  rw [hz, mul_zero]

lemma choose_step (point order : ℕ) :
    ((point : ℤ) - order) * point.choose order =
      (order + 1 : ℤ) * point.choose (order + 1) := by
  by_cases bound : order ≤ point
  · have eqn := congrArg (fun k : ℕ => (k : ℤ)) (Nat.choose_succ_right_eq point order)
    push_cast [Nat.cast_sub bound] at eqn
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : point < order),
      Nat.choose_eq_zero_of_lt (by omega : point < order + 1)]
    simp

lemma sparse_moments (points : Finset ℕ) (weight : ℕ → ℤ)
    (moments : ∀ order < points.card,
      ∑ point ∈ points, weight point * point.choose order = 0) :
    ∀ point ∈ points, weight point = 0 := by
  classical
  induction points using Finset.induction_on generalizing weight with
  | empty => simp
  | insert pivot tail fresh ih =>
    let reduced := fun point : ℕ => weight point * ((point : ℤ) - pivot)
    have tail_zero : ∀ point ∈ tail, reduced point = 0 := by
      apply ih
      intro order bound
      have lift : ∀ point, reduced point * point.choose order =
          (order + 1 : ℤ) * (weight point * point.choose (order + 1)) +
          ((order : ℤ) - pivot) * (weight point * point.choose order) := by
        intro point
        dsimp [reduced]
        linear_combination weight point * choose_step point order
      have all_zero : ∑ point ∈ insert pivot tail, reduced point * point.choose order = 0 := by
        simp_rw [lift]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          moments (order + 1) (by simpa [Finset.card_insert_of_notMem fresh] using bound),
          moments order (by rw [Finset.card_insert_of_notMem fresh]; omega)]
        ring
      simpa [Finset.sum_insert fresh, reduced] using all_zero
    have weights_zero : ∀ point ∈ tail, weight point = 0 := by
      intro point member
      have neq : point ≠ pivot := fun eqn => fresh (eqn ▸ member)
      exact (mul_eq_zero.mp (tail_zero point member)).resolve_right
        (sub_ne_zero.mpr (by exact_mod_cast neq))
    have base := moments 0 (by simp [fresh])
    simp [Finset.sum_insert fresh, Finset.sum_eq_zero weights_zero] at base
    intro point member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact base
    · exact weights_zero point member

abbrev Jet (degree : ℕ) := AdjoinRoot ((X : ℚ[X]) ^ (degree + 1))

noncomputable def jetBase (degree : ℕ) : Jet degree := 1 + AdjoinRoot.root ((X : ℚ[X]) ^ (degree + 1))

lemma jet_sparse (degree : ℕ) (points : Finset ℕ) (width : points.card ≤ degree + 1)
    (weight : ℕ → ℤ) (vanishes : ∑ red ∈ points, (weight red : Jet degree) * jetBase degree ^ red = 0) :
    ∀ red ∈ points, weight red = 0 := by
  have converted : AdjoinRoot.mk ((X : ℚ[X]) ^ (degree + 1))
      (∑ red ∈ points, C (weight red : ℚ) * (1 + X) ^ red) = 0 := by
    simpa [jetBase, ← Polynomial.algebraMap_apply, AdjoinRoot.algebraMap_eq] using vanishes
  apply sparse_moments points weight
  intro order bound
  have coeff_zero := Polynomial.X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_zero.mp converted) order (by omega)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow] at coeff_zero
  exact_mod_cast coeff_zero

def First {Ring : Type*} [CommRing Ring] (length : ℕ) (coefficient : Ring) (poly : Ring[X]) : Prop :=
  X ^ (length + 1) ∣ poly - 1 - C coefficient * X ^ length

lemma first_mul {Ring : Type*} [CommRing Ring] {length : ℕ} (positive : 0 < length)
    {left right : Ring[X]} {a b : Ring} (ha : First length a left) (hb : First length b right) :
    First length (a + b) (left * right) := by
  obtain ⟨lp, lcert⟩ := ha
  obtain ⟨rp, rcert⟩ := hb
  obtain ⟨n, rfl⟩ : ∃ n, length = n + 1 := ⟨length - 1, by omega⟩
  refine ⟨lp * right + (1 + C a * X ^ (n + 1)) * rp + C a * C b * X ^ n, ?_⟩
  rw [C_add]
  linear_combination right * lcert + (1 + C a * X ^ (n + 1)) * rcert

lemma first_prod {Ring Index : Type*} [CommRing Ring] {length : ℕ} (positive : 0 < length)
    (indices : Finset Index) (factor : Index → Ring[X]) (coefficient : Index → Ring)
    (cert : ∀ idx ∈ indices, First length (coefficient idx) (factor idx)) :
    First length (∑ idx ∈ indices, coefficient idx) (∏ idx ∈ indices, factor idx) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [First]
  | insert idx tail fresh ih =>
    rw [Finset.sum_insert fresh, Finset.prod_insert fresh]
    exact first_mul positive (cert idx (by simp)) (ih fun j hj => cert j (by simp [hj]))

lemma first_unique {Ring : Type*} [CommRing Ring] {length : ℕ} {left right : Ring} {poly : Ring[X]}
    (hl : First length left poly) (hr : First length right poly) : left = right := by
  have key := Polynomial.X_pow_dvd_iff.mp (dvd_sub hl hr) length (by omega)
  exact (sub_eq_zero.mp (by simpa [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow] using key : right - left = 0)).symm

lemma first_factor {Ring : Type*} [CommRing Ring] {length size : ℕ}
    (bound : length ≤ size) (coeff : Ring) :
    First length (if size = length then coeff else 0) (1 + C coeff * X ^ size) := by
  by_cases same : size = length
  · simp [First, same]
  · have decomp : size = (length + 1) + (size - (length + 1)) := by omega
    simp only [First, ite_eq_right same, map_zero, zero_mul, sub_zero, add_sub_cancel_left]
    refine ⟨C coeff * X ^ (size - (length + 1)), ?_⟩
    conv_lhs => rw [decomp, pow_add]
    ring

lemma first_pow {Ring : Type*} [CommRing Ring] {length : ℕ} (positive : 0 < length)
    {poly : Ring[X]} {coeff : Ring} (cert : First length coeff poly) (multiplicity : ℕ) :
    First length (multiplicity * coeff) (poly ^ multiplicity) := by
  induction multiplicity with
  | zero => simp [First]
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact first_mul positive ih cert

lemma cancel_unit_constant {Ring : Type*} [CommRing Ring] {p q r : Ring[X]}
    (hp : p.coeff 0 = 1) (eqn : p * q = p * r) : q = r := by
  apply Polynomial.coe_injective Ring
  have unit : IsUnit (p : PowerSeries Ring) := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    simpa using (hp ▸ isUnit_one : IsUnit (p.coeff 0)))
  apply unit.mul_left_cancel
  exact_mod_cast eqn

noncomputable def signedFactor {Ring : Type*} [CommRing Ring] (base : Ring) (key : ℕ × ℕ)
    (plus minus : ℕ) : Ring[X] :=
  (1 + C (base ^ key.2) * X ^ key.1) ^ plus * (1 + C (-(base ^ key.2)) * X ^ key.1) ^ minus

lemma signed_constant {Ring : Type*} [CommRing Ring] (base : Ring) (key : ℕ × ℕ)
    (pos : 0 < key.1) (plus minus : ℕ) : (signedFactor base key plus minus).coeff 0 = 1 := by
  rw [← Polynomial.constantCoeff_apply]
  have zeroX : Polynomial.constantCoeff (X : Ring[X]) = 0 := by simp
  simp only [signedFactor, map_mul, map_add, map_one, map_pow, zeroX, zero_pow (Nat.ne_of_gt pos),
    mul_zero, add_zero, one_pow, one_mul]

lemma signed_first {Ring : Type*} [CommRing Ring] (base : Ring) (key : ℕ × ℕ)
    (length plus minus : ℕ) (pos : 0 < length) (bound : length ≤ key.1) :
    First length (if key.1 = length then ((plus : Ring) - minus) * base ^ key.2 else 0)
      (signedFactor base key plus minus) := by
  have cert := first_mul pos (first_pow pos (first_factor bound (base ^ key.2)) plus)
    (first_pow pos (first_factor bound (-(base ^ key.2))) minus)
  unfold signedFactor
  split_ifs with eqn
  · rw [sub_mul, sub_eq_add_neg]; simpa only [ite_eq_left eqn, mul_neg] using cert
  · simpa [eqn] using cert

lemma recover_factors (degree : ℕ) (keys : Finset (ℕ × ℕ))
    (pos : ∀ k ∈ keys, 0 < k.1) (support : ℕ → Finset ℕ)
    (member : ∀ k ∈ keys, k.2 ∈ support k.1) (width : ∀ n, (support n).card ≤ degree + 1)
    (p q : Bool → ℕ × ℕ → ℕ)
    (resolve : ∀ k ∈ keys, (p false k : ℤ) - q false k = (p true k : ℤ) - q true k →
      p false k = p true k ∧ q false k = q true k)
    (product_eq : ∏ k ∈ keys, signedFactor (jetBase degree) k (p false k) (q false k) =
      ∏ k ∈ keys, signedFactor (jetBase degree) k (p true k) (q true k)) :
    ∀ k ∈ keys, p false k = p true k ∧ q false k = q true k := by
  classical
  let factor := fun side key => signedFactor (jetBase degree) key (p side key) (q side key)
  let diff := fun side key => (p side key : ℤ) - q side key
  change ∏ k ∈ keys, factor false k = ∏ k ∈ keys, factor true k at product_eq
  suffices claim : ∀ length, ∀ k ∈ keys, k.1 = length → p false k = p true k ∧ q false k = q true k by
    exact fun k hk => claim k.1 k hk rfl
  intro length
  induction length using Nat.strong_induction_on with
  | _ length ih =>
    intro key hk hlength
    have hpos : 0 < length := hlength ▸ pos key hk
    let tail := keys.filter (fun k => ¬k.1 < length)
    let low := keys.filter (fun k => k.1 < length)
    have same_low : ∏ k ∈ low, factor false k = ∏ k ∈ low, factor true k := by
      refine Finset.prod_congr rfl fun k h => ?_
      obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp h
      obtain ⟨hplus, hminus⟩ := ih k.1 hlt k hmem rfl
      simp [factor, hplus, hminus]
    have eq_tail : ∏ k ∈ tail, factor false k = ∏ k ∈ tail, factor true k := by
      apply cancel_unit_constant (p := ∏ k ∈ low, factor true k)
      · rw [Polynomial.coeff_zero_prod]
        exact Finset.prod_eq_one fun k h => signed_constant _ _ (pos k (Finset.mem_filter.mp h).1) _ _
      · conv_lhs => rw [← same_low]
        simpa only [low, tail, Finset.prod_filter_mul_prod_filter_not] using product_eq
    let coeff := fun side k => if k.1 = length then (diff side k : Jet degree) * jetBase degree ^ k.2 else 0
    have first (side : Bool) : First length (∑ k ∈ tail, coeff side k) (∏ k ∈ tail, factor side k) := by
      refine first_prod hpos tail _ _ fun k h => ?_
      simpa [factor, coeff, diff] using signed_first (jetBase degree) k length (p side k) (q side k)
        hpos (Nat.le_of_not_gt (Finset.mem_filter.mp h).2)
    have left := first false
    rw [eq_tail] at left
    have heq := first_unique left (first true)
    let vals := (support length).filter (fun red => (length, red) ∈ keys)
    have moved (side : Bool) : ∑ k ∈ tail, coeff side k =
        ∑ red ∈ vals, (diff side (length, red) : Jet degree) * jetBase degree ^ red := by
      change (∑ k ∈ tail, if k.1 = length then _ else 0) = _
      rw [← Finset.sum_filter]
      apply Finset.sum_nbij' Prod.snd (fun red => (length, red))
      · rintro ⟨size, red⟩ hx
        obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨member _ (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).1⟩
      · intro red hr
        simpa [tail] using (Finset.mem_filter.mp hr).2
      · rintro ⟨size, red⟩ h; simp [(Finset.mem_filter.mp h).2.symm]
      · intro red _; rfl
      · rintro ⟨size, red⟩ h; obtain rfl : size = length := (Finset.mem_filter.mp h).2; rfl
    rw [moved, moved] at heq
    have zeros := jet_sparse degree vals ((Finset.card_filter_le ..).trans (width length))
      (fun red => diff false (length, red) - diff true (length, red)) (by
        simpa [Int.cast_sub, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr heq)
    have key_eq : (length, key.2) = key := Prod.ext hlength.symm rfl
    have hval : key.2 ∈ vals := Finset.mem_filter.mpr ⟨hlength ▸ member key hk, key_eq ▸ hk⟩
    apply resolve key hk
    simpa [key_eq, diff, sub_eq_zero] using zeros key.2 hval

def sg {R : Type*} [CommRing R] (b : Bool) : R := if b = true then -1 else 1

lemma wt_eq {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → Bool) (p0 p1 : R) :
    p1 ^ (univ.filter (fun h : Fin n => x h = true)).card *
      p0 ^ (n - (univ.filter (fun h : Fin n => x h = true)).card) =
    ∏ h : Fin n, (if x h = true then p1 else p0) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun h => x h = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (univ.filter (fun h : Fin n => ¬ x h = true)).card =
      n - (univ.filter (fun h : Fin n => x h = true)).card := by omega
  rw [h2]

lemma sum_prod_bool {R : Type*} [CommRing R] {n : ℕ} (F : Fin n → Bool → R) :
    ∑ x : Fin n → Bool, ∏ h, F h (x h) = ∏ h, (F h true + F h false) := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool)) F
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_congr rfl fun i _ => Fintype.sum_bool _

lemma fiber_prod {R : Type*} [CommRing R] {n m : ℕ} (r : Fin n → Fin m) (φ : Fin m → R) :
    ∏ h : Fin n, φ (r h) =
      ∏ i : Fin m, φ i ^ (univ.filter (fun h : Fin n => r h = i)).card := by
  rw [← Finset.prod_fiberwise' univ r φ]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_const _

lemma sc {R : Type*} [CommRing R] {n m : ℕ} (r : Fin n → Fin m) (T : Finset (Fin m)) (p0 p1 : R) :
    ∑ x : Fin n → Bool, (∏ h, (if x h = true then p1 else p0)) *
        ∏ i ∈ T, ∏ h, (if r h = i ∧ x h = true then (-1 : R) else 1) =
      (∏ i ∈ T, (p0 - p1) ^ (univ.filter (fun h : Fin n => r h = i)).card) *
        ∏ i ∈ univ \ T, (p0 + p1) ^ (univ.filter (fun h : Fin n => r h = i)).card := by
  have key : ∀ x : Fin n → Bool, (∏ h, (if x h = true then p1 else p0)) *
        ∏ i ∈ T, ∏ h, (if r h = i ∧ x h = true then (-1 : R) else 1) =
      ∏ h, (fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : R) else 1)) h (x h) := by
    intro x
    rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun h _ => ?_
    by_cases hx : x h = true
    · simp only [hx, and_true]
      rw [Finset.prod_ite_eq]
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => key x, sum_prod_bool (fun (h : Fin n) (b : Bool) =>
    (if b = true then p1 else p0) * (if r h ∈ T ∧ b = true then (-1 : R) else 1))]
  have h2 : ∀ h : Fin n, ((fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : R) else 1)) h true +
      (fun (h : Fin n) (b : Bool) => (if b = true then p1 else p0) *
        (if r h ∈ T ∧ b = true then (-1 : R) else 1)) h false) =
      (fun i => if i ∈ T then p0 - p1 else p0 + p1) (r h) := by
    intro h
    by_cases hT : r h ∈ T <;> simp [hT] <;> ring
  rw [Finset.prod_congr rfl fun h _ => h2 h,
    fiber_prod r (fun i => if i ∈ T then p0 - p1 else p0 + p1),
    ← Finset.prod_sdiff (Finset.subset_univ T), mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]

lemma par {R : Type*} [CommRing R] (c : ℕ) (s : Bool) :
    (1 + sg s * (-1 : R) ^ c) = if c % 2 = s.toNat then 2 else 0 := by
  rcases Nat.even_or_odd c with hc | hc
  · have h2 : c % 2 = 0 := Nat.even_iff.mp hc
    cases s <;> simp [sg, hc.neg_one_pow, h2]; ring
  · have h2 : c % 2 = 1 := Nat.odd_iff.mp hc
    cases s <;> simp [sg, hc.neg_one_pow, h2]; ring

lemma neg_one_pow_card {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (-1 : R) ^ (univ.filter p).card = ∏ h : Fin n, (if p h then (-1 : R) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

abbrev Valid {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (x : (Fin A → Bool) × (Fin B → Bool)) : Prop :=
  ∀ i : Fin m,
    ((univ.filter (fun h : Fin A => red h = i ∧ x.1 h = true)).card +
      (univ.filter (fun h : Fin B => blue h = i ∧ x.2 h = true)).card) % 2 = (s i).toNat

abbrev wt1 {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : ℕ :=
  (univ.filter (fun h : Fin A => x.1 h = true)).card

abbrev wt2 {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : ℕ :=
  (univ.filter (fun h : Fin B => x.2 h = true)).card

theorem ci {R : Type*} [CommRing R] {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (p0 p1 q0 q1 : R) :
    (2 : R) ^ m * ∑ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then
        p1 ^ wt1 x * p0 ^ (A - wt1 x) * (q1 ^ wt2 x * q0 ^ (B - wt2 x)) else 0) =
    ∏ i : Fin m,
      ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card +
        sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) := by
  have hR : ∏ i : Fin m,
      ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card +
        sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) =
      ∑ T ∈ (univ : Finset (Fin m)).powerset,
        (∏ i ∈ T, sg (s i) * ((p0 - p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 - q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card)) *
        ∏ i ∈ univ \ T, ((p0 + p1) ^ (univ.filter (fun h : Fin A => red h = i)).card *
          (q0 + q1) ^ (univ.filter (fun h : Fin B => blue h = i)).card) := by
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun i _ => add_comm _ _
  have hx : ∀ x : (Fin A → Bool) × (Fin B → Bool),
      (2 : R) ^ m * (if Valid red blue s x then
        p1 ^ wt1 x * p0 ^ (A - wt1 x) * (q1 ^ wt2 x * q0 ^ (B - wt2 x)) else 0) =
      ∑ T ∈ (univ : Finset (Fin m)).powerset, (∏ i ∈ T, sg (s i)) *
        (((∏ h, (if x.1 h = true then p1 else p0)) *
          ∏ i ∈ T, ∏ h, (if red h = i ∧ x.1 h = true then (-1 : R) else 1)) *
        ((∏ h, (if x.2 h = true then q1 else q0)) *
          ∏ i ∈ T, ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : R) else 1))) := by
    intro x
    have h1 : (if Valid red blue s x then (2 : R) ^ m else 0) =
        ∏ i : Fin m, (1 + sg (s i) *
          ((∏ h, (if red h = i ∧ x.1 h = true then (-1 : R) else 1)) *
            ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : R) else 1))) := by
      have h3 : ∀ i : Fin m, (1 + sg (s i) *
          ((∏ h, (if red h = i ∧ x.1 h = true then (-1 : R) else 1)) *
            ∏ h, (if blue h = i ∧ x.2 h = true then (-1 : R) else 1))) =
          if ((univ.filter (fun h : Fin A => red h = i ∧ x.1 h = true)).card +
            (univ.filter (fun h : Fin B => blue h = i ∧ x.2 h = true)).card) % 2 = (s i).toNat
          then (2 : R) else 0 := by
        intro i
        rw [← neg_one_pow_card, ← neg_one_pow_card, ← pow_add, par]
      rw [Finset.prod_congr rfl fun i _ => h3 i, Finset.prod_ite_zero]
      simp [Finset.prod_const]
    rw [wt_eq, wt_eq]
    have h4 : (2 : R) ^ m * (if Valid red blue s x then
        (∏ h, (if x.1 h = true then p1 else p0)) * (∏ h, (if x.2 h = true then q1 else q0))
          else 0) =
        ((∏ h, (if x.1 h = true then p1 else p0)) * (∏ h, (if x.2 h = true then q1 else q0))) *
          (if Valid red blue s x then (2 : R) ^ m else 0) := by
      split_ifs <;> ring
    rw [h4, h1, Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hR, Finset.mul_sum, Finset.sum_congr rfl fun x _ => hx x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  dsimp only
  have hsplit := Finset.sum_mul_sum (univ : Finset (Fin A → Bool)) (univ : Finset (Fin B → Bool))
    (fun x => (∏ h, (if x h = true then p1 else p0)) *
      ∏ i ∈ T, ∏ h, (if red h = i ∧ x h = true then (-1 : R) else 1))
    (fun y => (∏ h, (if y h = true then q1 else q0)) *
      ∏ i ∈ T, ∏ h, (if blue h = i ∧ y h = true then (-1 : R) else 1))
  rw [← hsplit, sc, sc]
  simp only [Finset.prod_mul_distrib]
  ring
lemma fib_key {m : ℕ} {R : Type*} [CommRing R] (S : Finset (Fin m)) (key : Fin m → ℕ × ℕ)
    (K : Finset (ℕ × ℕ)) (hK : ∀ i ∈ S, key i ∈ K) (D : ℕ × ℕ → R) :
    ∏ k ∈ K, D k ^ (S.filter (fun i => key i = k)).card = ∏ i ∈ S, D (key i) := by
  rw [← Finset.prod_fiberwise_of_maps_to' hK D]
  exact Finset.prod_congr rfl fun k _ => (Finset.prod_const _).symm

theorem eo {m : ℕ} {R : Type*} [CommRing R] (a b : Fin m → ℕ) (s : Fin m → Bool)
    (K : Finset (ℕ × ℕ))
    (hK : ∀ i : Fin m, ∀ c : ℕ, c = 1 ∨ c = 2 → (c * a i, c * b i) ∈ K)
    (Pm Nm : ℕ → ℕ → R) (hP : ∀ u v, Pm (2 * u) (2 * v) = Pm u v ^ 2)
    (hN : ∀ u v, Nm (2 * u) (2 * v) = Nm u v ^ 2) :
    (∏ i : Fin m, (Pm (a i) (b i) + (if s i = true then -1 else 1) * Nm (a i) (b i))) *
      ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        (univ.filter (fun i : Fin m => s i = false ∧ 1 * a i = k.1 ∧ 1 * b i = k.2)).card =
    ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        ((univ.filter (fun i : Fin m => s i = true ∧ 1 * a i = k.1 ∧ 1 * b i = k.2)).card +
          (univ.filter (fun i : Fin m => s i = false ∧ 2 * a i = k.1 ∧ 2 * b i = k.2)).card) := by
  have hh : ∀ (par : Bool) (c : ℕ), c = 1 ∨ c = 2 →
      ∏ k ∈ K, (Pm k.1 k.2 - Nm k.1 k.2) ^
        (univ.filter (fun i : Fin m => s i = par ∧ c * a i = k.1 ∧ c * b i = k.2)).card =
      ∏ i : Fin m, (if s i = par then (Pm (c * a i) (c * b i) - Nm (c * a i) (c * b i))
        else 1) := by
    intro par c hc
    rw [← Finset.prod_filter,
      ← fib_key (univ.filter (fun i : Fin m => s i = par)) (fun i => (c * a i, c * b i)) K
        (fun i _ => hK i c hc) (fun k => Pm k.1 k.2 - Nm k.1 k.2)]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 2
    ext i
    simp [Finset.mem_filter, Prod.ext_iff]
  simp only [pow_add]
  rw [Finset.prod_mul_distrib, hh false 1 (Or.inl rfl), hh true 1 (Or.inl rfl),
    hh false 2 (Or.inr rfl), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hs : s i <;> simp [hP, hN] <;> ring

lemma ex1 (n : ℕ) (c : ℕ → ℤ)
    (h : ∀ x : ℤ, 2 ≤ x → ∑ u ∈ range (n + 1), c u * x ^ (n - u) = 0) :
    ∀ u ≤ n, c u = 0 := by
  have hp : (∑ u ∈ range (n + 1), C (c u) * X ^ (n - u) : ℤ[X]) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.Ici (2 : ℤ))
    · intro x hx
      simp only [IsRoot.def, eval_finsetSum, eval_mul, eval_C, eval_pow,
        eval_X]
      exact h x hx
    · exact Set.Ici_infinite 2
  intro u hu
  have h1 := congrArg (fun q : ℤ[X] => q.coeff (n - u)) hp
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single u] at h1
  · simpa using h1
  · intro u' hu' hne
    have h2 : n - u ≠ n - u' := by
      have := Finset.mem_range.mp hu'
      omega
    simp [h2]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

lemma ex2 (A B : ℕ) (c : ℕ → ℕ → ℤ)
    (h : ∀ x y : ℤ, 2 ≤ x → 2 ≤ y →
      ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), c u v * (x ^ (A - u) * y ^ (B - v)) = 0) :
    ∀ u ≤ A, ∀ v ≤ B, c u v = 0 := by
  intro u hu v hv
  refine ex1 B (c u) (fun y hy => ?_) v hv
  refine ex1 A (fun u => ∑ v ∈ range (B + 1), c u v * y ^ (B - v)) (fun x hx => ?_) u hu
  rw [← h x y hx hy]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

lemma dpos (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y) (u v : ℕ) (huv : (u, v) ≠ (0, 0)) :
    (x + 1) ^ u * (y + 1) ^ v - (x - 1) ^ u * (y - 1) ^ v ≠ 0 := by
  have hx0 : (0 : ℤ) ≤ x - 1 := by linarith
  have hy0 : (0 : ℤ) ≤ y - 1 := by linarith
  have hxl : x - 1 < x + 1 := by linarith
  have hyl : y - 1 < y + 1 := by linarith
  have h1 : (x - 1) ^ u ≤ (x + 1) ^ u := pow_le_pow_left₀ hx0 hxl.le u
  have h2 : (y - 1) ^ v ≤ (y + 1) ^ v := pow_le_pow_left₀ hy0 hyl.le v
  have hlt : (x - 1) ^ u * (y - 1) ^ v < (x + 1) ^ u * (y + 1) ^ v := by
    by_cases hu : u = 0
    · have hv : v ≠ 0 := by
        intro hv
        exact huv (by rw [hu, hv])
      subst hu
      simpa using pow_lt_pow_left₀ hyl hy0 hv
    · have h3 : (x - 1) ^ u < (x + 1) ^ u := pow_lt_pow_left₀ hxl hx0 hu
      have h4 : (0 : ℤ) < (y + 1) ^ v := by positivity
      have h5 : (0 : ℤ) ≤ (x - 1) ^ u := by positivity
      calc (x - 1) ^ u * (y - 1) ^ v ≤ (x - 1) ^ u * (y + 1) ^ v :=
            mul_le_mul_of_nonneg_left h2 h5
        _ < (x + 1) ^ u * (y + 1) ^ v := mul_lt_mul_of_pos_right h3 h4
  intro h0
  linarith

lemma fiber_sum {n m : ℕ} (r : Fin n → Fin m) :
    ∑ i : Fin m, (univ.filter (fun h : Fin n => r h = i)).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := r) (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin m))) (fun _ _ => Finset.mem_univ _)
  simpa using h.symm

abbrev fc {n m : ℕ} (r : Fin n → Fin m) (i : Fin m) : ℕ :=
  (univ.filter (fun h : Fin n => r h = i)).card

abbrev cnt {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (u v : ℕ) : ℕ :=
  (univ.filter (fun x : (Fin A → Bool) × (Fin B → Bool) =>
    wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x)).card

abbrev hit {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (par : Bool) (c u v : ℕ) : ℕ :=
  (univ.filter (fun i : Fin m => s i = par ∧ c * fc red i = u ∧ c * fc blue i = v)).card

abbrev KK (A B : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2 * A + 1)) ×ˢ (range (2 * B + 1))).erase (0, 0)

lemma fc_le {n m : ℕ} (r : Fin n → Fin m) (i : Fin m) : fc r i ≤ n := by
  have h := Finset.card_filter_le (univ : Finset (Fin n)) (fun h => r h = i)
  simpa using h

lemma wt1_le {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : wt1 x ≤ A := by
  have h := Finset.card_filter_le (univ : Finset (Fin A)) (fun h => x.1 h = true)
  simpa using h

lemma wt2_le {A B : ℕ} (x : (Fin A → Bool) × (Fin B → Bool)) : wt2 x ≤ B := by
  have h := Finset.card_filter_le (univ : Finset (Fin B)) (fun h => x.2 h = true)
  simpa using h

lemma fib {R : Type*} [CommRing R] {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (φ : ℕ → ℕ → R) :
    ∑ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then φ (wt1 x) (wt2 x) else 0) =
    ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red blue s u v : R) * φ u v := by
  have h1 : ∀ u v : ℕ, (cnt red blue s u v : R) * φ u v =
      ∑ x : (Fin A → Bool) × (Fin B → Bool),
        (if wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x then φ u v else 0) := by
    intro u v
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h2 : ∀ x : (Fin A → Bool) × (Fin B → Bool),
      (if Valid red blue s x then φ (wt1 x) (wt2 x) else 0) =
      ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1),
        (if wt1 x = u ∧ wt2 x = v ∧ Valid red blue s x then φ u v else 0) := by
    intro x
    rw [Finset.sum_eq_single (wt1 x), Finset.sum_eq_single (wt2 x)]
    · simp
    · intro v _ hv
      split_ifs with hc
      · exact absurd hc.2.1.symm hv
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (wt2_le x))) hn
    · intro u _ hu
      refine Finset.sum_eq_zero fun v _ => ?_
      split_ifs with hc
      · exact absurd hc.1.symm hu
      · rfl
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (wt1_le x))) hn
  rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => (h1 u v).symm

lemma sideH {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (x y : ℤ) :
    (2 : ℤ) ^ m * ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red blue s u v : ℤ) *
        (x ^ (A - u) * y ^ (B - v)) =
    ∏ i : Fin m, ((x + 1) ^ fc red i * (y + 1) ^ fc blue i +
      (if s i = true then -1 else 1) * ((x - 1) ^ fc red i * (y - 1) ^ fc blue i)) := by
  have h1 := fib red blue s (fun u v => x ^ (A - u) * y ^ (B - v))
  have h2 := ci red blue s x 1 y 1
  simp only [one_pow, one_mul] at h2
  rw [← h1, h2]
  rfl

lemma hKmem {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m)
    (hpos : ∀ i, 0 < fc red i + fc blue i) :
    ∀ i : Fin m, ∀ c : ℕ, c = 1 ∨ c = 2 → (c * fc red i, c * fc blue i) ∈ KK A B := by
  intro i c hc
  have h1 := fc_le red i
  have h2 := fc_le blue i
  have h3 := hpos i
  simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq]
  rcases hc with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> omega

lemma hit_zero {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (hpos : ∀ i, 0 < fc red i + fc blue i) (par : Bool) (c : ℕ) (hc : c = 1 ∨ c = 2)
    (u v : ℕ) (huv : (u, v) ∉ KK A B) : hit red blue s par c u v = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i _ ⟨_, h1, h2⟩
  apply huv
  rw [← h1, ← h2]
  exact hKmem red blue hpos i c hc

lemma cancel_core {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (K : Finset ι) (D : ι → R)
    (P0 P1 : R) (hE0 hO0 hE1 hO1 : ι → ℕ)
    (E0 : P0 * ∏ k ∈ K, D k ^ hE0 k = ∏ k ∈ K, D k ^ hO0 k)
    (E1 : P1 * ∏ k ∈ K, D k ^ hE1 k = ∏ k ∈ K, D k ^ hO1 k) :
    (P0 = P1 → ∏ k ∈ K, D k ^ (hO0 k + hE1 k) = ∏ k ∈ K, D k ^ (hO1 k + hE0 k)) ∧
    ((∀ k ∈ K, D k ≠ 0) → (∀ k ∈ K, hO0 k + hE1 k = hO1 k + hE0 k) → P0 = P1) := by
  have s0 : ∀ γ δ : ι → ℕ, ∏ k ∈ K, D k ^ (γ k + δ k) =
      (∏ k ∈ K, D k ^ γ k) * ∏ k ∈ K, D k ^ δ k := fun γ δ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  constructor
  · intro hP
    rw [s0, s0, ← E0, ← E1, hP]
    ring
  · intro hD hk
    have hne : (∏ k ∈ K, D k ^ hE0 k) * ∏ k ∈ K, D k ^ hE1 k ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hD k hk))
        (Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hD k hk))
    apply mul_right_cancel₀ hne
    have h1 : ∏ k ∈ K, D k ^ (hO0 k + hE1 k) = ∏ k ∈ K, D k ^ (hO1 k + hE0 k) :=
      Finset.prod_congr rfl fun k hk' => by rw [hk k hk']
    rw [s0, s0, ← E0, ← E1] at h1
    linear_combination h1

theorem bwd (A B m0 m1 f0 f1 : ℕ) (red0 : Fin A → Fin m0) (blue0 : Fin B → Fin m0)
    (s0 : Fin m0 → Bool) (red1 : Fin A → Fin m1) (blue1 : Fin B → Fin m1) (s1 : Fin m1 → Bool)
    (hpos0 : ∀ i, 0 < fc red0 i + fc blue0 i) (hpos1 : ∀ i, 0 < fc red1 i + fc blue1 i)
    (hf : f0 + m1 = f1 + m0)
    (hk : ∀ k ∈ KK A B,
      (hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2) +
          hit red1 blue1 s1 false 1 k.1 k.2 =
        (hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2) +
          hit red0 blue0 s0 false 1 k.1 k.2) :
    ∀ u v, 2 ^ f0 * cnt red0 blue0 s0 u v = 2 ^ f1 * cnt red1 blue1 s1 u v := by
  have hbig : ∀ u v : ℕ, ¬ (u ≤ A ∧ v ≤ B) → ∀ (m : ℕ) (red : Fin A → Fin m)
      (blue : Fin B → Fin m) (s : Fin m → Bool), cnt red blue s u v = 0 := by
    intro u v huv m red blue s
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨h1, h2, _⟩
    have h3 := wt1_le x
    have h4 := wt2_le x
    omega
  have key := ex2 A B (fun u v => (2 : ℤ) ^ f0 * (cnt red0 blue0 s0 u v : ℤ) -
      2 ^ f1 * (cnt red1 blue1 s1 u v : ℤ)) (by
    intro x y hx hy
    have e0 := sideH red0 blue0 s0 x y
    have e1 := sideH red1 blue1 s1 x y
    have E0 := eo (R := ℤ) (fun i => fc red0 i) (fun i => fc blue0 i) s0 (KK A B)
      (hKmem red0 blue0 hpos0) (fun u v => (x + 1) ^ u * (y + 1) ^ v)
      (fun u v => (x - 1) ^ u * (y - 1) ^ v) (by intro u v; ring) (by intro u v; ring)
    have E1 := eo (R := ℤ) (fun i => fc red1 i) (fun i => fc blue1 i) s1 (KK A B)
      (hKmem red1 blue1 hpos1) (fun u v => (x + 1) ^ u * (y + 1) ^ v)
      (fun u v => (x - 1) ^ u * (y - 1) ^ v) (by intro u v; ring) (by intro u v; ring)
    have hPi := (cancel_core (KK A B)
      (fun k : ℕ × ℕ => (x + 1) ^ k.1 * (y + 1) ^ k.2 - (x - 1) ^ k.1 * (y - 1) ^ k.2) _ _
      (fun k => hit red0 blue0 s0 false 1 k.1 k.2)
      (fun k => hit red0 blue0 s0 true 1 k.1 k.2 + hit red0 blue0 s0 false 2 k.1 k.2)
      (fun k => hit red1 blue1 s1 false 1 k.1 k.2)
      (fun k => hit red1 blue1 s1 true 1 k.1 k.2 + hit red1 blue1 s1 false 2 k.1 k.2)
      E0 E1).2 (by
        rintro ⟨u, v⟩ hk'
        simp only [KK, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq] at hk'
        exact dpos x y hx hy u v hk'.1) hk
    have epow : (2 : ℤ) ^ f0 * 2 ^ m1 = 2 ^ f1 * 2 ^ m0 := by
      rw [← pow_add, ← pow_add, hf]
    have h2 : (2 : ℤ) ^ m0 * 2 ^ m1 ≠ 0 := by positivity
    apply mul_left_cancel₀ h2
    rw [mul_zero]
    have hsum : ∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1),
        ((2 : ℤ) ^ f0 * (cnt red0 blue0 s0 u v : ℤ) - 2 ^ f1 * (cnt red1 blue1 s1 u v : ℤ)) *
          (x ^ (A - u) * y ^ (B - v)) =
        2 ^ f0 * (∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red0 blue0 s0 u v : ℤ) *
          (x ^ (A - u) * y ^ (B - v))) -
        2 ^ f1 * (∑ u ∈ range (A + 1), ∑ v ∈ range (B + 1), (cnt red1 blue1 s1 u v : ℤ) *
          (x ^ (A - u) * y ^ (B - v))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsum]
    linear_combination (2 ^ m1 * 2 ^ f0) * e0 - (2 ^ m0 * 2 ^ f1) * e1 +
      (2 ^ m1 * 2 ^ f0) * hPi +
      (∏ i : Fin m1, ((x + 1) ^ fc red1 i * (y + 1) ^ fc blue1 i +
        (if s1 i = true then -1 else 1) * ((x - 1) ^ fc red1 i * (y - 1) ^ fc blue1 i))) * epow)
  intro u v
  by_cases huv : u ≤ A ∧ v ≤ B
  · have h1 := key u huv.1 v huv.2
    have h2 : ((2 ^ f0 * cnt red0 blue0 s0 u v : ℕ) : ℤ) =
        ((2 ^ f1 * cnt red1 blue1 s1 u v : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · rw [hbig u v huv, hbig u v huv]
    simp

lemma transformed_hist {R : Type*} [CommRing R] {A B m : ℕ} (red : Fin A → Fin m)
    (blue : Fin B → Fin m) (s : Fin m → Bool) (u v : R) :
    (2 : R) ^ m * ∑ a ∈ range (A + 1), ∑ b ∈ range (B + 1), (cnt red blue s a b : R) *
      ((1 - u) ^ a * (1 + u) ^ (A-a) * ((1 - v) ^ b * (1 + v) ^ (B-b))) =
    2 ^ (A+B) * ∏ i : Fin m, (1 + sg (s i) * (u ^ fc red i * v ^ fc blue i)) := by
  have sum_eq := fib red blue s (fun a b => (1-u)^a * (1+u)^(A-a) * ((1-v)^b * (1+v)^(B-b)))
  rw [← sum_eq, ci red blue s (1+u) (1-u) (1+v) (1-v)]
  have factor (i : Fin m) : (1+u+(1-u))^fc red i * (1+v+(1-v))^fc blue i +
      sg (s i) * ((1+u-(1-u))^fc red i * (1+v-(1-v))^fc blue i) =
      2^(fc red i + fc blue i) * (1 + sg (s i) * (u ^ fc red i * v ^ fc blue i)) := by ring
  rw [Finset.prod_congr rfl fun i _ => factor i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, fiber_sum, fiber_sum]

lemma sum_by_total {R : Type*} [AddCommMonoid R] (A B : ℕ) (term : ℕ → ℕ → R) :
    ∑ u ∈ range (A+1), ∑ v ∈ range (B+1), term u v =
    ∑ L ∈ range (A+B+1), ∑ u ∈ (range (A+1)).filter (fun u => u ≤ L ∧ L-u ≤ B), term u (L-u) := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm (s := range (A+B+1))]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun v => u+v) (fun L => L-u)
  · intro v hv; simp only [mem_range, mem_filter] at *; omega
  · intro L hL; simp only [mem_range, mem_filter] at *; omega
  · intro v _; omega
  · intro L hL; simp only [mem_range, mem_filter] at *; omega
  · intro v _; simp

lemma transport_hist {R : Type*} [CommRing R] (A B d : ℕ) (hist : Bool → ℕ → ℕ → ℕ)
    (outside : ∀ j u v, B < v → hist j u v = 0)
    (moments : ∀ h ≤ d, ∀ L,
      (∑ u ∈ range (A+1), if u ≤ L then u.choose h * hist false u (L-u) else 0) =
      ∑ u ∈ range (A+1), if u ≤ L then u.choose h * hist true u (L-u) else 0)
    (x y : R) (nil : (x-y)^(d+1) = 0) :
    ∑ a ∈ range (A+1), ∑ b ∈ range (B+1), (hist false a b : R) * (x^a * y^b) =
    ∑ a ∈ range (A+1), ∑ b ∈ range (B+1), (hist true a b : R) * (x^a * y^b) := by
  rw [sum_by_total, sum_by_total]
  refine Finset.sum_congr rfl fun L _ => ?_
  let pts := (range (A+1)).filter (fun u => u ≤ L ∧ L-u ≤ B)
  have ms (j : Bool) (h : ℕ) : (∑ u ∈ range (A+1), if u ≤ L then u.choose h * hist j u (L-u) else 0) =
      ∑ u ∈ pts, hist j u (L-u) * u.choose h := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hv : L-u ≤ B
    · simp [hv, Nat.mul_comm]
    · simp [hv, outside j u (L-u) (by omega)]
  have cert := slice_transport y (x-y) d L pts (fun u => (hist false u (L-u) : ℤ) - hist true u (L-u))
    (fun u h => (Finset.mem_filter.mp h).2.1) nil (by
      intro h hh
      have eqn := moments h hh L
      rw [ms, ms] at eqn
      have lifted := congrArg (fun n : ℕ => (n : ℤ)) eqn
      push_cast at lifted
      simpa only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using lifted)
  simpa only [sub_add_cancel, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib,
    sub_eq_zero] using cert

lemma unit_change {R : Type*} [CommRing R] (u v : R) (d : ℕ) (nil : (v-u)^(d+1) = 0)
    (hu : IsUnit (1+u)) (hv : IsUnit (1+v)) :
    ∃ x y : R, x*(1+u) = 1-u ∧ y*(1+v) = 1-v ∧ (x-y)^(d+1) = 0 := by
  obtain ⟨ru, hru⟩ := hu
  obtain ⟨rv, hrv⟩ := hv
  let x := (1-u) * (↑ru⁻¹ : R)
  let y := (1-v) * (↑rv⁻¹ : R)
  have hx : x*(1+u) = 1-u := by rw [← hru]; simp [x, mul_assoc]
  have hy : y*(1+v) = 1-v := by rw [← hrv]; simp [y, mul_assoc]
  refine ⟨x, y, hx, hy, ?_⟩
  have identity : (x-y)*((1+u)*(1+v)) = 2*(v-u) := by
    linear_combination (1+v)*hx - (1+u)*hy
  have powered := congrArg (fun a : R => a^(d+1)) identity
  simp only [mul_pow, nil, mul_zero] at powered
  have leftUnit : IsUnit (1+u) := ⟨ru, hru⟩
  have rightUnit : IsUnit (1+v) := ⟨rv, hrv⟩
  apply ((leftUnit.pow (d+1)).mul (rightUnit.pow (d+1))).mul_right_cancel
  simpa using powered

lemma change_weight {R : Type*} [CommRing R] (u v x y : R)
    (hx : x*(1+u) = 1-u) (hy : y*(1+v) = 1-v) {A B a b : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    (1-u)^a*(1+u)^(A-a)*((1-v)^b*(1+v)^(B-b)) = ((1+u)^A*(1+v)^B)*(x^a*y^b) := by
  have make (z w : R) (n k : ℕ) (le : k ≤ n) (eqn : w*(1+z) = 1-z) :
      (1-z)^k*(1+z)^(n-k) = w^k*(1+z)^n := by
    rw [← eqn, mul_pow, mul_assoc, ← pow_add, Nat.add_sub_of_le le]
  rw [make _ _ _ _ ha hx, make _ _ _ _ hb hy]; ring

lemma scale_change {R : Type*} [CommRing R] {A B m f : ℕ} (red : Fin A → Fin m)
    (blue : Fin B → Fin m) (s : Fin m → Bool) (u v x y : R)
    (hx : x*(1+u) = 1-u) (hy : y*(1+v) = 1-v) :
    (2 : R)^m * (((1+u)^A*(1+v)^B) * ∑ a ∈ range (A+1), ∑ b ∈ range (B+1),
      ((2^f * cnt red blue s a b : ℕ) : R) * (x^a*y^b)) =
    2^f * (2^(A+B)*∏ i, (1 + sg (s i) * (u^fc red i * v^fc blue i))) := by
  rw [← transformed_hist red blue s]
  rw [mul_left_comm ((2:R)^f)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [change_weight u v x y hx hy (by have := mem_range.mp ha; omega) (by have := mem_range.mp hb; omega)]
  push_cast; ring

noncomputable def blockProduct (d : ℕ) {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) : (Jet d)[X] :=
  ∏ i, (1 + sg (s i) * (C (jetBase d ^ a i) * X ^ (a i + b i)))

lemma normalized (A B d : ℕ) (m f : Bool → ℕ)
    (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
    (s : (j : Bool) → Fin (m j) → Bool) (pos : ∀ j i, 0 < fc (red j) i + fc (blue j) i)
    (hist : Bool → ℕ → ℕ → ℕ) (hdef : ∀ j u v, hist j u v = 2^f j * cnt (red j) (blue j) (s j) u v)
    (moments : ∀ h ≤ d, ∀ L,
      (∑ u ∈ range (A+1), if u ≤ L then u.choose h * hist false u (L-u) else 0) =
      ∑ u ∈ range (A+1), if u ≤ L then u.choose h * hist true u (L-u) else 0) :
    f false + m true = f true + m false ∧
      blockProduct d (fc (red false)) (fc (blue false)) (s false) =
      blockProduct d (fc (red true)) (fc (blue true)) (s true) := by
  let base := jetBase d
  let z : PowerSeries (Jet d) := PowerSeries.X
  let v := z
  let u := PowerSeries.C base * z
  have hu : IsUnit (1+u) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [u,z])
  have hv : IsUnit (1+v) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [v,z])
  have nilBase : (1-base)^(d+1) = 0 := by
    have hz := AdjoinRoot.eval₂_root ((X : ℚ[X]) ^ (d+1))
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X] at hz
    have eqn : 1-base = (-1 : Jet d) * AdjoinRoot.root ((X : ℚ[X])^(d+1)) := by simp [base,jetBase]
    rw [eqn, mul_pow, hz, mul_zero]
  have nil : (v-u)^(d+1) = 0 := by
    have eq : v-u = PowerSeries.C (1-base)*z := by simp [v,u,sub_mul]
    rw [eq, mul_pow, ← map_pow, nilBase, map_zero, zero_mul]
  obtain ⟨x,y,hx,hy,nil⟩ := unit_change u v d nil hu hv
  have outside : ∀ j a b, B < b → hist j a b = 0 := by
    intro j a b beyond
    rw [hdef, show cnt (red j) (blue j) (s j) a b = 0 from ?_, mul_zero]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ h
    have := wt2_le t
    omega
  have sumEq := transport_hist A B d hist outside moments x y nil
  simp only [hdef] at sumEq
  let prod := fun j => blockProduct d (fc (red j)) (fc (blue j)) (s j)
  have side (j : Bool) : (2 : PowerSeries (Jet d))^(m j) *
      (((1+u)^A*(1+v)^B) * ∑ a ∈ range (A+1), ∑ b ∈ range (B+1),
      ((2^(f j) * cnt (red j) (blue j) (s j) a b : ℕ) : PowerSeries (Jet d)) * (x^a*y^b)) =
      2^(f j) * (2^(A+B)*(prod j : PowerSeries (Jet d))) := by
    rw [scale_change (red j) (blue j) (s j) u v x y hx hy]
    congr 2
    have coeProd (g : Fin (m j) → (Jet d)[X]) : ((∏ i, g i : (Jet d)[X]) : PowerSeries (Jet d)) =
        ∏ i, ((g i) : PowerSeries (Jet d)) := map_prod Polynomial.coeToPowerSeries.ringHom _ _
    simp only [prod, blockProduct, coeProd, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow, map_pow, pow_add, u,v,z, mul_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hs : s j i <;> simp [sg,base] <;> ring
  have twoUnit : IsUnit (2 : PowerSeries (Jet d)) := by
    have h := (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ (PowerSeries (Jet d)))
    simpa only [map_ofNat] using h
  have hcast : (2 : PowerSeries (Jet d))^(f false + m true) * (prod false : PowerSeries (Jet d)) =
      2^(f true + m false) * (prod true : PowerSeries (Jet d)) := by
    apply (twoUnit.pow (A+B)).mul_left_cancel
    have lf := side false
    rw [sumEq] at lf
    simp only [pow_add] at *
    linear_combination -((2 : PowerSeries (Jet d))^m true)*lf + (2^m false)*(side true)
  have ep : (2 : (Jet d)[X])^(f false + m true)*prod false = 2^(f true + m false)*prod true := by
    apply Polynomial.coe_injective (Jet d)
    have coeTwo : ((2 : (Jet d)[X]) : PowerSeries (Jet d)) = 2 := map_ofNat Polynomial.coeToPowerSeries.ringHom 2
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, coeTwo] using hcast
  have cnt0 (j : Bool) : Polynomial.constantCoeff (prod j) = 1 := by
    simp only [prod, blockProduct, map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have zc : Polynomial.constantCoeff (X : (Jet d)[X]) = 0 := by simp
    simp only [map_add, map_one, map_mul, map_pow, zc, zero_pow (pos j i).ne', mul_zero, add_zero]
  have gon : Jet d →+* ℚ := AdjoinRoot.lift (RingHom.id ℚ) 0 (by simp)
  have fe := congrArg (fun p : (Jet d)[X] => gon (Polynomial.constantCoeff p)) ep
  simp only [map_mul, map_pow, map_ofNat, cnt0, mul_one] at fe
  have hf := Nat.pow_right_injective (le_refl 2) (by exact_mod_cast fe)
  refine ⟨hf, ?_⟩
  rw [hf] at hcast
  exact Polynomial.coe_injective (Jet d) ((twoUnit.pow _).mul_left_cancel hcast)

def encode (key : ℕ × ℕ) : ℕ × ℕ := (key.1+key.2, key.1)

def decode (key : ℕ × ℕ) : ℕ × ℕ := (key.2, key.1-key.2)

lemma decode_encode (key : ℕ × ℕ) : decode (encode key) = key := by simp [encode,decode]

lemma recover_uv (degree : ℕ) (keys : Finset (ℕ × ℕ)) (support : ℕ → Finset ℕ)
    (width : ∀ n, (support n).card ≤ degree+1) (pos : ∀ k ∈ keys, 0 < k.1+k.2)
    (p q : Bool → ℕ × ℕ → ℕ)
    (out : ∀ k ∈ keys, k.1 ∉ support (k.1+k.2) → ∀ j, p j k = 0 ∧ q j k = 0)
    (resolve : ∀ k ∈ keys, (p false k : ℤ)-q false k = (p true k : ℤ)-q true k →
      p false k = p true k ∧ q false k = q true k)
    (eqn : ∏ k ∈ keys, signedFactor (jetBase degree) (encode k) (p false k) (q false k) =
      ∏ k ∈ keys, signedFactor (jetBase degree) (encode k) (p true k) (q true k)) :
    ∀ k ∈ keys, p false k = p true k ∧ q false k = q true k := by
  classical
  let active := keys.filter (fun k => k.1 ∈ support (k.1+k.2))
  let factors := active.image encode
  have transfer (j : Bool) : ∏ k ∈ factors, signedFactor (jetBase degree) k (p j (decode k)) (q j (decode k)) =
      ∏ k ∈ keys, signedFactor (jetBase degree) (encode k) (p j k) (q j k) := by
    rw [show factors = active.image encode from rfl, Finset.prod_image]
    · simp_rw [decode_encode]
      apply Finset.prod_subset (Finset.filter_subset ..)
      intro k hk notin
      have z := out k hk (by simpa [active,hk] using notin) j
      simp [signedFactor,z.1,z.2]
    · intro a _ b _ h; simpa [decode_encode] using congrArg decode h
  have recover := recover_factors degree factors (fun k hk => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk; exact pos a (Finset.mem_filter.mp ha).1)
    support (fun k hk => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk; exact (Finset.mem_filter.mp ha).2)
    width (fun j k => p j (decode k)) (fun j k => q j (decode k)) (fun k hk => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk; simpa [decode_encode] using resolve a (Finset.mem_filter.mp ha).1)
    ((transfer false).trans (eqn.trans (transfer true).symm))
  intro k hk
  by_cases hs : k.1 ∈ support (k.1+k.2)
  · simpa [decode_encode] using recover (encode k) (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk,hs⟩,rfl⟩)
  · have hf := out k hk hs false; have ht := out k hk hs true; omega

noncomputable def atom (d u v : ℕ) : (Jet d)[X] := C (jetBase d ^ u) * X ^ (u+v)

lemma atom_double (d u v : ℕ) : atom d (2*u) (2*v) = atom d u v ^ 2 := by
  simp only [atom,map_pow]; ring

lemma factor_form (d : ℕ) (k : ℕ × ℕ) (p q : ℕ) : signedFactor (jetBase d) (encode k) p q =
    (1+atom d k.1 k.2)^p * (1-atom d k.1 k.2)^q := by simp [encode,signedFactor,atom,sub_eq_add_neg]

lemma block_group (d A B m : ℕ) (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool)
    (pos : ∀ i, 0 < fc red i + fc blue i) :
    (∏ k ∈ KK A B, signedFactor (jetBase d) (encode k) (hit red blue s false 1 k.1 k.2)
      (hit red blue s true 1 k.1 k.2)) = blockProduct d (fc red) (fc blue) s := by
  have parity (par : Bool) (g : ℕ × ℕ → (Jet d)[X]) :
      ∏ k ∈ KK A B, g k ^ hit red blue s par 1 k.1 k.2 = ∏ i ∈ univ.filter (fun i => s i = par),
        g (fc red i, fc blue i) := by
    rw [← fib_key _ _ (KK A B) (fun i _ => by simpa using hKmem red blue pos i 1 (Or.inl rfl)) g]
    refine Finset.prod_congr rfl fun k _ => ?_
    unfold hit
    congr 2
    ext i; simp [Prod.ext_iff]
  simp_rw [factor_form]
  rw [Finset.prod_mul_distrib, parity false (fun k => 1+atom d k.1 k.2),
    parity true (fun k => 1-atom d k.1 k.2), Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hs : s i <;> simp [sg,atom,sub_eq_add_neg]

lemma hit_split {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool) (u v : ℕ) :
    hit red blue s false 1 u v + hit red blue s true 1 u v =
      (univ.filter (fun i : Fin m => fc red i = u ∧ fc blue i = v)).card := by
  let pool := univ.filter (fun i : Fin m => fc red i = u ∧ fc blue i = v)
  have cert := Finset.card_filter_add_card_filter_not (s := pool) (fun i => s i = false)
  unfold hit
  convert cert using 2 <;> congr 1 <;> ext i <;> simp [pool,and_comm]

lemma hit_twice {A B m : ℕ} (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool) (u v : ℕ) :
    hit red blue s false 2 u v = if 2 ∣ u ∧ 2 ∣ v then hit red blue s false 1 (u/2) (v/2) else 0 := by
  split_ifs with divs
  · obtain ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩ := divs
    simp [hit]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi cond
    apply divs
    exact ⟨⟨_,cond.2.1.symm⟩,⟨_,cond.2.2.symm⟩⟩

lemma block_canonical (d A B m : ℕ) (red : Fin A → Fin m) (blue : Fin B → Fin m)
    (s : Fin m → Bool) (pos : ∀ i, 0 < fc red i + fc blue i) :
    blockProduct d (fc red) (fc blue) s * ∏ k ∈ KK A B, (1-atom d k.1 k.2)^hit red blue s false 1 k.1 k.2 =
    ∏ k ∈ KK A B, (1-atom d k.1 k.2)^(hit red blue s true 1 k.1 k.2 + hit red blue s false 2 k.1 k.2) := by
  exact eo (fun i => fc red i) (fun i => fc blue i) s (KK A B) (hKmem red blue pos)
    (fun _ _ => (1 : (Jet d)[X])) (atom d) (by simp) (atom_double d)

lemma signatures (A B d : ℕ) (common : Bool) (m : Bool → ℕ)
    (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
    (s : (j : Bool) → Fin (m j) → Bool) (positive : ∀ j i, 0 < fc (red j) i + fc (blue j) i)
    (shared : common = true → ∀ u v, (univ.filter (fun i => fc (red false) i = u ∧ fc (blue false) i = v)).card =
      (univ.filter (fun i => fc (red true) i = u ∧ fc (blue true) i = v)).card)
    (support : ℕ → Finset ℕ) (member : ∀ j i, fc (red j) i ∈ support (fc (red j) i + fc (blue j) i))
    (dmember : common = false → ∀ j i, s j i = false → 2*fc (red j) i ∈ support (2*(fc (red j) i + fc (blue j) i)))
    (width : ∀ L, (support L).card ≤ d+1)
    (equal : blockProduct d (fc (red false)) (fc (blue false)) (s false) =
      blockProduct d (fc (red true)) (fc (blue true)) (s true)) :
    ∀ k ∈ KK A B, (hit (red false) (blue false) (s false) true 1 k.1 k.2 +
      hit (red false) (blue false) (s false) false 2 k.1 k.2) + hit (red true) (blue true) (s true) false 1 k.1 k.2 =
      (hit (red true) (blue true) (s true) true 1 k.1 k.2 + hit (red true) (blue true) (s true) false 2 k.1 k.2) +
      hit (red false) (blue false) (s false) false 1 k.1 k.2 := by
  classical
  let hits := fun j par c (k : ℕ × ℕ) => hit (red j) (blue j) (s j) par c k.1 k.2
  have posK : ∀ k ∈ KK A B, 0 < k.1+k.2 := by
    rintro ⟨u,v⟩ h; simp [KK] at h; omega
  have outside (k : ℕ × ℕ) (hn : k.1 ∉ support (k.1+k.2)) (j par : Bool) : hits j par 1 k = 0 := by
    rw [show hits j par 1 k = _ from rfl, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i _ ⟨_,hr,hb⟩
    simp only [one_mul] at hr hb
    exact hn (by simpa [← hr,← hb] using member j i)
  cases common with
  | false =>
    let exponent := fun j k => (hits j true 1 k + hits j false 2 k) + hits (!j) false 1 k
    have grouped : ∏ k ∈ KK A B, (1-atom d k.1 k.2)^exponent false k = ∏ k ∈ KK A B, (1-atom d k.1 k.2)^exponent true k := by
      have left := block_canonical d A B _ (red false) (blue false) (s false) (positive false)
      have right := block_canonical d A B _ (red true) (blue true) (s true) (positive true)
      simp only [exponent,hits,pow_add,Finset.prod_mul_distrib] at *
      rw [← left,← right,equal]; change (_ * _) * _ = (_ * _) * _; exact mul_right_comm _ _ _
    have mult := recover_uv d (KK A B) support width posK (fun _ _ => 0) exponent (by
      intro k hk hn j
      have twice : hits j false 2 k = 0 := by
        apply Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
        rintro i _ ⟨hs,hr,hb⟩
        apply hn
        rw [← hr,← hb, ← Nat.mul_add]; exact dmember rfl j i hs
      simp [exponent,twice,outside k hn]) (by intros; omega) (by simpa [factor_form] using grouped)
    exact fun k hk => (mult k hk).2
  | true =>
    have mult := recover_uv d (KK A B) support width posK (fun j => hits j false 1) (fun j => hits j true 1)
      (fun k _ hn j => ⟨outside k hn j false,outside k hn j true⟩) (by
        intro k hk he
        have tot := shared rfl k.1 k.2
        rw [← hit_split (red false) (blue false) (s false), ← hit_split (red true) (blue true) (s true)] at tot
        change hits false false 1 k + hits false true 1 k = hits true false 1 k + hits true true 1 k at tot
        omega) (by simpa only [hits,block_group d A B _ _ _ _ (positive false),block_group d A B _ _ _ _ (positive true)] using equal)
    have allEq (k : ℕ × ℕ) : hits false false 1 k = hits true false 1 k ∧ hits false true 1 k = hits true true 1 k := by
      by_cases hk : k ∈ KK A B
      · exact mult k hk
      · have z (j par : Bool) : hits j par 1 k = 0 := hit_zero (red j) (blue j) (s j) (positive j) par 1 (Or.inl rfl) _ _ (by simpa using hk)
        simp [z]
    intro k _
    have signs := allEq k
    have halves := (allEq (k.1/2,k.2/2)).1
    simp only [hits] at signs halves
    simp only [hit_twice,signs.1,signs.2,halves]

end PEqualNP.Outside.L_lib_920

theorem PEqualNP.Outside.L_lib_920 : (∀ (A B d : ℕ) (common : Bool) (m f : Bool → ℕ)
  (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
  (s : (j : Bool) → Fin (m j) → Bool),
  let a := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin A => red j h = i)).card
  let b := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin B => blue j h = i)).card
  (∀ j i, 0 < a j i + b j i) →
  let X := (Fin A → Bool) × (Fin B → Bool)
  let hist := fun (j : Bool) (u v : ℕ) =>
    2^(f j) * ((Finset.univ : Finset X).filter (fun x =>
      (Finset.univ.filter (fun h : Fin A => x.1 h = true)).card = u ∧
      (Finset.univ.filter (fun h : Fin B => x.2 h = true)).card = v ∧
      ∀ i : Fin (m j),
        ((Finset.univ.filter (fun h : Fin A => red j h = i ∧ x.1 h = true)).card +
         (Finset.univ.filter (fun h : Fin B => blue j h = i ∧ x.2 h = true)).card) % 2 =
        (s j i).toNat)).card
  let count := fun (j : Bool) (u v : ℕ) =>
    (Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ b j i = v)).card
  (common = true → ∀ u v, count false u v = count true u v) →
  let support := fun (L : ℕ) => (Finset.range (L+1)).filter (fun u =>
    ∃ j : Bool, ∃ i : Fin (m j),
      (a j i = u ∧ a j i + b j i = L) ∨
      (common = false ∧ s j i = false ∧ 2*a j i = u ∧ 2*(a j i + b j i) = L))
  (∀ L, (support L).card ≤ d+1) →
  let moment := fun (j : Bool) (h L : ℕ) =>
    ∑ u ∈ Finset.range (A+1), if u ≤ L then Nat.choose u h * hist j u (L-u) else 0
  (∀ u v, hist false u v = hist true u v) ↔
    ∀ h, h ≤ d → ∀ L, moment false h L = moment true h L) := by
  intro A B d common m f red blue s a b positive assignments hist count shared support width moment
  constructor
  · intro equal order _ total
    simp only [moment, equal]
  · intro equal
    have normed := PEqualNP.Outside.L_lib_920.normalized A B d m f red blue s positive hist (by intros; rfl) equal
    apply PEqualNP.Outside.L_lib_920.bwd A B (m false) (m true) (f false) (f true) (red false) (blue false)
      (s false) (red true) (blue true) (s true) (positive false) (positive true) normed.1
    apply PEqualNP.Outside.L_lib_920.signatures A B d common m red blue s positive shared support _ _ width normed.2
    · intro j i
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), j,i,Or.inl ⟨rfl,rfl⟩⟩
    · intro hc j i hs
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), j,i,Or.inr ⟨hc,hs,rfl,rfl⟩⟩
