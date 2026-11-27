import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_960_aux
open Finset Matrix

theorem pow_sum {α R : Type*} [DecidableEq α] [CommRing R] (A : Finset α) :
    ∑ S ∈ A.powerset, (-2 : R) ^ S.card = (-1) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : ∑ t ∈ s.powerset, (-2 : R) ^ (insert a t).card
        = ∑ t ∈ s.powerset, (-2 : R) ^ t.card * (-2) :=
      sum_congr rfl (fun t ht => by
        rw [card_insert_of_notMem (fun h => ha (mem_powerset.1 ht h)), pow_succ])
    rw [sum_powerset_insert ha, e, ← sum_mul, ih, card_insert_of_notMem ha]
    ring

theorem par_sum {α R : Type*} [DecidableEq α] [CommRing R] (A : Finset α) :
    ∑ S ∈ A.powerset, (if S = ∅ then 0 else (-2 : R) ^ (S.card - 1)) = ((A.card % 2 : ℕ) : R) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_powerset_insert ha, ih]
    rw [sum_congr rfl (fun t ht => by
      rw [if_neg (Finset.insert_ne_empty a t),
        card_insert_of_notMem (fun h => ha (mem_powerset.1 ht h)), Nat.add_sub_cancel])]
    rw [pow_sum, card_insert_of_notMem ha]
    rcases Nat.even_or_odd s.card with ⟨q, hq⟩ | ⟨q, hq⟩
    · rw [hq]
      have e1 : (q + q) % 2 = 0 := by omega
      have e2 : (q + q + 1) % 2 = 1 := by omega
      rw [e1, e2, show q + q = 2 * q by ring, pow_mul]
      simp
    · rw [hq]
      have e1 : (2 * q + 1) % 2 = 1 := by omega
      have e2 : (2 * q + 1 + 1) % 2 = 0 := by omega
      rw [e1, e2, pow_succ, pow_mul]
      simp

def Pm (r h : ℕ) : Matrix (Finset (Fin r)) (Finset (Fin r)) (ZMod (2 ^ h)) :=
  fun I J => (((I ∩ J).card % 2 : ℕ) : ZMod (2 ^ h))

def Zm (r : ℕ) (R : Type*) [CommRing R] : Matrix (Finset (Fin r)) (Finset (Fin r)) R :=
  fun I S => if S ⊆ I then 1 else 0

def Mu (r : ℕ) (R : Type*) [CommRing R] : Matrix (Finset (Fin r)) (Finset (Fin r)) R :=
  fun S T => if T ⊆ S then (-1) ^ (S \ T).card else 0

def dd {r : ℕ} {R : Type*} [CommRing R] (S : Finset (Fin r)) : R :=
  if S = ∅ then 0 else (-2) ^ (S.card - 1)

theorem P_eq (r h : ℕ) : Pm r h = Zm r _ * diagonal dd * (Zm r _)ᵀ := by
  ext I J
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, transpose_apply]
  have e : ∀ S : Finset (Fin r), Zm r (ZMod (2 ^ h)) I S * dd S * Zm r (ZMod (2 ^ h)) J S
      = if S ∈ (I ∩ J).powerset then dd S else 0 := by
    intro S
    simp only [Zm, mem_powerset, subset_inter_iff]
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun S _ => e S), sum_ite_mem, univ_inter]
  exact (par_sum (I ∩ J)).symm

theorem ZMu (r : ℕ) (R : Type*) [CommRing R] : Zm r R * Mu r R = 1 := by
  ext I T
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hT : T ⊆ I
  · have e : ∀ S : Finset (Fin r), Zm r R I S * Mu r R S T
        = if S ∈ univ.filter (fun S => S ⊆ I ∧ T ⊆ S) then (-1) ^ (S \ T).card else 0 := by
      intro S
      simp only [Zm, Mu, mem_filter, mem_univ, true_and]
      split_ifs <;> simp_all
    rw [sum_congr rfl (fun S _ => e S), sum_ite_mem, univ_inter]
    have e2 : ∑ S ∈ univ.filter (fun S => S ⊆ I ∧ T ⊆ S), ((-1 : R) ^ (S \ T).card)
        = ∑ U ∈ (I \ T).powerset, (-1 : R) ^ U.card := by
      refine sum_nbij' (fun S => S \ T) (fun U => T ∪ U) ?_ ?_ ?_ ?_ ?_
      · intro S hS
        simp only [mem_filter, mem_univ, true_and] at hS
        simp only [mem_powerset]
        exact sdiff_subset_sdiff hS.1 (le_refl T)
      · intro U hU
        simp only [mem_powerset] at hU
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨union_subset hT (hU.trans sdiff_subset), subset_union_left⟩
      · intro S hS
        simp only [mem_filter, mem_univ, true_and] at hS
        exact union_sdiff_of_subset hS.2
      · intro U hU
        simp only [mem_powerset] at hU
        exact union_sdiff_cancel_left (disjoint_of_subset_right hU disjoint_sdiff)
      · intro S _; rfl
    rw [e2]
    have h3 := congrArg (Int.cast : ℤ → R) (sum_powerset_neg_one_pow_card (x := I \ T))
    push_cast at h3
    rw [h3]
    by_cases hIT : I = T
    · subst hIT; simp
    · have : I \ T ≠ ∅ := by
        intro h0
        exact hIT (Subset.antisymm (sdiff_eq_empty_iff_subset.1 h0) hT)
      simp [this, hIT]
  · have hIT : I ≠ T := by rintro rfl; exact hT (Subset.refl _)
    rw [if_neg hIT]
    refine sum_eq_zero (fun S _ => ?_)
    simp only [Zm, Mu]
    split_ifs with h1 h2
    · exact absurd (h2.trans h1) hT
    · simp
    · simp
    · simp

theorem MuZ (r : ℕ) (R : Type*) [CommRing R] : Mu r R * Zm r R = 1 :=
  (mul_eq_one_comm_of_card_eq _ _ _ rfl).mp (ZMu r R)


theorem card_mul_pow (h j : ℕ) :
    (univ.image (fun x : ZMod (2 ^ h) => (2 : ZMod (2 ^ h)) ^ j * x)).card = 2 ^ (h - j) := by
  have : NeZero (2 ^ h) := ⟨by positivity⟩
  by_cases hj : h ≤ j
  · have h0 : (2 : ZMod (2 ^ h)) ^ j = 0 := by
      have : ((2 ^ j : ℕ) : ZMod (2 ^ h)) = ((0 : ℕ) : ZMod (2 ^ h)) :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).2
          (by rw [Nat.zero_mod]; exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hj))
      rw [Nat.cast_zero] at this
      exact_mod_cast this
    simp only [h0, zero_mul]
    rw [Nat.sub_eq_zero_of_le hj, pow_zero, image_const univ_nonempty, card_singleton]
  · have hlt : j < h := by omega
    have e : 2 ^ h = 2 ^ j * 2 ^ (h - j) := by rw [← pow_add]; congr 1; omega
    have himg : univ.image (fun x : ZMod (2 ^ h) => (2 : ZMod (2 ^ h)) ^ j * x)
        = (range (2 ^ (h - j))).image (fun n : ℕ => ((2 ^ j * n : ℕ) : ZMod (2 ^ h))) := by
      ext y
      simp only [mem_image, mem_univ, true_and, mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x.val % 2 ^ (h - j), Nat.mod_lt _ (by positivity), ?_⟩
        conv_rhs => rw [← ZMod.natCast_zmod_val x]
        rw [show (2 : ZMod (2 ^ h)) ^ j * (x.val : ZMod (2 ^ h))
            = ((2 ^ j * x.val : ℕ) : ZMod (2 ^ h)) by push_cast; ring]
        rw [ZMod.natCast_eq_natCast_iff']
        have hm := Nat.mul_mod_mul_left (2 ^ j) x.val (2 ^ (h - j))
        rw [← e] at hm
        rw [hm]
        refine Nat.mod_eq_of_lt ?_
        calc 2 ^ j * (x.val % 2 ^ (h - j)) < 2 ^ j * 2 ^ (h - j) :=
              (Nat.mul_lt_mul_left (by positivity)).2 (Nat.mod_lt _ (by positivity))
          _ = 2 ^ h := e.symm
      · rintro ⟨n, -, rfl⟩
        exact ⟨n, by push_cast; ring⟩
    rw [himg, card_image_of_injOn, card_range]
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
    have hpos : 0 < 2 ^ j := by positivity
    rw [e, Nat.mod_eq_of_lt ((Nat.mul_lt_mul_left hpos).2 ha),
      Nat.mod_eq_of_lt ((Nat.mul_lt_mul_left hpos).2 hb)] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this

theorem card_dd {r h : ℕ} (S : Finset (Fin r)) :
    (univ.image (fun x : ZMod (2 ^ h) => dd S * x)).card
      = 2 ^ (if S.card = 0 then 0 else h - (S.card - 1)) := by
  by_cases hS : S = ∅
  · subst hS
    simp only [dd, if_true, zero_mul, card_empty]
    rw [image_const univ_nonempty, card_singleton]; rfl
  · have hc : S.card ≠ 0 := by rwa [Ne, card_eq_zero]
    rw [if_neg hc, ← card_mul_pow h (S.card - 1)]
    congr 1
    ext y
    simp only [mem_image, mem_univ, true_and, dd, if_neg hS]
    have hu : ((-1 : ZMod (2 ^ h)) ^ (S.card - 1)) * (-1) ^ (S.card - 1) = 1 := by
      rw [← mul_pow]; simp
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(-1) ^ (S.card - 1) * x, by rw [neg_pow (2 : ZMod (2 ^ h))]; ring⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(-1) ^ (S.card - 1) * x, ?_⟩
      rw [neg_pow (2 : ZMod (2 ^ h))]
      calc (-1) ^ (S.card - 1) * 2 ^ (S.card - 1) * ((-1) ^ (S.card - 1) * x)
          = ((-1 : ZMod (2 ^ h)) ^ (S.card - 1) * (-1) ^ (S.card - 1)) * (2 ^ (S.card - 1) * x) := by
            ring
        _ = _ := by rw [hu, one_mul]

theorem part1 (r h : ℕ) :
    (univ.image (fun x : Finset (Fin r) → ZMod (2 ^ h) => (Pm r h) *ᵥ x)).card
      = 2 ^ ((Finset.range h).sum (fun k => (h - k) * Nat.choose r (k + 1))) := by
  have hsurj : ∀ y : Finset (Fin r) → ZMod (2 ^ h), ∃ x, (Zm r _)ᵀ *ᵥ x = y := fun y =>
    ⟨(Mu r _)ᵀ *ᵥ y, by rw [mulVec_mulVec, ← transpose_mul, MuZ, transpose_one, one_mulVec]⟩
  have hinj : Function.Injective (fun v : Finset (Fin r) → ZMod (2 ^ h) => Zm r _ *ᵥ v) := by
    intro v w hvw
    have := congrArg (fun u => Mu r _ *ᵥ u) hvw
    simpa only [mulVec_mulVec, MuZ, one_mulVec] using this
  have e1 : univ.image (fun x : Finset (Fin r) → ZMod (2 ^ h) => (Pm r h) *ᵥ x)
      = (univ.image (fun v : Finset (Fin r) → ZMod (2 ^ h) => diagonal dd *ᵥ v)).image
          (fun v => Zm r _ *ᵥ v) := by
    rw [image_image]
    ext y
    simp only [mem_image, mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Zm r _)ᵀ *ᵥ x, by rw [P_eq, ← mulVec_mulVec, ← mulVec_mulVec]⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨x, by rw [P_eq, ← mulVec_mulVec, ← mulVec_mulVec]⟩
  rw [e1, card_image_of_injective _ hinj]
  have e2 : univ.image (fun v : Finset (Fin r) → ZMod (2 ^ h) => diagonal dd *ᵥ v)
      = Fintype.piFinset (fun S => univ.image (fun x : ZMod (2 ^ h) => dd S * x)) := by
    ext w
    simp only [mem_image, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨v, rfl⟩ S
      exact ⟨v S, by rw [mulVec_diagonal]⟩
    · intro hw
      choose v hv using hw
      exact ⟨v, funext fun S => by rw [mulVec_diagonal, hv]⟩
  rw [e2, Fintype.card_piFinset]
  simp_rw [card_dd]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (f := fun m => if m = 0 then 0 else h - (m - 1)),
    card_univ, Fintype.card_fin, Finset.sum_range_succ']
  simp only [smul_eq_mul, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true,
    mul_zero, add_zero]
  have a1 : ∑ m ∈ range r, r.choose (m + 1) * (h - m)
      = ∑ m ∈ range (r + h), (h - m) * r.choose (m + 1) := by
    rw [← Finset.sum_subset (range_subset_range.2 (by omega : r ≤ r + h))]
    · exact sum_congr rfl (fun m _ => mul_comm _ _)
    · intro m _ hm
      simp only [mem_range, not_lt] at hm
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  have a2 : ∑ m ∈ range h, (h - m) * r.choose (m + 1)
      = ∑ m ∈ range (r + h), (h - m) * r.choose (m + 1) := by
    rw [← Finset.sum_subset (range_subset_range.2 (by omega : h ≤ r + h))]
    intro m _ hm
    simp only [mem_range, not_lt] at hm
    rw [Nat.sub_eq_zero_of_le hm, zero_mul]
  rw [a1, a2]


theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem part2 (r h n m : ℕ) (H : Fin n → Fin m → Bool)
    (hB : Matrix.rank (fun i j => ((H i j).toNat : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2)) ≤ r) :
    (univ.image (fun x : Fin m → ZMod (2 ^ h) =>
      (fun i j => ((H i j).toNat : ZMod (2 ^ h)) : Matrix (Fin n) (Fin m) (ZMod (2 ^ h))) *ᵥ x)).card
      ≤ 2 ^ ((Finset.range h).sum (fun k => (h - k) * Nat.choose r (k + 1))) := by
  classical
  set B : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => ((H i j).toNat : ZMod 2) with hBdef
  set A : Matrix (Fin n) (Fin m) (ZMod (2 ^ h)) := fun i j => ((H i j).toNat : ZMod (2 ^ h))
    with hAdef
  set C := LinearMap.range B.mulVecLin with hC
  have hr' : Module.finrank (ZMod 2) C ≤ r := hB
  set r' := Module.finrank (ZMod 2) C with hr'def
  let b := Module.finBasis (ZMod 2) C
  have hmem : ∀ j, (fun i => B i j) ∈ C := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    rw [Matrix.mulVecLin_apply, mulVec_single_one]
    rfl
  let L : Fin n → Fin r' → ZMod 2 := fun i l => ((b l : C) : Fin n → ZMod 2) i
  let R : Fin r' → Fin m → ZMod 2 := fun l j => b.repr ⟨fun i => B i j, hmem j⟩ l
  have hfac : ∀ i j, B i j = ∑ l, R l j * L i l := by
    intro i j
    have := congrArg (fun v : C => (v : Fin n → ZMod 2) i) (b.sum_repr ⟨fun i => B i j, hmem j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    exact this.symm
  let Si : Fin n → Finset (Fin r') := fun i => univ.filter (fun l => L i l = 1)
  let Tj : Fin m → Finset (Fin r') := fun j => univ.filter (fun l => R l j = 1)
  have hpar : ∀ i j, (H i j).toNat = (Si i ∩ Tj j).card % 2 := by
    intro i j
    have h1 : B i j = (((Si i ∩ Tj j).card : ℕ) : ZMod 2) := by
      rw [hfac]
      have : ∀ l, R l j * L i l = if l ∈ Si i ∩ Tj j then 1 else 0 := by
        intro l
        simp only [Si, Tj, mem_inter, mem_filter, mem_univ, true_and]
        rcases z2 (R l j) with h1 | h1 <;> rcases z2 (L i l) with h2 | h2 <;> simp [h1, h2]
      rw [sum_congr rfl (fun l _ => this l), sum_boole, filter_mem_eq_inter, univ_inter]
    have h2 : (((H i j).toNat : ℕ) : ZMod 2) = (((Si i ∩ Tj j).card : ℕ) : ZMod 2) := h1
    have h3 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2
    rw [Nat.mod_eq_of_lt (Bool.toNat_lt _)] at h3
    exact h3
  have hA : ∀ i j, A i j = Pm r' h (Si i) (Tj j) := by
    intro i j
    simp only [hAdef, Pm, hpar i j]
  have hsub : univ.image (fun x : Fin m → ZMod (2 ^ h) => A *ᵥ x)
      ⊆ (univ.image (fun x : Finset (Fin r') → ZMod (2 ^ h) => (Pm r' h) *ᵥ x)).image
          (fun v i => v (Si i)) := by
    intro w hw
    simp only [mem_image, mem_univ, true_and] at hw ⊢
    obtain ⟨x, rfl⟩ := hw
    refine ⟨(Pm r' h) *ᵥ (fun U => ∑ j ∈ univ.filter (fun j => Tj j = U), x j), ⟨_, rfl⟩, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_fiberwise univ Tj (fun j => A i j * x j)]
    refine sum_congr rfl (fun U _ => sum_congr rfl (fun j hj => ?_))
    rw [hA, (mem_filter.1 hj).2]
  calc _ ≤ ((univ.image (fun x : Finset (Fin r') → ZMod (2 ^ h) => (Pm r' h) *ᵥ x)).image
          (fun v i => v (Si i))).card := card_le_card hsub
    _ ≤ (univ.image (fun x : Finset (Fin r') → ZMod (2 ^ h) => (Pm r' h) *ᵥ x)).card :=
          card_image_le
    _ = _ := part1 r' h
    _ ≤ _ := by
          refine Nat.pow_le_pow_right (by norm_num) (sum_le_sum (fun k _ => ?_))
          exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ hr')

end PEqualNP.Outside.L_lib_960_aux

theorem PEqualNP.Outside.L_lib_960 : (∀ (r h : ℕ),
  let F := (Finset.range h).sum (fun k => (h-k) * Nat.choose r (k+1))
  let P : Matrix (Finset (Fin r)) (Finset (Fin r)) (ZMod (2^h)) :=
    fun I J => (((I ∩ J).card % 2 : ℕ) : ZMod (2^h))
  (Finset.univ.image (fun x : Finset (Fin r) → ZMod (2^h) => P.mulVec x)).card = 2^F ∧
  ∀ (n m : ℕ) (H : Fin n → Fin m → Bool),
    let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => ((H i j).toNat : ZMod 2)
    let A : Matrix (Fin n) (Fin m) (ZMod (2^h)) := fun i j => ((H i j).toNat : ZMod (2^h))
    Matrix.rank B ≤ r →
      (Finset.univ.image (fun x : Fin m → ZMod (2^h) => A.mulVec x)).card ≤ 2^F) := by
  exact fun r h => ⟨PEqualNP.Outside.L_lib_960_aux.part1 r h,
    fun n m H hB => PEqualNP.Outside.L_lib_960_aux.part2 r h n m H hB⟩
