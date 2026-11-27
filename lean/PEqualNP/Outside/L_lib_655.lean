import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_655

open Finset

theorem bool_ite_ne : ∀ p q : Bool, p ≠ q → (if p then (1 : ZMod 2) else 0) ≠ (if q then 1 else 0) := by
  decide

theorem rows_half {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ZMod 2) (he : e ≠ 0) :
    (univ.filter (fun v : ι → ZMod 2 => dotProduct v e = 0)).card * 2 = Fintype.card (ι → ZMod 2) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp he
  have hk1 : e k = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hk
  have hδ : ∀ v : ι → ZMod 2, dotProduct (v + Pi.single k 1) e = dotProduct v e + 1 := by
    intro v
    rw [add_dotProduct, single_dotProduct, hk1, one_mul]
  have hinv : ∀ v : ι → ZMod 2, v + Pi.single k 1 + Pi.single k 1 = v := by
    intro v
    funext i
    simp only [Pi.add_apply]
    exact (by decide : ∀ a c : ZMod 2, a + c + c = a) _ _
  have hcard : (univ.filter (fun v : ι → ZMod 2 => dotProduct v e = 0)).card
      = (univ.filter (fun v : ι → ZMod 2 => ¬ dotProduct v e = 0)).card := by
    apply Finset.card_nbij' (fun v => v + Pi.single k 1) (fun v => v + Pi.single k 1)
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hδ, hv]
      decide
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hδ]
      exact (by decide : ∀ a : ZMod 2, ¬ a = 0 → a + 1 = 0) _ hv
    · intro v _
      exact hinv v
    · intro v _
      exact hinv v
  rw [mul_two]
  nth_rewrite 2 [hcard]
  rw [card_filter_add_card_filter_not, card_univ]

theorem mats_count {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℕ) (e : ι → ZMod 2) (he : e ≠ 0) :
    (univ.filter (fun M : Fin f → ι → ZMod 2 => ∀ r, dotProduct (M r) e = 0)).card * 2 ^ f
      = Fintype.card (Fin f → ι → ZMod 2) := by
  have h1 : univ.filter (fun M : Fin f → ι → ZMod 2 => ∀ r, dotProduct (M r) e = 0)
      = Fintype.piFinset (fun _ : Fin f => univ.filter (fun v : ι → ZMod 2 => dotProduct v e = 0)) := by
    ext M
    simp [Fintype.mem_piFinset]
  rw [h1, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, ← mul_pow, rows_half e he]
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem block_count (m b w : ℕ) :
    (univ.filter (fun e : Fin m × Fin b → ZMod 2 =>
      (univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0)).card ≤ w)).card ≤ 2 ^ m * (2 ^ b) ^ w := by
  let V : Finset (Fin m) → Finset (Fin m × Fin b → ZMod 2) := fun T =>
    Fintype.piFinset (fun p : Fin m × Fin b => if p.1 ∈ T then (univ : Finset (ZMod 2)) else {0})
  have hsub : univ.filter (fun e : Fin m × Fin b → ZMod 2 =>
      (univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0)).card ≤ w)
      ⊆ (univ.filter (fun T : Finset (Fin m) => T.card ≤ w)).biUnion V := by
    intro e he
    rw [mem_filter] at he
    rw [mem_biUnion]
    refine ⟨univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0), mem_filter.mpr ⟨mem_univ _, he.2⟩, ?_⟩
    show e ∈ Fintype.piFinset (fun p : Fin m × Fin b =>
      if p.1 ∈ univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0) then (univ : Finset (ZMod 2)) else {0})
    rw [Fintype.mem_piFinset]
    rintro ⟨j, i⟩
    by_cases hj : ∃ i' : Fin b, e (j, i') ≠ 0
    · have hjm : j ∈ univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0) :=
        mem_filter.mpr ⟨mem_univ _, hj⟩
      simp only [hjm, if_true, mem_univ]
    · have hjm : j ∉ univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0) :=
        fun h' => hj (mem_filter.mp h').2
      push_neg at hj
      simp only [hjm, if_false, mem_singleton]
      exact hj i
  have hV : ∀ T : Finset (Fin m), T.card ≤ w → (V T).card ≤ (2 ^ b) ^ w := by
    intro T hT
    calc (V T).card = ∏ p : Fin m × Fin b, (if p.1 ∈ T then (univ : Finset (ZMod 2)) else {0}).card :=
          Fintype.card_piFinset _
      _ = ∏ p : Fin m × Fin b, (if p.1 ∈ T then 2 else 1) := by
          apply prod_congr rfl
          intro p _
          by_cases hp : p.1 ∈ T <;> simp [hp, ZMod.card]
      _ = ∏ j : Fin m, ∏ _i : Fin b, (if j ∈ T then 2 else 1) := Fintype.prod_prod_type _
      _ = ∏ j : Fin m, (if j ∈ T then 2 ^ b else 1) := by
          apply prod_congr rfl
          intro j _
          by_cases hj : j ∈ T <;> simp [hj]
      _ = (2 ^ b) ^ T.card := by rw [prod_ite_mem, univ_inter, prod_const]
      _ ≤ (2 ^ b) ^ w := Nat.pow_le_pow_right (by positivity) hT
  calc _ ≤ ((univ.filter (fun T : Finset (Fin m) => T.card ≤ w)).biUnion V).card := card_le_card hsub
    _ ≤ ∑ T ∈ univ.filter (fun T : Finset (Fin m) => T.card ≤ w), (V T).card := card_biUnion_le
    _ ≤ ∑ _T ∈ univ.filter (fun T : Finset (Fin m) => T.card ≤ w), (2 ^ b) ^ w :=
        sum_le_sum (fun T hT => hV T (mem_filter.mp hT).2)
    _ = (univ.filter (fun T : Finset (Fin m) => T.card ≤ w)).card * (2 ^ b) ^ w := by
        rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ m * (2 ^ b) ^ w := by
        apply Nat.mul_le_mul_right
        calc _ ≤ (univ : Finset (Finset (Fin m))).card := card_filter_le _ _
          _ = 2 ^ m := by rw [card_univ, Fintype.card_finset, Fintype.card_fin]

theorem key (m b w f : ℕ) (hf : 2 ^ m * (2 ^ b) ^ w < 2 ^ f) :
    ∃ M : Fin f → (Fin m × Fin b) → ZMod 2, ∀ e : Fin m × Fin b → ZMod 2, e ≠ 0 →
      (univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0)).card ≤ w →
        ∃ r, dotProduct (M r) e ≠ 0 := by
  set S := univ.filter (fun e : Fin m × Fin b → ZMod 2 =>
    e ≠ 0 ∧ (univ.filter (fun j : Fin m => ∃ i : Fin b, e (j, i) ≠ 0)).card ≤ w) with hS
  have hSc : S.card < 2 ^ f := by
    refine lt_of_le_of_lt (le_trans (card_le_card ?_) (block_count m b w)) hf
    intro e he
    rw [hS, mem_filter] at he
    exact mem_filter.mpr ⟨mem_univ _, he.2.2⟩
  by_contra hno
  push_neg at hno
  have h1 : (univ : Finset (Fin f → (Fin m × Fin b) → ZMod 2)).card ≤
      ∑ M : Fin f → (Fin m × Fin b) → ZMod 2, (S.filter (fun e => ∀ r, dotProduct (M r) e = 0)).card := by
    rw [card_eq_sum_ones]
    apply sum_le_sum
    intro M _
    obtain ⟨e, he0, hew, hz⟩ := hno M
    have heS : e ∈ S := by
      rw [hS]
      exact mem_filter.mpr ⟨mem_univ _, he0, hew⟩
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨heS, hz⟩⟩
  have h2 : ∑ M : Fin f → (Fin m × Fin b) → ZMod 2, (S.filter (fun e => ∀ r, dotProduct (M r) e = 0)).card
      = ∑ e ∈ S, (univ.filter (fun M : Fin f → (Fin m × Fin b) → ZMod 2 =>
          ∀ r, dotProduct (M r) e = 0)).card := by
    simp only [card_filter]
    exact sum_comm
  have h3 : (∑ e ∈ S, (univ.filter (fun M : Fin f → (Fin m × Fin b) → ZMod 2 =>
          ∀ r, dotProduct (M r) e = 0)).card) * 2 ^ f
      = S.card * Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) := by
    rw [sum_mul, card_eq_sum_ones S, sum_mul]
    apply sum_congr rfl
    intro e he
    rw [one_mul]
    rw [hS, mem_filter] at he
    exact mats_count f e he.2.1
  have hpos : 0 < Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) := Fintype.card_pos
  rw [card_univ] at h1
  have h4 : Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) * 2 ^ f
      ≤ S.card * Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) := by
    calc Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) * 2 ^ f
        ≤ (∑ M : Fin f → (Fin m × Fin b) → ZMod 2,
            (S.filter (fun e => ∀ r, dotProduct (M r) e = 0)).card) * 2 ^ f :=
          Nat.mul_le_mul_right _ h1
      _ = S.card * Fintype.card (Fin f → (Fin m × Fin b) → ZMod 2) := by rw [h2, h3]
  nlinarith [h4, hSc, hpos]

theorem dist_sq (a c : ℕ) : ((Nat.dist a c : ℕ) : ℤ) ^ 2 = ((a : ℤ) - c) ^ 2 := by
  rcases le_total a c with hac | hac
  · rw [Nat.dist_eq_sub_of_le hac, Nat.cast_sub hac]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hac, Nat.cast_sub hac]

theorem par (a c d e : ℕ) (hs : a + c = d + e) :
    2 * (Nat.dist a e) ^ 2 + 2 * (Nat.dist a d) ^ 2 = (Nat.dist a c) ^ 2 + (Nat.dist d e) ^ 2 := by
  have hz : (2 : ℤ) * ((Nat.dist a e : ℕ) : ℤ) ^ 2 + 2 * ((Nat.dist a d : ℕ) : ℤ) ^ 2
      = ((Nat.dist a c : ℕ) : ℤ) ^ 2 + ((Nat.dist d e : ℕ) : ℤ) ^ 2 := by
    rw [dist_sq, dist_sq, dist_sq, dist_sq]
    have hc : (c : ℤ) = d + e - a := by omega
    rw [hc]
    ring
  exact_mod_cast hz

end PEqualNP.Outside.L_lib_655

theorem PEqualNP.Outside.L_lib_655 : (∀ (m b h : ℕ), 0 < b →
  let Q := 2^b
  let X := Fin m → Fin Q
  let width := m*Q^2 / 2^h + 1
  let distance := fun (x y : X) => ∑ j : Fin m, (Nat.dist (x j).val (y j).val)^2
  let bucket := fun (x y : X) => distance x y / width
  let f := 1+m+b*width
  let vec := fun (x : X) (i : Fin m × Fin b) => if (x i.1).val.testBit i.2.val then
    (1 : ZMod 2) else 0
  (∀ x y : X, bucket x y < 2^h) ∧
    ∃ H : ((Fin m × Fin b) → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      (∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ width →
        H (vec x) ≠ H (vec y)) ∧
      ∀ p q : X × X, p ≠ q → bucket p.1 p.2 = bucket q.1 q.2 →
        (∀ j, (p.1 j).val + (p.2 j).val = (q.1 j).val + (q.2 j).val) →
        H (vec p.1) = H (vec q.1) →
        bucket p.1 q.2 < bucket p.1 p.2 ∧ bucket q.1 p.2 < bucket p.1 p.2) := by
  intro m b h hb Q X width distance bucket f vec
  have hw : 0 < width := Nat.succ_pos _
  have hdle : ∀ x y : X, distance x y ≤ m * Q ^ 2 := by
    intro x y
    show ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2 ≤ m * Q ^ 2
    calc ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2 ≤ ∑ _j : Fin m, Q ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have h1 := (x j).isLt
          have h2 := (y j).isLt
          have h3 : Nat.dist (x j).val (y j).val ≤ Q := by
            unfold Nat.dist
            omega
          exact Nat.pow_le_pow_left h3 2
      _ = m * Q ^ 2 := by simp
  have part1 : ∀ x y : X, bucket x y < 2 ^ h := by
    intro x y
    show distance x y / width < 2 ^ h
    rw [Nat.div_lt_iff_lt_mul hw]
    calc distance x y ≤ m * Q ^ 2 := hdle x y
      _ < 2 ^ h * (m * Q ^ 2 / 2 ^ h + 1) := Nat.lt_mul_div_succ _ (by positivity)
      _ = 2 ^ h * width := rfl
  have hfbig : 2 ^ m * (2 ^ b) ^ width < 2 ^ f := by
    have h0 : 0 < 2 ^ m * (2 ^ b) ^ width := by positivity
    calc 2 ^ m * (2 ^ b) ^ width < 2 * (2 ^ m * (2 ^ b) ^ width) := by linarith
      _ = 2 ^ (1 + m + b * width) := by ring
      _ = 2 ^ f := rfl
  obtain ⟨M, hM⟩ := PEqualNP.Outside.L_lib_655.key m b width f hfbig
  have hHv : ∀ (v : Fin m × Fin b → ZMod 2) (r : Fin f),
      (Matrix.mulVecLin (Matrix.of M) v) r = dotProduct (M r) v := fun _ _ => rfl
  have hsep : ∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ width →
      Matrix.mulVecLin (Matrix.of M) (vec x) ≠ Matrix.mulVecLin (Matrix.of M) (vec y) := by
    intro x y hxy hcard hH
    have he0 : vec x - vec y ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
      have hjv : (x j).val ≠ (y j).val := fun h' => hj (Fin.ext h')
      obtain ⟨i, hi⟩ : ∃ i, (x j).val.testBit i ≠ (y j).val.testBit i := by
        by_contra hcon
        push_neg at hcon
        exact hjv (Nat.eq_of_testBit_eq hcon)
      have hib : i < b := by
        by_contra hib
        push_neg at hib
        have hpow : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hib
        have hxQ : (x j).val < 2 ^ b := (x j).isLt
        have hyQ : (y j).val < 2 ^ b := (y j).isLt
        have hx : (x j).val < 2 ^ i := lt_of_lt_of_le hxQ hpow
        have hy : (y j).val < 2 ^ i := lt_of_lt_of_le hyQ hpow
        exact hi (by rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy])
      have hne : vec x (j, ⟨i, hib⟩) ≠ vec y (j, ⟨i, hib⟩) :=
        PEqualNP.Outside.L_lib_655.bool_ite_ne ((x j).val.testBit i) ((y j).val.testBit i) hi
      intro hzero
      have hz := congrFun hzero (j, ⟨i, hib⟩)
      rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hz
      exact hne hz
    have hsupp : (Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, (vec x - vec y) (j, i) ≠ 0)).card
        ≤ width := by
      refine le_trans (Finset.card_le_card ?_) hcard
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨i, hi⟩ := hj.2
      intro hxj
      apply hi
      have hv : vec x (j, i) = vec y (j, i) := by
        show (if (x j).val.testBit i.val then (1 : ZMod 2) else 0)
          = (if (y j).val.testBit i.val then 1 else 0)
        rw [hxj]
      rw [Pi.sub_apply, hv, sub_self]
    obtain ⟨r, hr⟩ := hM (vec x - vec y) he0 hsupp
    apply hr
    have hHr := congrFun hH r
    rw [hHv, hHv] at hHr
    rw [dotProduct_sub, hHr, sub_self]
  refine ⟨part1, Matrix.mulVecLin (Matrix.of M), hsep, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hpq hB hs hH
  dsimp only at hB hs hH ⊢
  have hxx : x ≠ x' := by
    rintro rfl
    apply hpq
    have hyy : y = y' := by
      funext j
      apply Fin.ext
      have := hs j
      omega
    rw [hyy]
  have hmany : width < (Finset.univ.filter (fun j : Fin m => x j ≠ x' j)).card := by
    by_contra hle
    push_neg at hle
    exact hsep x x' hxx hle hH
  have hsq : (Finset.univ.filter (fun j : Fin m => x j ≠ x' j)).card
      ≤ ∑ j : Fin m, (Nat.dist (x j).val (x' j).val) ^ 2 := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : x j ≠ x' j
    · rw [if_pos hj]
      have hjv : (x j).val ≠ (x' j).val := fun h' => hj (Fin.ext h')
      have hd : 0 < Nat.dist (x j).val (x' j).val := by
        unfold Nat.dist
        omega
      exact Nat.one_le_pow _ _ hd
    · rw [if_neg hj]
      exact Nat.zero_le _
  have hsum : 2 * distance x y' + 2 * ∑ j : Fin m, (Nat.dist (x j).val (x' j).val) ^ 2
      = distance x y + distance x' y' := by
    show 2 * ∑ j : Fin m, (Nat.dist (x j).val (y' j).val) ^ 2
        + 2 * ∑ j : Fin m, (Nat.dist (x j).val (x' j).val) ^ 2
      = ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2
        + ∑ j : Fin m, (Nat.dist (x' j).val (y' j).val) ^ 2
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => PEqualNP.Outside.L_lib_655.par _ _ _ _ (hs j))
  have hswap : distance x' y = distance x y' := by
    show ∑ j : Fin m, (Nat.dist (x' j).val (y j).val) ^ 2
      = ∑ j : Fin m, (Nat.dist (x j).val (y' j).val) ^ 2
    apply Finset.sum_congr rfl
    intro j _
    have hsj := hs j
    have hd : Nat.dist (x' j).val (y j).val = Nat.dist (x j).val (y' j).val := by
      unfold Nat.dist
      omega
    rw [hd]
  have hlt1 : distance x y < width * (bucket x y + 1) := Nat.lt_mul_div_succ _ hw
  have hlt2 : distance x' y' < width * (bucket x y + 1) := by
    rw [hB]
    exact Nat.lt_mul_div_succ _ hw
  have hmain : distance x y' < bucket x y * width := by
    have e1 : width * (bucket x y + 1) = width * bucket x y + width := by ring
    rw [e1] at hlt1 hlt2
    rw [mul_comm]
    omega
  have goal1 : bucket x y' < bucket x y := by
    show distance x y' / width < bucket x y
    rw [Nat.div_lt_iff_lt_mul hw]
    exact hmain
  refine ⟨goal1, ?_⟩
  show distance x' y / width < bucket x y
  rw [hswap]
  exact goal1
