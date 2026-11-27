import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_792_aux

open scoped BigOperators

abbrev Vec (r : ℕ) := Fin r → ZMod 2

def fVal {r : ℕ} (z : ℚ) (a : Vec r) : ℚ :=
  if a = 0 then z - 1 else -1

def TMat {r : ℕ} (z : ℚ) (h : Vec r) : Matrix (Option (Vec r)) (Option (Vec r)) ℚ :=
  fun before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (fVal z a) (fun b => if b = a + h then 1 else 0))

def seriesVal {r : ℕ} (z : ℚ) (w : List (Vec r)) : ℚ :=
  (w.map (TMat z)).prod none none

def Fits (r : ℕ) (z : ℚ) (k : ℕ) (test : List (Vec r) → Prop) : Prop :=
  ∃ (left right : Fin k → ℚ) (M : Vec r → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List (Vec r), test w →
      (∑ i : Fin k, ∑ j : Fin k, left i * (w.map M).prod i j * right j) = seriesVal z w

lemma zmod2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_add, ZMod.val_zero] at hv
    have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    exact ZMod.val_injective 2 (by omega)
  · rintro rfl
    apply ZMod.val_injective 2
    rw [ZMod.val_add, ZMod.val_zero]
    omega

lemma vec_add_eq_zero_iff {r : ℕ} (a b : Vec r) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    exact (zmod2_add_eq_zero_iff (a i) (b i)).mp (congrFun h i)
  · rintro rfl
    funext i
    exact (zmod2_add_eq_zero_iff (a i) (a i)).mpr rfl

lemma card_vec (r : ℕ) : Fintype.card (Vec r) = 2 ^ r := by
  simp [Vec]

lemma sum_fVal {r : ℕ} (z : ℚ) : ∑ a : Vec r, fVal z a = z - (2 ^ r : ℚ) := by
  have h0 : (0 : Vec r) ∈ (Finset.univ : Finset (Vec r)) := Finset.mem_univ 0
  rw [← Finset.add_sum_erase _ _ h0]
  have h1 : fVal z (0 : Vec r) = z - 1 := by simp [fVal]
  have h2 : ∑ a ∈ Finset.univ.erase (0 : Vec r), fVal z a = ((2 ^ r : ℕ) - 1 : ℕ) * (-1 : ℚ) := by
    have heq : ∀ a ∈ Finset.univ.erase (0 : Vec r), fVal z a = (-1 : ℚ) := by
      intro a ha
      have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
      simp [fVal, hne]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_erase_of_mem h0,
      Finset.card_univ, card_vec, nsmul_eq_mul]
  rw [h1, h2]
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [Nat.cast_sub hpos]
  push_cast
  ring

lemma sum_one_sub_fVal {r : ℕ} (z : ℚ) : ∑ a : Vec r, (1 - fVal z a) = 2 * (2 ^ r : ℚ) - z := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul,
    mul_one, sum_fVal]
  push_cast
  ring

lemma list_prod_intertwine {α β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : α → Matrix β β ℚ) (B : α → Matrix γ γ ℚ) (E : Matrix β γ ℚ)
    (hstep : ∀ a : α, A a * E = E * B a) :
    ∀ w : List α, (w.map A).prod * E = E * (w.map B).prod := by
  intro w
  induction w with
  | nil => simp
  | cons a ws ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih, ← Matrix.mul_assoc (A a) E,
      hstep a]

lemma fits_of_intertwine {r k : ℕ} (z : ℚ) {γ : Type*} [Fintype γ] [DecidableEq γ]
    (e : Fin k ≃ γ) (M : Vec r → Matrix γ γ ℚ) (E : Matrix (Option (Vec r)) γ ℚ)
    (c0 : γ)
    (hstep : ∀ h : Vec r, TMat z h * E = E * M h)
    (hcol : ∀ s : Option (Vec r), E s c0 = if s = none then 1 else 0)
    (hrow : ∀ c : γ, E none c = if c = c0 then 1 else 0) :
    Fits r z k (fun _ => True) := by
  let left : Fin k → ℚ := fun i => if e i = c0 then 1 else 0
  let right : Fin k → ℚ := fun j => if e j = c0 then 1 else 0
  let M' : Vec r → Matrix (Fin k) (Fin k) ℚ := fun h => (M h).submatrix e e
  have hprod_sub : ∀ w : List (Vec r), (w.map M').prod = ((w.map M).prod).submatrix e e := by
    intro w
    induction w with
    | nil =>
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
    | cons a ws ih =>
      simp only [List.map_cons, List.prod_cons, ih, M']
      ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply]
      exact e.sum_comp (fun x => M a (e i) x * (ws.map M).prod x (e j))
  refine ⟨left, right, M', ?_⟩
  intro w _
  have hsum : ∑ i : Fin k, ∑ j : Fin k, left i * (w.map M').prod i j * right j =
      (w.map M).prod c0 c0 := by
    rw [Finset.sum_eq_single (e.symm c0)]
    · rw [Finset.sum_eq_single (e.symm c0)]
      · simp [left, right, hprod_sub w, Matrix.submatrix_apply]
      · intro j _ hj
        have hne : e j ≠ c0 := fun h => hj (e.injective (h.trans (e.apply_symm_apply c0).symm))
        simp [right, hne]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · intro i _ hi
      have hne : e i ≠ c0 := fun h => hi (e.injective (h.trans (e.apply_symm_apply c0).symm))
      simp [left, hne]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  rw [hsum]
  have hinter := congrFun (congrFun (list_prod_intertwine (TMat z) M E hstep w) none) c0
  have hlhs : ((w.map (TMat z)).prod * E) none c0 = seriesVal z w := by
    rw [Matrix.mul_apply]
    simp only [hcol, seriesVal]
    rw [Finset.sum_eq_single none]
    · simp
    · intro s _ hs; simp [hs]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hrhs : (E * (w.map M).prod) none c0 = (w.map M).prod c0 c0 := by
    rw [Matrix.mul_apply]
    simp only [hrow]
    rw [Finset.sum_eq_single c0]
    · simp
    · intro c _ hc; simp [hc]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  rw [← hrhs, ← hinter, hlhs]

lemma fits_mono {r k1 k2 : ℕ} (z : ℚ) (hk : k1 ≤ k2) (hfit : Fits r z k1 (fun _ => True)) :
    Fits r z k2 (fun _ => True) := by
  rcases hfit with ⟨left, right, M, hM⟩
  let left' : Fin k2 → ℚ := fun i => if h : i.val < k1 then left ⟨i.val, h⟩ else 0
  let right' : Fin k2 → ℚ := fun j => if h : j.val < k1 then right ⟨j.val, h⟩ else 0
  let M' : Vec r → Matrix (Fin k2) (Fin k2) ℚ := fun a i j =>
    if hi : i.val < k1 then if hj : j.val < k1 then M a ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0
  let emb : Fin k1 ↪ Fin k2 := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hprod : ∀ (w : List (Vec r)) (i j : Fin k1),
      (w.map M').prod (emb i) (emb j) = (w.map M).prod i j := by
    intro w
    induction w with
    | nil =>
      intro i j
      simp [emb, Matrix.one_apply, Fin.ext_iff]
    | cons a ws ih =>
      intro i j
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      calc ∑ x : Fin k2, M' a (emb i) x * (ws.map M').prod x (emb j)
          = ∑ x ∈ Finset.univ.map emb, M' a (emb i) x * (ws.map M').prod x (emb j) := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro x _ hx
            have hxge : ¬ x.val < k1 := by
              intro hlt
              apply hx
              exact Finset.mem_map.mpr ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
            simp [M', emb, i.isLt, hxge]
        _ = ∑ x : Fin k1, M a i x * (ws.map M).prod x j := by
            rw [Finset.sum_map]
            apply Finset.sum_congr rfl
            intro x _
            have hM_eq : M' a (emb i) (emb x) = M a i x := by
              simp [M', emb, i.isLt, x.isLt]
            rw [hM_eq, ih x j]
  refine ⟨left', right', M', ?_⟩
  intro w _
  have hsum_eq :
      ∑ i : Fin k2, ∑ j : Fin k2, left' i * (w.map M').prod i j * right' j =
      ∑ i : Fin k1, ∑ j : Fin k1, left i * (w.map M).prod i j * right j := by
    calc ∑ i : Fin k2, ∑ j : Fin k2, left' i * (w.map M').prod i j * right' j
        = ∑ i ∈ Finset.univ.map emb, ∑ j : Fin k2, left' i * (w.map M').prod i j * right' j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          have hige : ¬ i.val < k1 := by
            intro hlt
            exact hi (Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          simp [left', hige]
      _ = ∑ i : Fin k1, ∑ j : Fin k2, left' (emb i) * (w.map M').prod (emb i) j * right' j := by
          rw [Finset.sum_map]
      _ = ∑ i : Fin k1, ∑ j ∈ Finset.univ.map emb,
            left' (emb i) * (w.map M').prod (emb i) j * right' j := by
          apply Finset.sum_congr rfl
          intro i _
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hjge : ¬ j.val < k1 := by
            intro hlt
            exact hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          simp [right', hjge]
      _ = ∑ i : Fin k1, ∑ j : Fin k1, left i * (w.map M).prod i j * right j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j _
          have hl : left' (emb i) = left i := by simp [left', emb, i.isLt]
          have hr : right' (emb j) = right j := by simp [right', emb, j.isLt]
          rw [hl, hr, hprod w i j]
  rw [hsum_eq]
  exact hM w trivial

lemma fits_general (r : ℕ) (z : ℚ) : Fits r z (2 ^ r + 1) (fun _ => True) := by
  have hcard : Fintype.card (Option (Vec r)) = 2 ^ r + 1 := by
    simp
  let e : Fin (2 ^ r + 1) ≃ Option (Vec r) :=
    (Fintype.equivFinOfCardEq hcard).symm
  exact fits_of_intertwine z e (TMat z) 1 none
    (fun h => by simp)
    (fun s => by simp [Matrix.one_apply])
    (fun c => by simp [Matrix.one_apply, eq_comm])

lemma fits_zero (r : ℕ) : Fits r 0 2 (fun _ => True) := by
  let E : Matrix (Option (Vec r)) (Fin 2) ℚ := fun s j =>
    s.elim (if j = 0 then 1 else 0) (fun _ => if j = 1 then 1 else 0)
  let M : Vec r → Matrix (Fin 2) (Fin 2) ℚ := fun _ => !![1, 1; -1, 1]
  have hstep : ∀ h : Vec r, TMat 0 h * E = E * M h := by
    intro h
    ext s j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_option, Fin.sum_univ_two]
    cases s with
    | none =>
      fin_cases j <;> simp [TMat, E, M]
    | some a =>
      have hfa : fVal 0 a = -1 := by
        unfold fVal
        by_cases ha : a = 0 <;> simp [ha]
      fin_cases j <;> simp [TMat, E, M, hfa]
  exact fits_of_intertwine 0 (Equiv.refl (Fin 2)) M E 0 hstep
    (fun s => by cases s <;> simp [E])
    (fun c => by fin_cases c <;> simp [E])

lemma fits_q (r : ℕ) : Fits r (2 ^ r : ℚ) (2 ^ r) (fun _ => True) := by
  let z : ℚ := (2 ^ r : ℚ)
  let e : Fin (2 ^ r) ≃ Vec r := (Fintype.equivFinOfCardEq (card_vec r)).symm
  let E : Matrix (Option (Vec r)) (Vec r) ℚ := fun s c =>
    s.elim (if c = 0 then 1 else 0)
      (fun a => if c = 0 then 0 else if a = c then 1 else if a = 0 then -1 else 0)
  let P : Matrix (Vec r) (Option (Vec r)) ℚ := fun c s =>
    s.elim (if c = 0 then 1 else 0)
      (fun a => if c = 0 then 0 else if a = c then 1 else 0)
  let M : Vec r → Matrix (Vec r) (Vec r) ℚ := fun h => P * (TMat z h * E)
  have hEP_ker : ∀ v : Option (Vec r) → ℚ, (∑ a : Vec r, v (some a)) = 0 →
      (E * P).mulVec v = v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    have hPv0 : P.mulVec v 0 = v none := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
      simp [P]
    have hPvc : ∀ c : Vec r, c ≠ 0 → P.mulVec v c = v (some c) := by
      intro c hc
      rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
      simp only [P, Option.elim_none, Option.elim_some, hc, ↓reduceIte, zero_mul, zero_add]
      rw [Finset.sum_eq_single c]
      · simp
      · intro a _ hac; simp [hac]
      · intro h; exact False.elim (h (Finset.mem_univ c))
    funext s
    rw [Matrix.mulVec, dotProduct]
    cases s with
    | none =>
      rw [Finset.sum_eq_single (0 : Vec r)]
      · simp only [E, Option.elim_none, ↓reduceIte, one_mul, hPv0]
      · intro c _ hc; simp [E, hc]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    | some a =>
      by_cases ha0 : a = 0
      · subst ha0
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Vec r))]
        have hzero0 : E (some 0) 0 * P.mulVec v 0 = 0 := by simp [E]
        rw [hzero0, zero_add]
        have hsum_er :
            ∑ c ∈ Finset.univ.erase (0 : Vec r), E (some 0) c * P.mulVec v c =
            ∑ c ∈ Finset.univ.erase (0 : Vec r), (-1 : ℚ) * v (some c) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
          have hEc : E (some 0) c = -1 := by simp [E, hc0, Ne.symm hc0]
          rw [hEc, hPvc c hc0]
        rw [hsum_er, ← Finset.mul_sum]
        have htot := Finset.add_sum_erase Finset.univ (fun c : Vec r => v (some c)) (Finset.mem_univ 0)
        linarith
      · rw [Finset.sum_eq_single a]
        · have hEa : E (some a) a = 1 := by simp [E, ha0]
          rw [hEa, one_mul, hPvc a ha0]
        · intro c _ hca
          have hEc : E (some a) c = 0 := by
            by_cases hc0 : c = 0
            · simp [E, hc0]
            · simp [E, hc0, Ne.symm hca, ha0]
          rw [hEc, zero_mul]
        · intro h; exact False.elim (h (Finset.mem_univ a))
  have hcol_ker : ∀ (h : Vec r) (c : Vec r), ∑ a : Vec r, (TMat z h * E) (some a) c = 0 := by
    intro h c
    have hTE : ∀ a : Vec r, (TMat z h * E) (some a) c =
        fVal z a * E none c + E (some (a + h)) c := by
      intro a
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [TMat, Option.elim_some, Option.elim_none]
      congr 1
      rw [Finset.sum_eq_single (a + h)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    simp_rw [hTE, Finset.sum_add_distrib, ← Finset.sum_mul, sum_fVal]
    have hz0 : z - (2 ^ r : ℚ) = 0 := sub_self _
    rw [hz0, zero_mul, zero_add]
    have hshift : ∑ a : Vec r, E (some (a + h)) c = ∑ b : Vec r, E (some b) c := by
      refine Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)
    rw [hshift]
    by_cases hc0 : c = 0
    · simp [E, hc0]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
      have h0mem : (0 : Vec r) ∈ Finset.univ.erase c :=
        Finset.mem_erase.mpr ⟨Ne.symm hc0, Finset.mem_univ 0⟩
      rw [← Finset.add_sum_erase _ _ h0mem]
      have hrest : ∑ b ∈ (Finset.univ.erase c).erase 0, E (some b) c = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
        have hbc : b ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        simp [E, hc0, hbc, hb0]
      rw [hrest, add_zero]
      have hEc : E (some c) c = 1 := by simp [E, hc0]
      have hE0 : E (some 0) c = -1 := by simp [E, hc0, Ne.symm hc0]
      rw [hEc, hE0]
      ring
  have hstep : ∀ h : Vec r, TMat z h * E = E * M h := by
    intro h
    dsimp only [M]
    rw [← Matrix.mul_assoc]
    ext s c
    have hv := congrFun (hEP_ker (fun u => (TMat z h * E) u c) (hcol_ker h c)) s
    have hlhs : ((E * P).mulVec (fun u => (TMat z h * E) u c)) s = ((E * P) * (TMat z h * E)) s c := by
      rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hlhs] at hv
    exact hv.symm
  exact fits_of_intertwine z e M E 0 hstep
    (fun s => by cases s <;> simp [E])
    (fun c => by simp [E])

lemma series_nil {r : ℕ} (z : ℚ) : seriesVal (r := r) z [] = 1 := by
  simp [seriesVal]

lemma series_one {r : ℕ} (z : ℚ) (a : Vec r) : seriesVal z [a] = 1 := by
  simp [seriesVal, TMat]

lemma series_two {r : ℕ} (z : ℚ) (a b : Vec r) : seriesVal z [a, b] = 1 + fVal z a := by
  simp only [seriesVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [Matrix.mul_apply, Fintype.sum_option]
  simp only [TMat, Option.elim_none, Option.elim_some, one_mul]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact False.elim (h (Finset.mem_univ a))

lemma series_three {r : ℕ} (z : ℚ) (a b c : Vec r) :
    seriesVal z [a, b, c] = 1 + fVal z a + fVal z b + fVal z (a + b) := by
  have hmul : (TMat z a * TMat z b) none none = 1 + fVal z a := by
    simpa [seriesVal] using series_two z a b
  have hmul_some : ∀ x : Vec r, (TMat z a * TMat z b) none (some x) =
      (if x = b then 1 else 0) + (if x = a + b then 1 else 0) := by
    intro x
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [TMat, Option.elim_none, Option.elim_some, one_mul]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact False.elim (h (Finset.mem_univ a))
  simp only [seriesVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ← Matrix.mul_assoc]
  rw [Matrix.mul_apply, Fintype.sum_option, hmul]
  simp only [TMat, Option.elim_none, Option.elim_some, mul_one]
  simp_rw [hmul_some, add_mul, Finset.sum_add_distrib]
  have hs1 : ∑ x : Vec r, (if x = b then (1 : ℚ) else 0) * fVal z x = fVal z b := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact False.elim (h (Finset.mem_univ b))
  have hs2 : ∑ x : Vec r, (if x = a + b then (1 : ℚ) else 0) * fVal z x = fVal z (a + b) := by
    rw [Finset.sum_eq_single (a + b)]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact False.elim (h (Finset.mem_univ (a + b)))
  rw [hs1, hs2]
  ring

lemma hankel_rank_le {r k : ℕ} {z : ℚ} {I J : Type*} [Fintype I] [Fintype J]
    (pref : I → List (Vec r)) (suff : J → List (Vec r))
    (hlen : ∀ i j, (pref i ++ suff j).length ≤ 3)
    (hfit : Fits r z k (fun w => w.length ≤ 3)) :
    (Matrix.of (fun i j => seriesVal z (pref i ++ suff j))).rank ≤ k := by
  rcases hfit with ⟨left, right, M, hM⟩
  let U : Matrix I (Fin k) ℚ := fun i a => ∑ b : Fin k, left b * ((pref i).map M).prod b a
  let V : Matrix (Fin k) J ℚ := fun a j => ∑ c : Fin k, ((suff j).map M).prod a c * right c
  have hfac : Matrix.of (fun i j => seriesVal z (pref i ++ suff j)) = U * V := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    dsimp only [U, V]
    rw [← hM (pref i ++ suff j) (hlen i j)]
    simp only [List.map_append, List.prod_append]
    calc ∑ b : Fin k, ∑ c : Fin k,
            left b * (((pref i).map M).prod * ((suff j).map M).prod) b c * right c
        = ∑ b : Fin k, ∑ c : Fin k, ∑ a : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro a _; ring
      _ = ∑ b : Fin k, ∑ a : Fin k, ∑ c : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
      _ = ∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) :=
          Finset.sum_comm
      _ = ∑ a : Fin k,
            (∑ b : Fin k, left b * ((pref i).map M).prod b a) *
            (∑ c : Fin k, ((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.mul_sum]
  rw [hfac]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans (Fintype.card_fin k).le)

lemma lower_bound_zero {r k : ℕ} (hfit : Fits r 0 k (fun w => w.length ≤ 3)) :
    2 ≤ k := by
  let pref : Fin 2 → List (Vec r) := ![ [], [0] ]
  let suff : Fin 2 → List (Vec r) := ![ [], [0, 0] ]
  have hlen : ∀ i j : Fin 2, (pref i ++ suff j).length ≤ 3 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pref, suff]
  let H : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of (fun i j => seriesVal 0 (pref i ++ suff j))
  have hle : H.rank ≤ k := hankel_rank_le pref suff hlen hfit
  have h00 : H 0 0 = 1 := by simp [H, pref, suff, series_nil]
  have h01 : H 0 1 = 0 := by simp [H, pref, suff, series_two, fVal]
  have h10 : H 1 0 = 1 := by simp [H, pref, suff, series_one]
  have h11 : H 1 1 = -2 := by simp [H, pref, suff, series_three, fVal]; ring
  have hinj : Function.Injective H.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hr0 : (H.mulVec v) 0 = 0 := congrFun hv 0
    have hr1 : (H.mulVec v) 1 = 0 := congrFun hv 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h10, h11] at hr0 hr1
    funext i
    fin_cases i
    · change v 0 = 0; linarith
    · change v 1 = 0; linarith
  have hrank2 : H.rank = 2 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  omega

lemma lower_bound_nonzero {r k : ℕ} {z : ℚ} (hz0 : z ≠ 0)
    (hfit : Fits r z k (fun w => w.length ≤ 3)) :
    (if z = (2 ^ r : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k := by
  let pref : Option (Vec r) → List (Vec r) := fun s => s.elim [] (fun a => [a])
  let suff : Option (Vec r) → List (Vec r) := fun s => s.elim [] (fun b => [b, 0])
  have hlen : ∀ i j : Option (Vec r), (pref i ++ suff j).length ≤ 3 := by
    intro i j
    cases i <;> cases j <;> simp [pref, suff]
  let H : Matrix (Option (Vec r)) (Option (Vec r)) ℚ :=
    Matrix.of (fun i j => seriesVal z (pref i ++ suff j))
  have hH_le : H.rank ≤ k := hankel_rank_le pref suff hlen hfit
  let L : Matrix (Option (Vec r)) (Option (Vec r)) ℚ := fun i s =>
    i.elim (if s = none then 1 else 0)
      (fun a => if s = some a then 1 else if s = none then -1 else 0)
  let LH := L * H
  have hLH_le : LH.rank ≤ k := (Matrix.rank_mul_le_right L H).trans hH_le
  have hLH_none_none : LH none none = 1 := by
    change (L * H) none none = 1
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp [L, H, pref, suff, series_nil]
  have hLH_none_some : ∀ b : Vec r, LH none (some b) = 1 + fVal z b := by
    intro b
    change (L * H) none (some b) = 1 + fVal z b
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp [L, H, pref, suff, series_two]
  have hLH_some_none : ∀ a : Vec r, LH (some a) none = 0 := by
    intro a
    change (L * H) (some a) none = 0
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [L, H, Matrix.of_apply, pref, suff, Option.elim_none, Option.elim_some,
      reduceCtorEq, ↓reduceIte, List.append_nil, series_nil, series_one]
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact False.elim (h (Finset.mem_univ a))
  have hLH_some_some : ∀ a b : Vec r, LH (some a) (some b) = fVal z a + fVal z (a + b) := by
    intro a b
    change (L * H) (some a) (some b) = fVal z a + fVal z (a + b)
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [L, H, Matrix.of_apply, pref, suff, Option.elim_none, Option.elim_some,
      reduceCtorEq, ↓reduceIte, List.nil_append, List.cons_append, series_two, series_three]
    rw [Finset.sum_eq_single a]
    · simp; ring
    · intro x _ hx; simp [hx]
    · intro h; exact False.elim (h (Finset.mem_univ a))
  have hker_eq : ∀ v : Option (Vec r) → ℚ, v ∈ LinearMap.ker LH.mulVecLin →
      let S := ∑ b : Vec r, v (some b)
      (∀ a : Vec r, z * v (some a) = (1 - fVal z a) * S) ∧
      v none = - ∑ b : Vec r, (1 + fVal z b) * v (some b) ∧
      2 * (z - (2 ^ r : ℚ)) * S = 0 := by
    intro v hv
    dsimp only
    let S := ∑ b : Vec r, v (some b)
    have hmv : LH.mulVec v = 0 := hv
    have htop : v none = - ∑ b : Vec r, (1 + fVal z b) * v (some b) := by
      have h0 : (LH.mulVec v) none = 0 := congrFun hmv none
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, hLH_none_none, hLH_none_some,
        one_mul] at h0
      linarith
    have hbot : ∀ a : Vec r, z * v (some a) = (1 - fVal z a) * S := by
      intro a
      have ha : (LH.mulVec v) (some a) = 0 := congrFun hmv (some a)
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, hLH_some_none, hLH_some_some,
        zero_mul, zero_add] at ha
      have hfab : ∀ b : Vec r, fVal z (a + b) = (if a = b then z else 0) - 1 := by
        intro b
        simp only [fVal, vec_add_eq_zero_iff]
        by_cases hab : a = b <;> simp [hab]
      simp_rw [hfab, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, one_mul] at ha
      have hsingle : ∑ b : Vec r, (if a = b then z else 0) * v (some b) = z * v (some a) := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact False.elim (h (Finset.mem_univ a))
      rw [hsingle] at ha
      change fVal z a * S + (z * v (some a) - S) = 0 at ha
      linarith
    have hsum_eq : 2 * (z - (2 ^ r : ℚ)) * S = 0 := by
      have h1 : ∑ a : Vec r, z * v (some a) = ∑ a : Vec r, (1 - fVal z a) * S :=
        Finset.sum_congr rfl (fun a _ => hbot a)
      rw [← Finset.mul_sum, ← Finset.sum_mul, sum_one_sub_fVal] at h1
      change z * S = (2 * (2 ^ r : ℚ) - z) * S at h1
      linarith
    exact ⟨hbot, htop, hsum_eq⟩
  have hrn := LH.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hcard_opt : Fintype.card (Option (Vec r)) = 2 ^ r + 1 := by
    simp
  rw [hcard_opt] at hrn
  change LH.rank + Module.finrank ℚ (LinearMap.ker LH.mulVecLin) = 2 ^ r + 1 at hrn
  by_cases hzq : z = (2 ^ r : ℚ)
  · simp only [hzq, ↓reduceIte]
    let w0 : Option (Vec r) → ℚ := fun s =>
      s.elim (- ∑ b : Vec r, (1 + fVal z b) * ((1 - fVal z b) / z))
        (fun a => (1 - fVal z a) / z)
    let g : ℚ →ₗ[ℚ] (Option (Vec r) → ℚ) := LinearMap.toSpanSingleton ℚ (Option (Vec r) → ℚ) w0
    have hker_sub : LinearMap.ker LH.mulVecLin ≤ LinearMap.range g := by
      intro v hv
      rcases hker_eq v hv with ⟨hbot, htop, _⟩
      let S := ∑ b : Vec r, v (some b)
      refine ⟨S, ?_⟩
      change S • w0 = v
      symm
      funext s
      cases s with
      | none =>
        simp only [Pi.smul_apply, smul_eq_mul, w0, Option.elim_none, htop]
        have hterm : ∀ b : Vec r, (1 + fVal z b) * v (some b) =
            S * ((1 + fVal z b) * ((1 - fVal z b) / z)) := by
          intro b
          have hvb : v (some b) = S * ((1 - fVal z b) / z) := by
            have hb := hbot b
            field_simp [hz0]
            linarith
          rw [hvb]; ring
        simp_rw [hterm, ← Finset.mul_sum]
        ring
      | some a =>
        simp only [Pi.smul_apply, smul_eq_mul, w0, Option.elim_some]
        have ha := hbot a
        field_simp [hz0]
        linarith
    have hfin_ker : Module.finrank ℚ (LinearMap.ker LH.mulVecLin) ≤ 1 := by
      calc Module.finrank ℚ (LinearMap.ker LH.mulVecLin)
          ≤ Module.finrank ℚ (LinearMap.range g) := Submodule.finrank_mono hker_sub
        _ ≤ Module.finrank ℚ ℚ := LinearMap.finrank_range_le g
        _ = 1 := Module.finrank_self ℚ
    omega
  · simp only [hzq, ↓reduceIte]
    have hker_bot : LinearMap.ker LH.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      rcases hker_eq v hv with ⟨hbot, htop, hS0⟩
      have hsub_ne : z - (2 ^ r : ℚ) ≠ 0 := sub_ne_zero.mpr hzq
      have hS_zero : ∑ b : Vec r, v (some b) = 0 := by
        have h1 : 2 * (z - (2 ^ r : ℚ)) ≠ 0 := mul_ne_zero (by norm_num) hsub_ne
        exact (mul_eq_zero.mp hS0).resolve_left h1
      have hsome0 : ∀ a : Vec r, v (some a) = 0 := by
        intro a
        have ha := hbot a
        rw [hS_zero, mul_zero] at ha
        exact (mul_eq_zero.mp ha).resolve_left hz0
      funext s
      cases s with
      | none =>
        rw [htop]
        simp [hsome0]
      | some a => exact hsome0 a
    rw [hker_bot, finrank_bot, add_zero] at hrn
    omega

lemma main_proof (r : ℕ) (z : ℚ) (k : ℕ) :
    (Fits r z k (fun w => w.length ≤ 3) ↔
      (if z = 0 then 2 else if z = ((2 ^ r : ℕ) : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k) ∧
    (Fits r z k (fun _ => True) ↔
      (if z = 0 then 2 else if z = ((2 ^ r : ℕ) : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k) := by
  have hup : (if z = 0 then 2 else if z = ((2 ^ r : ℕ) : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k →
      Fits r z k (fun _ => True) := by
    intro hk
    by_cases hz0 : z = 0
    · subst hz0
      simp only [↓reduceIte] at hk
      exact fits_mono 0 hk (fits_zero r)
    · simp only [hz0, ↓reduceIte] at hk
      by_cases hzq : z = ((2 ^ r : ℕ) : ℚ)
      · subst hzq
        simp only [↓reduceIte] at hk
        simpa using fits_mono (2 ^ r : ℚ) hk (fits_q r)
      · simp only [hzq, ↓reduceIte] at hk
        exact fits_mono z hk (fits_general r z)
  have hdown : Fits r z k (fun w => w.length ≤ 3) →
      (if z = 0 then 2 else if z = ((2 ^ r : ℕ) : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k := by
    intro hfit
    by_cases hz0 : z = 0
    · subst hz0
      simp only [↓reduceIte]
      exact lower_bound_zero hfit
    · simp only [hz0, ↓reduceIte]
      simpa using lower_bound_nonzero hz0 hfit
  have hweak : Fits r z k (fun _ => True) → Fits r z k (fun w => w.length ≤ 3) := by
    rintro ⟨left, right, M, hM⟩
    exact ⟨left, right, M, fun w _ => hM w trivial⟩
  exact ⟨⟨hdown, fun hk => hweak (hup hk)⟩, ⟨fun h => hdown (hweak h), hup⟩⟩

end PEqualNP.Outside.L_lib_792_aux

theorem PEqualNP.Outside.L_lib_792 :
∀ (r : ℕ) (z : ℚ),
  let A := Fin r → ZMod 2
  let q := 2^r
  let f := fun a : A => if a = 0 then z-1 else -1
  let T : A → Matrix (Option A) (Option A) ℚ := fun h before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (f a) (fun b => if b = a+h then 1 else 0))
  let series := fun w : List A => (w.map T).prod none none
  let fits := fun (k : ℕ) (test : List A → Prop) =>
    ∃ (left right : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
      ∀ w : List A, test w →
        (∑ i : Fin k, ∑ j : Fin k, left i * (w.map M).prod i j * right j) = series w
  let least := if z = 0 then 2 else if z = (q : ℚ) then q else q+1
  ∀ k : ℕ, (fits k (fun w => w.length ≤ 3) ↔ least ≤ k) ∧
    (fits k (fun _ => True) ↔ least ≤ k) := by
  intro r z
  dsimp only
  intro k
  have hcast :
      ((if z = 0 then (2 : ℚ) else if z = 2 ^ r then 2 ^ r else 2 ^ r + 1) ≤ (k : ℚ)) ↔
      ((if z = 0 then (2 : ℕ) else if z = ((2 ^ r : ℕ) : ℚ) then 2 ^ r else 2 ^ r + 1) ≤ k) := by
    by_cases hz0 : z = 0
    · simp only [hz0, ↓reduceIte]
      exact_mod_cast Iff.rfl
    · simp only [hz0, ↓reduceIte]
      by_cases hzq : z = ((2 ^ r : ℕ) : ℚ)
      · subst hzq
        simp only [Nat.cast_pow, Nat.cast_ofNat, ↓reduceIte]
        exact_mod_cast Iff.rfl
      · have hzq' : z ≠ (2 ^ r : ℚ) := by simpa using hzq
        simp only [hzq, hzq', ↓reduceIte]
        exact_mod_cast Iff.rfl
  rw [hcast]
  exact PEqualNP.Outside.L_lib_792_aux.main_proof r z k
