import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_574_aux

open Finset

def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

def ofZ2 (z : ZMod 2) : Bool := decide (z = 1)

lemma toZ2_injective : Function.Injective toZ2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma toZ2_ofZ2 (z : ZMod 2) : toZ2 (ofZ2 z) = z := by
  fin_cases z <;> rfl

lemma z2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> rfl

lemma z2_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  fin_cases x <;> fin_cases y <;> first | rfl | exact absurd h (by decide)

lemma exists_win_idx {n h : ℕ} (hh : h ≤ n)
    (start : ℕ) (hstart : start + h ≤ n) (u : Fin n)
    (hu : u.val < start ∨ start + h ≤ u.val) :
    ∃ j : Fin (n - h), ((start + h) % n + j.val) % n = u.val := by
  by_cases hfull : start + h = n
  · have hlt : u.val < n - h := by omega
    refine ⟨⟨u.val, hlt⟩, ?_⟩
    rw [hfull, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt u.isLt]
  · have hlt_n : start + h < n := by omega
    rw [Nat.mod_eq_of_lt hlt_n]
    rcases hu with h1 | h2
    · refine ⟨⟨n - (start + h) + u.val, by omega⟩, ?_⟩
      have heq : start + h + (n - (start + h) + u.val) = n + u.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt u.isLt]
    · refine ⟨⟨u.val - (start + h), by omega⟩, ?_⟩
      have heq : start + h + (u.val - (start + h)) = u.val := by omega
      rw [heq, Nat.mod_eq_of_lt u.isLt]

lemma card_nonZeroLab (s : ℕ) :
    Fintype.card {v : Fin s → Bool // ∃ j : Fin s, v j = true} = 2 ^ s - 1 := by
  have hcompl :
      Fintype.card {v : Fin s → Bool // ∃ j : Fin s, v j = true} +
      Fintype.card {v : Fin s → Bool // ¬ ∃ j : Fin s, v j = true} =
      Fintype.card (Fin s → Bool) := by
    rw [Fintype.card_subtype_compl, add_comm]
    exact Nat.sub_add_cancel
      (Fintype.card_subtype_le (fun v : Fin s → Bool => ∃ j : Fin s, v j = true))
  have hfalse : Fintype.card {v : Fin s → Bool // ¬ ∃ j : Fin s, v j = true} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨fun _ => false, by simp⟩, ?_⟩
    rintro ⟨v, hv⟩
    apply Subtype.ext
    funext j
    cases h : v j
    · exact h
    · exact absurd ⟨j, h⟩ hv
  have htot : Fintype.card (Fin s → Bool) = 2 ^ s := by simp
  omega

def skipIdx {q' : ℕ} (t0 : Fin (q' + 1)) (j : Fin q') : Fin (q' + 1) :=
  t0.succAbove j

lemma skipIdx_ne {q' : ℕ} (t0 : Fin (q' + 1)) (j : Fin q') : skipIdx t0 j ≠ t0 :=
  Fin.succAbove_ne t0 j

lemma skipIdx_inj {q' : ℕ} (t0 : Fin (q' + 1)) : Function.Injective (skipIdx t0) :=
  Fin.succAbove_right_injective

lemma exists_skipIdx {q' : ℕ} (t0 t : Fin (q' + 1)) (hne : t ≠ t0) :
    ∃ j : Fin q', skipIdx t0 j = t :=
  Fin.exists_succAbove_eq hne

noncomputable def unskipIdx {q' : ℕ} (t0 t : Fin (q' + 1)) (hne : t ≠ t0) : Fin q' :=
  Classical.choose (exists_skipIdx t0 t hne)

lemma skipIdx_unskipIdx {q' : ℕ} (t0 t : Fin (q' + 1)) (hne : t ≠ t0) :
    skipIdx t0 (unskipIdx t0 t hne) = t :=
  Classical.choose_spec (exists_skipIdx t0 t hne)

lemma unskipIdx_skipIdx {q' : ℕ} (t0 : Fin (q' + 1)) (j : Fin q') :
    unskipIdx t0 (skipIdx t0 j) (skipIdx_ne t0 j) = j :=
  skipIdx_inj t0 (skipIdx_unskipIdx t0 (skipIdx t0 j) (skipIdx_ne t0 j))

lemma unskipIdx_skipIdx_eq {q' : ℕ} {t1 t2 : Fin (q' + 1)} (heq : t1 = t2) (k : Fin q')
    (hne : skipIdx t1 k ≠ t2) : unskipIdx t2 (skipIdx t1 k) hne = k := by
  subst heq
  exact unskipIdx_skipIdx t1 k

def lPosOf (a b h s q' : ℕ) (hsh : s ≤ h) (ha : (q' + 1) * h < a)
    (t : Fin (q' + 1)) (j : Fin s) : Fin (a + b) :=
  ⟨t.val * h + j.val, by
    have ht : t.val + 1 ≤ q' + 1 := t.isLt
    have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    omega⟩

def rPosOf (a b h s q' : ℕ) (hsh : s ≤ h) (hb : (q' + 1 + 1) * h ≤ b)
    (t : Fin (q' + 1)) (j : Fin s) : Fin (a + b) :=
  ⟨a + t.val * h + j.val, by
    have ht : t.val + 1 ≤ q' + 1 := t.isLt
    have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    have hqb : (q' + 1) * h + h = (q' + 1 + 1) * h := by ring
    omega⟩

def lParOf (a b h s q' : ℕ) (hsh : s ≤ h) (ha : (q' + 1) * h < a)
    (t : Fin (q' + 1)) (c : Fin (h - s)) : Fin (a + b) :=
  ⟨t.val * h + (s + c.val), by
    have ht : t.val + 1 ≤ q' + 1 := t.isLt
    have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    omega⟩

def rParOf (a b h s q' : ℕ) (hsh : s ≤ h) (hb : (q' + 1 + 1) * h ≤ b)
    (t : Fin (q' + 1)) (c : Fin (h - s)) : Fin (a + b) :=
  ⟨a + t.val * h + (s + c.val), by
    have ht : t.val + 1 ≤ q' + 1 := t.isLt
    have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    have hqb : (q' + 1) * h + h = (q' + 1 + 1) * h := by ring
    omega⟩

def ValidWord (a b h s q' : ℕ) (hsh : s ≤ h)
    (ha : (q' + 1) * h < a) (hb : (q' + 1 + 1) * h ≤ b) (x : Fin (a + b) → Bool) : Prop :=
  (∃! t : Fin (q' + 1), ∀ j : Fin s, x (lPosOf a b h s q' hsh ha t j) = false) ∧
  (∃! t : Fin (q' + 1), ∀ j : Fin s, x (rPosOf a b h s q' hsh hb t j) = false) ∧
  (∀ c : Fin (h - s),
    (∑ t : Fin (q' + 1), toZ2 (x (lParOf a b h s q' hsh ha t c))) +
    (∑ t : Fin (q' + 1), toZ2 (x (rParOf a b h s q' hsh hb t c))) = 0)

theorem exists_valid_code (a b h s q' : ℕ) (hs : 0 < s) (hsh : s ≤ h)
    (ha : (q' + 1) * h < a) (hb : (q' + 1 + 1) * h ≤ b) :
    let q := q' + 1
    let n := a + b
    let M := q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (n - (2 * q * s + (h - s)))
    ∃ (code : Fin M → Fin n → Bool) (tL tR : Fin M → Fin q),
      Function.Injective code ∧
      (∀ i, ValidWord a b h s q' hsh ha hb (code i)) ∧
      (∀ x, ValidWord a b h s q' hsh ha hb x → ∃ i, code i = x) ∧
      (∀ i j, code i (lPosOf a b h s q' hsh ha (tL i) j) = false) ∧
      (∀ i j, code i (rPosOf a b h s q' hsh hb (tR i) j) = false) := by
  classical
  intro q n M
  have hh : 0 < h := Nat.lt_of_lt_of_le hs hsh
  have hq_def : q = q' + 1 := rfl
  have hn_def : n = a + b := rfl
  let lPos := lPosOf a b h s q' hsh ha
  let rPos := rPosOf a b h s q' hsh hb
  let lPar := lParOf a b h s q' hsh ha
  let rPar := rParOf a b h s q' hsh hb
  let LLab : Finset (Fin n) := Finset.univ.image (fun p : Fin q × Fin s => lPos p.1 p.2)
  let RLab : Finset (Fin n) := Finset.univ.image (fun p : Fin q × Fin s => rPos p.1 p.2)
  let L0Par : Finset (Fin n) := Finset.univ.image (fun c : Fin (h - s) => lPar 0 c)
  let DepSet : Finset (Fin n) := LLab ∪ RLab ∪ L0Par
  have hLLab_inj : Function.Injective (fun p : Fin q × Fin s => lPos p.1 p.2) := by
    intro p1 p2 heq
    have hv : p1.1.val * h + p1.2.val = p2.1.val * h + p2.2.val := congrArg Fin.val heq
    have h1 : (p1.1.val * h + p1.2.val) / h = p1.1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have h2 : (p2.1.val * h + p2.2.val) / h = p2.1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [hv] at h1
    have hqeq : p1.1.val = p2.1.val := h1.symm.trans h2
    have hjeq : p1.2.val = p2.2.val := by rw [hqeq] at hv; omega
    exact Prod.ext (Fin.ext hqeq) (Fin.ext hjeq)
  have hRLab_inj : Function.Injective (fun p : Fin q × Fin s => rPos p.1 p.2) := by
    intro p1 p2 heq
    have hv : a + p1.1.val * h + p1.2.val = a + p2.1.val * h + p2.2.val := congrArg Fin.val heq
    have hv' : p1.1.val * h + p1.2.val = p2.1.val * h + p2.2.val := by omega
    have h1 : (p1.1.val * h + p1.2.val) / h = p1.1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have h2 : (p2.1.val * h + p2.2.val) / h = p2.1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hh, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [hv'] at h1
    have hqeq : p1.1.val = p2.1.val := h1.symm.trans h2
    have hjeq : p1.2.val = p2.2.val := by rw [hqeq] at hv'; omega
    exact Prod.ext (Fin.ext hqeq) (Fin.ext hjeq)
  have hL0Par_inj : Function.Injective (fun c : Fin (h - s) => lPar 0 c) := by
    intro c1 c2 heq
    have hv : (0 : Fin q).val * h + (s + c1.val) = (0 : Fin q).val * h + (s + c2.val) :=
      congrArg Fin.val heq
    exact Fin.ext (by omega)
  have hLLab_lt_a : ∀ u ∈ LLab, u.val < a := by
    intro u hu
    obtain ⟨⟨t, j⟩, _, rfl⟩ := Finset.mem_image.1 hu
    have ht : t.val + 1 ≤ q' + 1 := t.isLt
    have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    dsimp [lPos, lPosOf]; omega
  have hRLab_ge_a : ∀ u ∈ RLab, a ≤ u.val := by
    intro u hu
    obtain ⟨⟨t, j⟩, _, rfl⟩ := Finset.mem_image.1 hu
    dsimp [rPos, rPosOf]; omega
  have hDisj_LR : Disjoint LLab RLab := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    have := hLLab_lt_a u h1
    have := hRLab_ge_a u h2
    omega
  have hDisj_L0 : Disjoint (LLab ∪ RLab) L0Par := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 h2
    rcases Finset.mem_union.1 h1 with hL | hR
    · obtain ⟨⟨t, j⟩, _, heq⟩ := Finset.mem_image.1 hL
      have hv : t.val * h + j.val = (0 : Fin q).val * h + (s + c.val) := congrArg Fin.val heq
      have h0v : (0 : Fin q).val = 0 := rfl
      rw [h0v, Nat.zero_mul, Nat.zero_add] at hv
      have : t.val = 0 := by
        by_contra hne
        have : h ≤ t.val * h := Nat.le_mul_of_pos_left h (Nat.pos_of_ne_zero hne)
        omega
      rw [this, Nat.zero_mul, Nat.zero_add] at hv
      omega
    · have hge := hRLab_ge_a _ hR
      dsimp [lPar, lParOf] at hge
      have h1 : h ≤ (q' + 1) * h := Nat.le_mul_of_pos_left h (Nat.succ_pos q')
      omega
  have hDepCard : DepSet.card = 2 * q * s + (h - s) := by
    dsimp only [DepSet]
    rw [Finset.card_union_of_disjoint hDisj_L0, Finset.card_union_of_disjoint hDisj_LR]
    rw [Finset.card_image_of_injective _ hLLab_inj,
      Finset.card_image_of_injective _ hRLab_inj,
      Finset.card_image_of_injective _ hL0Par_inj]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  have hPar_not_dep_L : ∀ (t : Fin q) (ht : t ≠ 0) (c : Fin (h - s)), lPar t c ∉ DepSet := by
    intro t ht c hmem
    have htv : 0 < t.val := Nat.pos_of_ne_zero (fun h0 => ht (Fin.ext h0))
    dsimp only [DepSet] at hmem
    rcases Finset.mem_union.1 hmem with hLR | h0
    · rcases Finset.mem_union.1 hLR with hL | hR
      · obtain ⟨⟨t', j⟩, _, heq⟩ := Finset.mem_image.1 hL
        have hv : t'.val * h + j.val = t.val * h + (s + c.val) := congrArg Fin.val heq
        have hmod1 : (t'.val * h + j.val) % h = j.val := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        have hmod2 : (t.val * h + (s + c.val)) % h = s + c.val := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hv] at hmod1
        omega
      · have hge := hRLab_ge_a _ hR
        dsimp [lPar, lParOf] at hge
        have ht1 : t.val + 1 ≤ q' + 1 := t.isLt
        have hmul : (t.val + 1) * h ≤ (q' + 1) * h := Nat.mul_le_mul_right h ht1
        have hmul' : t.val * h + h = (t.val + 1) * h := by ring
        omega
    · obtain ⟨c', _, heq⟩ := Finset.mem_image.1 h0
      have hv : (0 : Fin q).val * h + (s + c'.val) = t.val * h + (s + c.val) := congrArg Fin.val heq
      have h0v : (0 : Fin q).val = 0 := rfl
      rw [h0v, Nat.zero_mul, Nat.zero_add] at hv
      have : h ≤ t.val * h := Nat.le_mul_of_pos_left h htv
      omega
  have hPar_not_dep_R : ∀ (t : Fin q) (c : Fin (h - s)), rPar t c ∉ DepSet := by
    intro t c hmem
    dsimp only [DepSet] at hmem
    rcases Finset.mem_union.1 hmem with hLR | h0
    · rcases Finset.mem_union.1 hLR with hL | hR
      · have hlt := hLLab_lt_a _ hL
        dsimp [rPar, rParOf] at hlt
        omega
      · obtain ⟨⟨t', j⟩, _, heq⟩ := Finset.mem_image.1 hR
        have hv : a + t'.val * h + j.val = a + t.val * h + (s + c.val) := congrArg Fin.val heq
        have hv' : t'.val * h + j.val = t.val * h + (s + c.val) := by omega
        have hmod1 : (t'.val * h + j.val) % h = j.val := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        have hmod2 : (t.val * h + (s + c.val)) % h = s + c.val := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hv'] at hmod1
        omega
    · obtain ⟨c', _, heq⟩ := Finset.mem_image.1 h0
      have hv : (0 : Fin q).val * h + (s + c'.val) = a + t.val * h + (s + c.val) := congrArg Fin.val heq
      have h0v : (0 : Fin q).val = 0 := rfl
      rw [h0v, Nat.zero_mul, Nat.zero_add] at hv
      have h1 : h ≤ (q' + 1) * h := Nat.le_mul_of_pos_left h (Nat.succ_pos q')
      omega
  let NonZero := {v : Fin s → Bool // ∃ j : Fin s, v j = true}
  let FreeIdx := {u : Fin n // u ∉ DepSet}
  let Param := (Fin q × Fin q) × ((Fin q' → NonZero) × (Fin q' → NonZero)) × (FreeIdx → Bool)
  have hFreeCard : Fintype.card FreeIdx = n - (2 * q * s + (h - s)) := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe, hDepCard]
  have hNZCard : Fintype.card NonZero = 2 ^ s - 1 := card_nonZeroLab s
  have hParamCard : Fintype.card Param = M := by
    dsimp only [Param, M]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      hNZCard, hFreeCard]
    have hqm : q - 1 = q' := Nat.add_sub_cancel q' 1
    rw [hqm]
    ring
  let rawWord : Param → Fin n → Bool := fun p u =>
    if hu : u ∉ DepSet then
      p.2.2 ⟨u, hu⟩
    else if hL : u ∈ LLab then
      let pr := Classical.choose (Finset.mem_image.1 hL)
      if ht : pr.1 = p.1.1 then false
      else (p.2.1.1 (unskipIdx p.1.1 pr.1 ht)).1 pr.2
    else if hR : u ∈ RLab then
      let pr := Classical.choose (Finset.mem_image.1 hR)
      if ht : pr.1 = p.1.2 then false
      else (p.2.1.2 (unskipIdx p.1.2 pr.1 ht)).1 pr.2
    else false
  let encode : Param → Fin n → Bool := fun p u =>
    if h0 : u ∈ L0Par then
      let c := Classical.choose (Finset.mem_image.1 h0)
      ofZ2 ((∑ t ∈ Finset.univ.erase (0 : Fin q), toZ2 (rawWord p (lPar t c))) +
            (∑ t : Fin q, toZ2 (rawWord p (rPar t c))))
    else rawWord p u
  have hraw_free : ∀ (p : Param) (u : Fin n) (hu : u ∉ DepSet), encode p u = p.2.2 ⟨u, hu⟩ := by
    intro p u hu
    have h0 : u ∉ L0Par := fun h => hu (Finset.mem_union_right _ h)
    dsimp only [encode, rawWord]
    simp only [h0, hu, not_false_eq_true, ↓reduceDIte]
  have hraw_lLab : ∀ (p : Param) (t : Fin q) (j : Fin s),
      encode p (lPos t j) =
        if ht : t = p.1.1 then false else (p.2.1.1 (unskipIdx p.1.1 t ht)).1 j := by
    intro p t j
    have hL : lPos t j ∈ LLab := Finset.mem_image.2 ⟨(t, j), Finset.mem_univ _, rfl⟩
    have h0 : lPos t j ∉ L0Par :=
      Finset.disjoint_left.1 hDisj_L0 (Finset.mem_union_left _ hL)
    have hdep : lPos t j ∈ DepSet := Finset.mem_union_left _ (Finset.mem_union_left _ hL)
    have hch : Classical.choose (Finset.mem_image.1 hL) = (t, j) :=
      hLLab_inj (Classical.choose_spec (Finset.mem_image.1 hL)).2
    dsimp only [encode, rawWord]
    simp only [h0, hdep, not_true_eq_false, hL, ↓reduceDIte]
    rw [hch]
  have hraw_rLab : ∀ (p : Param) (t : Fin q) (j : Fin s),
      encode p (rPos t j) =
        if ht : t = p.1.2 then false else (p.2.1.2 (unskipIdx p.1.2 t ht)).1 j := by
    intro p t j
    have hR : rPos t j ∈ RLab := Finset.mem_image.2 ⟨(t, j), Finset.mem_univ _, rfl⟩
    have h0 : rPos t j ∉ L0Par :=
      Finset.disjoint_left.1 hDisj_L0 (Finset.mem_union_right _ hR)
    have hL : rPos t j ∉ LLab := Finset.disjoint_right.1 hDisj_LR hR
    have hdep : rPos t j ∈ DepSet := Finset.mem_union_left _ (Finset.mem_union_right _ hR)
    have hch : Classical.choose (Finset.mem_image.1 hR) = (t, j) :=
      hRLab_inj (Classical.choose_spec (Finset.mem_image.1 hR)).2
    dsimp only [encode, rawWord]
    simp only [h0, hdep, not_true_eq_false, hL, hR, ↓reduceDIte]
    rw [hch]
  have hraw_l0Par : ∀ (p : Param) (c : Fin (h - s)),
      encode p (lPar 0 c) =
        ofZ2 ((∑ t ∈ Finset.univ.erase (0 : Fin q), toZ2 (encode p (lPar t c))) +
              (∑ t : Fin q, toZ2 (encode p (rPar t c)))) := by
    intro p c
    have h0 : lPar 0 c ∈ L0Par := Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩
    dsimp only [encode]
    split_ifs with h1
    · have hch : Classical.choose (Finset.mem_image.1 h1) = c :=
        hL0Par_inj (Classical.choose_spec (Finset.mem_image.1 h1)).2
      rw [hch]
      congr 1
      congr 1
      · refine Finset.sum_congr rfl (fun t ht => ?_)
        have hne : t ≠ 0 := (Finset.mem_erase.1 ht).1
        have hn0 : lPar t c ∉ L0Par := fun h => hPar_not_dep_L t hne c (Finset.mem_union_right _ h)
        simp only [hn0, ↓reduceDIte]
      · refine Finset.sum_congr rfl (fun t _ => ?_)
        have hn0 : rPar t c ∉ L0Par := fun h => hPar_not_dep_R t c (Finset.mem_union_right _ h)
        simp only [hn0, ↓reduceDIte]
    · exact absurd h0 h1
  have henc_valid : ∀ p : Param, ValidWord a b h s q' hsh ha hb (encode p) := by
    intro p
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨p.1.1, fun j => by rw [hraw_lLab]; simp, ?_⟩
      intro t ht
      by_contra hne
      obtain ⟨j, hj⟩ := (p.2.1.1 (unskipIdx p.1.1 t hne)).2
      have htj := ht j
      rw [hraw_lLab] at htj
      simp only [hne, ↓reduceDIte] at htj
      rw [hj] at htj
      cases htj
    · refine ⟨p.1.2, fun j => by rw [hraw_rLab]; simp, ?_⟩
      intro t ht
      by_contra hne
      obtain ⟨j, hj⟩ := (p.2.1.2 (unskipIdx p.1.2 t hne)).2
      have htj := ht j
      rw [hraw_rLab] at htj
      simp only [hne, ↓reduceDIte] at htj
      rw [hj] at htj
      cases htj
    · intro c
      rw [← Finset.add_sum_erase Finset.univ (fun t => toZ2 (encode p (lPar t c))) (Finset.mem_univ 0)]
      rw [hraw_l0Par p c, toZ2_ofZ2, add_assoc]
      exact z2_add_self _
  have henc_inj : Function.Injective encode := by
    intro p1 p2 heq
    have h1 : p1.1.1 = p2.1.1 := by
      have h0 : ∀ j : Fin s, encode p2 (lPos p1.1.1 j) = false := by
        intro j; rw [← heq, hraw_lLab]; simp
      exact (henc_valid p2).1.unique h0 (fun j => by rw [hraw_lLab]; simp)
    have h2 : p1.1.2 = p2.1.2 := by
      have h0 : ∀ j : Fin s, encode p2 (rPos p1.1.2 j) = false := by
        intro j; rw [← heq, hraw_rLab]; simp
      exact (henc_valid p2).2.1.unique h0 (fun j => by rw [hraw_rLab]; simp)
    have h3 : p1.2.1.1 = p2.2.1.1 := by
      funext k
      apply Subtype.ext
      funext j
      have hne : skipIdx p1.1.1 k ≠ p1.1.1 := skipIdx_ne p1.1.1 k
      have hne2 : skipIdx p1.1.1 k ≠ p2.1.1 := by rwa [← h1]
      have hl1 := hraw_lLab p1 (skipIdx p1.1.1 k) j
      have hl2 := hraw_lLab p2 (skipIdx p1.1.1 k) j
      rw [heq] at hl1
      rw [hl1] at hl2
      simp only [hne, hne2, ↓reduceDIte] at hl2
      rw [unskipIdx_skipIdx, unskipIdx_skipIdx_eq h1 k hne2] at hl2
      exact hl2
    have h4 : p1.2.1.2 = p2.2.1.2 := by
      funext k
      apply Subtype.ext
      funext j
      have hne : skipIdx p1.1.2 k ≠ p1.1.2 := skipIdx_ne p1.1.2 k
      have hne2 : skipIdx p1.1.2 k ≠ p2.1.2 := by rwa [← h2]
      have hr1 := hraw_rLab p1 (skipIdx p1.1.2 k) j
      have hr2 := hraw_rLab p2 (skipIdx p1.1.2 k) j
      rw [heq] at hr1
      rw [hr1] at hr2
      simp only [hne, hne2, ↓reduceDIte] at hr2
      rw [unskipIdx_skipIdx, unskipIdx_skipIdx_eq h2 k hne2] at hr2
      exact hr2
    have h5 : p1.2.2 = p2.2.2 := by
      funext ⟨u, hu⟩
      have hf1 := hraw_free p1 u hu
      have hf2 := hraw_free p2 u hu
      rw [heq] at hf1
      exact hf1.symm.trans hf2
    rcases p1 with ⟨⟨a1, b1⟩, ⟨c1, d1⟩, e1⟩
    rcases p2 with ⟨⟨a2, b2⟩, ⟨c2, d2⟩, e2⟩
    dsimp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl
  have henc_surj : ∀ x : Fin n → Bool, ValidWord a b h s q' hsh ha hb x → ∃ p : Param, encode p = x := by
    intro x ⟨⟨tL, htL0, htLu⟩, ⟨tR, htR0, htRu⟩, hpar⟩
    let labL : Fin q' → NonZero := fun k =>
      ⟨fun j => x (lPos (skipIdx tL k) j), by
        by_contra hnone
        have hall : ∀ j : Fin s, x (lPos (skipIdx tL k) j) = false := by
          intro j
          cases hxj : x (lPos (skipIdx tL k) j)
          · rfl
          · exact absurd ⟨j, hxj⟩ hnone
        exact skipIdx_ne tL k (htLu _ hall)⟩
    let labR : Fin q' → NonZero := fun k =>
      ⟨fun j => x (rPos (skipIdx tR k) j), by
        by_contra hnone
        have hall : ∀ j : Fin s, x (rPos (skipIdx tR k) j) = false := by
          intro j
          cases hxj : x (rPos (skipIdx tR k) j)
          · rfl
          · exact absurd ⟨j, hxj⟩ hnone
        exact skipIdx_ne tR k (htRu _ hall)⟩
    let p : Param := ((tL, tR), (labL, labR), fun u => x u.1)
    refine ⟨p, ?_⟩
    funext u
    by_cases hnd : u ∉ DepSet
    · exact hraw_free p u hnd
    · have hdep : u ∈ DepSet := not_not.1 hnd
      dsimp only [DepSet] at hdep
      rcases Finset.mem_union.1 hdep with hLR | h0
      · rcases Finset.mem_union.1 hLR with hL | hR
        · obtain ⟨⟨t, j⟩, _, rfl⟩ := Finset.mem_image.1 hL
          rw [hraw_lLab]
          by_cases ht : t = tL
          · subst ht
            simp only [p, ↓reduceDIte]
            exact (htL0 j).symm
          · simp only [p, ht, ↓reduceDIte, labL]
            rw [skipIdx_unskipIdx tL t ht]
        · obtain ⟨⟨t, j⟩, _, rfl⟩ := Finset.mem_image.1 hR
          rw [hraw_rLab]
          by_cases ht : t = tR
          · subst ht
            simp only [p, ↓reduceDIte]
            exact (htR0 j).symm
          · simp only [p, ht, ↓reduceDIte, labR]
            rw [skipIdx_unskipIdx tR t ht]
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 h0
        have hp1 := (henc_valid p).2.2 c
        have hp2 := hpar c
        rw [← Finset.add_sum_erase Finset.univ (fun t => toZ2 (encode p (lPar t c))) (Finset.mem_univ 0)] at hp1
        rw [← Finset.add_sum_erase Finset.univ (fun t => toZ2 (x (lPar t c))) (Finset.mem_univ 0)] at hp2
        have hsumL :
            ∑ t ∈ Finset.univ.erase (0 : Fin q), toZ2 (encode p (lPar t c)) =
            ∑ t ∈ Finset.univ.erase (0 : Fin q), toZ2 (x (lPar t c)) := by
          refine Finset.sum_congr rfl (fun t ht => ?_)
          have hne : t ≠ 0 := (Finset.mem_erase.1 ht).1
          rw [hraw_free p (lPar t c) (hPar_not_dep_L t hne c)]
        have hsumR :
            ∑ t : Fin q, toZ2 (encode p (rPar t c)) =
            ∑ t : Fin q, toZ2 (x (rPar t c)) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [hraw_free p (rPar t c) (hPar_not_dep_R t c)]
        rw [hsumL, hsumR] at hp1
        rw [add_assoc] at hp1 hp2
        exact toZ2_injective ((z2_eq_of_add_eq_zero hp1).trans (z2_eq_of_add_eq_zero hp2).symm)
  let eM : Fin M ≃ Param := (Fintype.equivFinOfCardEq hParamCard).symm
  refine ⟨fun i => encode (eM i), fun i => (eM i).1.1, fun i => (eM i).1.2,
    henc_inj.comp eM.injective, fun i => henc_valid (eM i), ?_, ?_, ?_⟩
  · intro x hv
    obtain ⟨p, hp⟩ := henc_surj x hv
    exact ⟨eM.symm p, by simp [hp]⟩
  · intro i j
    change encode (eM i) (lPos (eM i).1.1 j) = false
    rw [hraw_lLab]
    simp
  · intro i j
    change encode (eM i) (rPos (eM i).1.2 j) = false
    rw [hraw_rLab]
    simp

theorem main_succ (a b h s q' : ℕ) (hn : 0 < a + b) (hs : 0 < s) (hsh : s ≤ h)
    (ha : (q' + 1) * h < a) (hb : (q' + 1 + 1) * h ≤ b) :
    let q := q' + 1
    let n := a + b
    let M := q ^ 2 * (2 ^ s - 1) ^ (2 * (q - 1)) * 2 ^ (n - (2 * q * s + (h - s)))
    let Word := Fin n → Bool
    let Pat := Fin (n - h) → Bool
    let Slot := Fin n × Pat
    let loc := fun k : ℕ => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
    let solutions := fun (tab : Slot → Bool) =>
      (Finset.univ : Finset Word).filter (fun x =>
        ∀ i : Fin n, tab (i, fun j => x (loc (i.val + j.val))) = true)
    ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
      Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
      (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
        base (left i) = false ∧ base (right i) = false) ∧
      ∀ A B : Finset (Fin M), solutions (fun slot =>
        base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
          (A ∩ B).image code := by
  classical
  intro q n M Word Pat Slot loc solutions
  have hh : 0 < h := Nat.lt_of_lt_of_le hs hsh
  have hqa : q * h < a := ha
  have hqb : q * h + h ≤ b := by
    have : (q' + 1 + 1) * h = q * h + h := by dsimp [q]; ring
    omega
  have hn_eq : n = a + b := rfl
  have hhn : h ≤ n := by
    have h1 : h ≤ q * h := Nat.le_mul_of_pos_left h (Nat.succ_pos q')
    omega
  obtain ⟨code, tL, tR, hcode_inj, hcode_valid, hcode_surj, htL_zero, htR_zero⟩ :=
    exists_valid_code a b h s q' hs hsh ha hb
  let lPos := lPosOf a b h s q' hsh ha
  let rPos := rPosOf a b h s q' hsh hb
  let lPar := lParOf a b h s q' hsh ha
  let rPar := rParOf a b h s q' hsh hb
  let win : Word → Fin n → Pat := fun x p j => x (loc (p.val + j.val))
  let leftPort : Fin q → Fin n := fun t =>
    ⟨(t.val + 1) * h, by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      omega⟩
  let rightPort : Fin q → Fin n := fun t =>
    ⟨a + (t.val + 1) * h, by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      omega⟩
  let gAll : Fin n := loc (a + q * h + h)
  have hgAll_ne_left : ∀ t : Fin q, leftPort t ≠ gAll := by
    intro t heq
    have hv : (t.val + 1) * h = (a + q * h + h) % n := congrArg Fin.val heq
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    have hge : h ≤ (t.val + 1) * h := Nat.le_mul_of_pos_left h (Nat.succ_pos t.val)
    by_cases hfull : a + q * h + h = n
    · rw [hfull, Nat.mod_self] at hv; omega
    · have hlt : a + q * h + h < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hv; omega
  have hgAll_ne_right : ∀ t : Fin q, rightPort t ≠ gAll := by
    intro t heq
    have hv : a + (t.val + 1) * h = (a + q * h + h) % n := congrArg Fin.val heq
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    by_cases hfull : a + q * h + h = n
    · rw [hfull, Nat.mod_self] at hv; omega
    · have hlt : a + q * h + h < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hv; omega
  let left : Fin M → Slot := fun i => (leftPort (tL i), win (code i) (leftPort (tL i)))
  let right : Fin M → Slot := fun i => (rightPort (tR i), win (code i) (rightPort (tR i)))
  have hleft_port_eq : ∀ (t : Fin q), (leftPort t).val = (t.val * h + h) % n := by
    intro t
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    have heq : (t.val + 1) * h = t.val * h + h := by ring
    dsimp [leftPort]
    rw [heq, Nat.mod_eq_of_lt (by omega)]
  have hright_port_eq : ∀ (t : Fin q), (rightPort t).val = (a + t.val * h + h) % n := by
    intro t
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    have heq : a + (t.val + 1) * h = a + t.val * h + h := by ring
    dsimp [rightPort]
    rw [heq, Nat.mod_eq_of_lt (by omega)]
  have hwin_eq_left : ∀ (x y : Word) (t : Fin q),
      win x (leftPort t) = win y (leftPort t) →
      ∀ u : Fin n, (u.val < t.val * h ∨ t.val * h + h ≤ u.val) → x u = y u := by
    intro x y t hwin u hu
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    obtain ⟨j, hj⟩ := exists_win_idx hhn (t.val * h) (by omega) u hu
    have hfun := congrFun hwin j
    dsimp only [win, loc] at hfun
    rw [hleft_port_eq t] at hfun
    have hu_eq : (⟨((t.val * h + h) % n + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = u := Fin.ext hj
    rwa [hu_eq] at hfun
  have hwin_eq_right : ∀ (x y : Word) (t : Fin q),
      win x (rightPort t) = win y (rightPort t) →
      ∀ u : Fin n, (u.val < a + t.val * h ∨ a + t.val * h + h ≤ u.val) → x u = y u := by
    intro x y t hwin u hu
    have ht : t.val + 1 ≤ q := t.isLt
    have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
    have hmul' : t.val * h + h = (t.val + 1) * h := by ring
    obtain ⟨j, hj⟩ := exists_win_idx hhn (a + t.val * h) (by omega) u hu
    have hfun := congrFun hwin j
    dsimp only [win, loc] at hfun
    rw [hright_port_eq t] at hfun
    have hu_eq : (⟨((a + t.val * h + h) % n + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = u := Fin.ext hj
    rwa [hu_eq] at hfun
  have hwin_eq_gAll : ∀ (x y : Word),
      win x gAll = win y gAll →
      ∀ u : Fin n, u.val < a + q * h → x u = y u := by
    intro x y hwin u hu
    obtain ⟨j, hj⟩ := exists_win_idx hhn (a + q * h) (by omega) u (Or.inl hu)
    have hfun := congrFun hwin j
    dsimp only [win, loc, gAll] at hfun
    have hu_eq : (⟨((a + q * h + h) % n + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = u := Fin.ext hj
    rwa [hu_eq] at hfun
  have hvalid_of_gAll : ∀ (x y : Word),
      ValidWord a b h s q' hsh ha hb y → win y gAll = win x gAll →
      ValidWord a b h s q' hsh ha hb x := by
    intro x y ⟨⟨tL0, htL0, htLu⟩, ⟨tR0, htR0, htRu⟩, hpar⟩ hwin
    have hagree := hwin_eq_gAll y x hwin
    have hlP : ∀ t j, y (lPos t j) = x (lPos t j) := fun t j => hagree _ (by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      have hmul' : t.val * h + h = (t.val + 1) * h := by ring
      dsimp [lPos, lPosOf]; omega)
    have hrP : ∀ t j, y (rPos t j) = x (rPos t j) := fun t j => hagree _ (by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      have hmul' : t.val * h + h = (t.val + 1) * h := by ring
      dsimp [rPos, rPosOf]; omega)
    have hlC : ∀ t c, y (lPar t c) = x (lPar t c) := fun t c => hagree _ (by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      have hmul' : t.val * h + h = (t.val + 1) * h := by ring
      dsimp [lPar, lParOf]; omega)
    have hrC : ∀ t c, y (rPar t c) = x (rPar t c) := fun t c => hagree _ (by
      have ht : t.val + 1 ≤ q := t.isLt
      have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      have hmul' : t.val * h + h = (t.val + 1) * h := by ring
      dsimp [rPar, rParOf]; omega)
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨tL0, fun j => (hlP tL0 j).symm.trans (htL0 j), fun t ht => htLu t (fun j => (hlP t j).trans (ht j))⟩
    · refine ⟨tR0, fun j => (hrP tR0 j).symm.trans (htR0 j), fun t ht => htRu t (fun j => (hrP t j).trans (ht j))⟩
    · intro c
      have := hpar c
      have h1 : ∑ t : Fin q, toZ2 (x (lPar t c)) = ∑ t : Fin q, toZ2 (y (lPar t c)) :=
        Finset.sum_congr rfl (fun t _ => by rw [hlC t c])
      have h2 : ∑ t : Fin q, toZ2 (x (rPar t c)) = ∑ t : Fin q, toZ2 (y (rPar t c)) :=
        Finset.sum_congr rfl (fun t _ => by rw [hrC t c])
      rw [h1, h2]
      exact this
  have hcode_eq_of_left_win : ∀ (i j : Fin M),
      win (code i) (leftPort (tL j)) = win (code j) (leftPort (tL j)) → i = j := by
    intro i j hwin
    let t := tL j
    have hout := hwin_eq_left (code i) (code j) t hwin
    have ht_eq : tL i = t := by
      by_contra hne
      have hlt_or : ∀ l : Fin s, (lPos (tL i) l).val < t.val * h ∨ t.val * h + h ≤ (lPos (tL i) l).val := by
        intro l
        dsimp [lPos, lPosOf]
        by_cases hlt : (tL i).val < t.val
        · left
          have hle : (tL i).val + 1 ≤ t.val := hlt
          have hmul : ((tL i).val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h hle
          have hmul' : (tL i).val * h + h = ((tL i).val + 1) * h := by ring
          omega
        · right
          have hgt : t.val + 1 ≤ (tL i).val := by
            have : (tL i).val ≠ t.val := fun hv => hne (Fin.ext hv)
            omega
          have hmul : (t.val + 1) * h ≤ (tL i).val * h := Nat.mul_le_mul_right h hgt
          have hmul' : t.val * h + h = (t.val + 1) * h := by ring
          omega
      have hzero_j : ∀ l : Fin s, code j (lPos (tL i) l) = false := fun l =>
        (hout _ (hlt_or l)).symm.trans (htL_zero i l)
      exact hne ((hcode_valid j).1.unique hzero_j (htL_zero j))
    apply hcode_inj
    funext u
    by_cases hin : u.val < t.val * h ∨ t.val * h + h ≤ u.val
    · exact hout u hin
    · have hbounds : t.val * h ≤ u.val ∧ u.val < t.val * h + h := by omega
      let off := u.val - t.val * h
      have hoff_lt : off < h := by omega
      by_cases hs_lt : off < s
      · have hu_eq : u = lPos t ⟨off, hs_lt⟩ := Fin.ext (by dsimp [lPos, lPosOf]; omega)
        rw [hu_eq]
        have hi0 : code i (lPos t ⟨off, hs_lt⟩) = false := by
          rw [← ht_eq]; exact htL_zero i ⟨off, hs_lt⟩
        have hj0 : code j (lPos t ⟨off, hs_lt⟩) = false := htL_zero j ⟨off, hs_lt⟩
        exact hi0.trans hj0.symm
      · let c : Fin (h - s) := ⟨off - s, by omega⟩
        have hu_eq : u = lPar t c := Fin.ext (by dsimp [lPar, lParOf, c]; omega)
        rw [hu_eq]
        have hp1 := (hcode_valid i).2.2 c
        have hp2 := (hcode_valid j).2.2 c
        rw [← Finset.add_sum_erase Finset.univ (fun t' => toZ2 (code i (lPar t' c))) (Finset.mem_univ t)] at hp1
        rw [← Finset.add_sum_erase Finset.univ (fun t' => toZ2 (code j (lPar t' c))) (Finset.mem_univ t)] at hp2
        have hsumL :
            ∑ t' ∈ Finset.univ.erase t, toZ2 (code i (lPar t' c)) =
            ∑ t' ∈ Finset.univ.erase t, toZ2 (code j (lPar t' c)) := by
          refine Finset.sum_congr rfl (fun t' ht' => ?_)
          have hne : t' ≠ t := (Finset.mem_erase.1 ht').1
          congr 1
          apply hout
          dsimp [lPar, lParOf]
          by_cases hlt : t'.val < t.val
          · left
            have hle : t'.val + 1 ≤ t.val := hlt
            have hmul : (t'.val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h hle
            have hmul' : t'.val * h + h = (t'.val + 1) * h := by ring
            omega
          · right
            have hgt : t.val + 1 ≤ t'.val := by
              have : t'.val ≠ t.val := fun hv => hne (Fin.ext hv)
              omega
            have hmul : (t.val + 1) * h ≤ t'.val * h := Nat.mul_le_mul_right h hgt
            have hmul' : t.val * h + h = (t.val + 1) * h := by ring
            omega
        have hsumR :
            ∑ t' : Fin q, toZ2 (code i (rPar t' c)) =
            ∑ t' : Fin q, toZ2 (code j (rPar t' c)) := by
          refine Finset.sum_congr rfl (fun t' _ => ?_)
          congr 1
          apply hout
          right
          dsimp [rPar, rParOf]
          have ht1 : t.val + 1 ≤ q := t.isLt
          have hmul : (t.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht1
          have hmul' : t.val * h + h = (t.val + 1) * h := by ring
          omega
        rw [hsumL, hsumR] at hp1
        rw [add_assoc] at hp1 hp2
        exact toZ2_injective ((z2_eq_of_add_eq_zero hp1).trans (z2_eq_of_add_eq_zero hp2).symm)
  have hcode_eq_of_right_win : ∀ (i j : Fin M),
      win (code i) (rightPort (tR j)) = win (code j) (rightPort (tR j)) → i = j := by
    intro i j hwin
    let t := tR j
    have hout := hwin_eq_right (code i) (code j) t hwin
    have ht_eq : tR i = t := by
      by_contra hne
      have hlt_or : ∀ l : Fin s, (rPos (tR i) l).val < a + t.val * h ∨ a + t.val * h + h ≤ (rPos (tR i) l).val := by
        intro l
        dsimp [rPos, rPosOf]
        by_cases hlt : (tR i).val < t.val
        · left
          have hle : (tR i).val + 1 ≤ t.val := hlt
          have hmul : ((tR i).val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h hle
          have hmul' : (tR i).val * h + h = ((tR i).val + 1) * h := by ring
          omega
        · right
          have hgt : t.val + 1 ≤ (tR i).val := by
            have : (tR i).val ≠ t.val := fun hv => hne (Fin.ext hv)
            omega
          have hmul : (t.val + 1) * h ≤ (tR i).val * h := Nat.mul_le_mul_right h hgt
          have hmul' : t.val * h + h = (t.val + 1) * h := by ring
          omega
      have hzero_j : ∀ l : Fin s, code j (rPos (tR i) l) = false := fun l =>
        (hout _ (hlt_or l)).symm.trans (htR_zero i l)
      exact hne ((hcode_valid j).2.1.unique hzero_j (htR_zero j))
    apply hcode_inj
    funext u
    by_cases hin : u.val < a + t.val * h ∨ a + t.val * h + h ≤ u.val
    · exact hout u hin
    · have hbounds : a + t.val * h ≤ u.val ∧ u.val < a + t.val * h + h := by omega
      let off := u.val - (a + t.val * h)
      have hoff_lt : off < h := by omega
      by_cases hs_lt : off < s
      · have hu_eq : u = rPos t ⟨off, hs_lt⟩ := Fin.ext (by dsimp [rPos, rPosOf]; omega)
        rw [hu_eq]
        have hi0 : code i (rPos t ⟨off, hs_lt⟩) = false := by
          rw [← ht_eq]; exact htR_zero i ⟨off, hs_lt⟩
        have hj0 : code j (rPos t ⟨off, hs_lt⟩) = false := htR_zero j ⟨off, hs_lt⟩
        exact hi0.trans hj0.symm
      · let c : Fin (h - s) := ⟨off - s, by omega⟩
        have hu_eq : u = rPar t c := Fin.ext (by dsimp [rPar, rParOf, c]; omega)
        rw [hu_eq]
        have hp1 := (hcode_valid i).2.2 c
        have hp2 := (hcode_valid j).2.2 c
        rw [← Finset.add_sum_erase Finset.univ (fun t' => toZ2 (code i (rPar t' c))) (Finset.mem_univ t)] at hp1
        rw [← Finset.add_sum_erase Finset.univ (fun t' => toZ2 (code j (rPar t' c))) (Finset.mem_univ t)] at hp2
        have hsumL :
            ∑ t' : Fin q, toZ2 (code i (lPar t' c)) =
            ∑ t' : Fin q, toZ2 (code j (lPar t' c)) := by
          refine Finset.sum_congr rfl (fun t' _ => ?_)
          congr 1
          apply hout
          left
          dsimp [lPar, lParOf]
          have ht1 : t'.val + 1 ≤ q := t'.isLt
          have hmul : (t'.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht1
          have hmul' : t'.val * h + h = (t'.val + 1) * h := by ring
          omega
        have hsumR :
            ∑ t' ∈ Finset.univ.erase t, toZ2 (code i (rPar t' c)) =
            ∑ t' ∈ Finset.univ.erase t, toZ2 (code j (rPar t' c)) := by
          refine Finset.sum_congr rfl (fun t' ht' => ?_)
          have hne : t' ≠ t := (Finset.mem_erase.1 ht').1
          congr 1
          apply hout
          dsimp [rPar, rParOf]
          by_cases hlt : t'.val < t.val
          · left
            have hle : t'.val + 1 ≤ t.val := hlt
            have hmul : (t'.val + 1) * h ≤ t.val * h := Nat.mul_le_mul_right h hle
            have hmul' : t'.val * h + h = (t'.val + 1) * h := by ring
            omega
          · right
            have hgt : t.val + 1 ≤ t'.val := by
              have : t'.val ≠ t.val := fun hv => hne (Fin.ext hv)
              omega
            have hmul : (t.val + 1) * h ≤ t'.val * h := Nat.mul_le_mul_right h hgt
            have hmul' : t.val * h + h = (t.val + 1) * h := by ring
            omega
        rw [hsumL, hsumR] at hp1
        have hp1' : toZ2 (code i (rPar t c)) +
            ((∑ t' : Fin q, toZ2 (code j (lPar t' c))) +
             (∑ t' ∈ Finset.univ.erase t, toZ2 (code j (rPar t' c)))) = 0 := by
          rw [← hp1]; ring
        have hp2' : toZ2 (code j (rPar t c)) +
            ((∑ t' : Fin q, toZ2 (code j (lPar t' c))) +
             (∑ t' ∈ Finset.univ.erase t, toZ2 (code j (rPar t' c)))) = 0 := by
          rw [← hp2]; ring
        exact toZ2_injective ((z2_eq_of_add_eq_zero hp1').trans (z2_eq_of_add_eq_zero hp2').symm)
  have hleft_inj : Function.Injective left := by
    intro i j heq
    have hp : leftPort (tL i) = leftPort (tL j) := congrArg Prod.fst heq
    have hpat : win (code i) (leftPort (tL i)) = win (code j) (leftPort (tL j)) :=
      congrArg Prod.snd heq
    rw [hp] at hpat
    exact hcode_eq_of_left_win i j hpat
  have hright_inj : Function.Injective right := by
    intro i j heq
    have hp : rightPort (tR i) = rightPort (tR j) := congrArg Prod.fst heq
    have hpat : win (code i) (rightPort (tR i)) = win (code j) (rightPort (tR j)) :=
      congrArg Prod.snd heq
    rw [hp] at hpat
    exact hcode_eq_of_right_win i j hpat
  let base : Slot → Bool := fun slot =>
    if slot.1 = gAll then
      decide (∃ i : Fin M, win (code i) gAll = slot.2)
    else
      decide ((∀ i : Fin M, left i ≠ slot) ∧ (∀ i : Fin M, right i ≠ slot))
  refine ⟨code, base, left, right, hcode_inj, hleft_inj, hright_inj, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [left, leftPort]
      have ht : (tL i).val + 1 ≤ q := (tL i).isLt
      have hmul : ((tL i).val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
      omega
    · dsimp [right, rightPort]
      omega
    · dsimp only [base]
      have hne : (left i).1 ≠ gAll := hgAll_ne_left (tL i)
      simp only [hne, ↓reduceIte, decide_eq_false_iff_not, not_and]
      intro h
      exact absurd rfl (h i)
    · dsimp only [base]
      have hne : (right i).1 ≠ gAll := hgAll_ne_right (tR i)
      simp only [hne, ↓reduceIte, decide_eq_false_iff_not, not_and]
      intro _ h
      exact absurd rfl (h i)
  · intro A B
    ext x
    dsimp only [solutions]
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · intro hall
      have hg := hall gAll
      have hg_notL : (gAll, win x gAll) ∉ A.image left := by
        intro hmem
        obtain ⟨j, _, heq⟩ := Finset.mem_image.1 hmem
        exact hgAll_ne_left (tL j) (congrArg Prod.fst heq)
      have hg_notR : (gAll, win x gAll) ∉ B.image right := by
        intro hmem
        obtain ⟨j, _, heq⟩ := Finset.mem_image.1 hmem
        exact hgAll_ne_right (tR j) (congrArg Prod.fst heq)
      have hbase_g : base (gAll, win x gAll) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
        rcases hg with (hb | hA) | hB
        · exact hb
        · exact absurd hA hg_notL
        · exact absurd hB hg_notR
      dsimp only [base] at hbase_g
      simp only [↓reduceIte, decide_eq_true_eq] at hbase_g
      obtain ⟨j0, hj0⟩ := hbase_g
      have hxv : ValidWord a b h s q' hsh ha hb x :=
        hvalid_of_gAll x (code j0) (hcode_valid j0) hj0
      obtain ⟨i, hi⟩ := hcode_surj x hxv
      refine ⟨i, ⟨?_, ?_⟩, hi⟩
      · have hL := hall (left i).1
        have hslot : ((left i).1, fun j => x (loc ((left i).1.val + j.val))) = left i := by
          rw [← hi]
        rw [hslot] at hL
        have hbf : base (left i) = false := by
          dsimp only [base]
          have hne : (left i).1 ≠ gAll := hgAll_ne_left (tL i)
          simp only [hne, ↓reduceIte, decide_eq_false_iff_not, not_and]
          intro h; exact absurd rfl (h i)
        have hnotB : left i ∉ B.image right := by
          intro hmem
          obtain ⟨j, _, heq⟩ := Finset.mem_image.1 hmem
          have h1 : (right j).1.val = (left i).1.val := congrArg (fun s => s.1.val) heq
          dsimp [left, right, leftPort, rightPort] at h1
          have ht : (tL i).val + 1 ≤ q := (tL i).isLt
          have hmul : ((tL i).val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
          omega
        simp only [hbf, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hL
        rcases hL with hA | hB
        · obtain ⟨j, hjA, heq⟩ := Finset.mem_image.1 hA
          rwa [← hleft_inj heq]
        · exact absurd hB hnotB
      · have hR := hall (right i).1
        have hslot : ((right i).1, fun j => x (loc ((right i).1.val + j.val))) = right i := by
          rw [← hi]
        rw [hslot] at hR
        have hbf : base (right i) = false := by
          dsimp only [base]
          have hne : (right i).1 ≠ gAll := hgAll_ne_right (tR i)
          simp only [hne, ↓reduceIte, decide_eq_false_iff_not, not_and]
          intro _ h; exact absurd rfl (h i)
        have hnotA : right i ∉ A.image left := by
          intro hmem
          obtain ⟨j, _, heq⟩ := Finset.mem_image.1 hmem
          have h1 : (left j).1.val = (right i).1.val := congrArg (fun s => s.1.val) heq
          dsimp [left, right, leftPort, rightPort] at h1
          have ht : (tL j).val + 1 ≤ q := (tL j).isLt
          have hmul : ((tL j).val + 1) * h ≤ q * h := Nat.mul_le_mul_right h ht
          omega
        simp only [hbf, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hR
        rcases hR with hA | hB
        · exact absurd hA hnotA
        · obtain ⟨j, hjB, heq⟩ := Finset.mem_image.1 hB
          rwa [← hright_inj heq]
    · rintro ⟨i, ⟨hiA, hiB⟩, rfl⟩ p
      let slot : Slot := (p, fun j => code i (loc (p.val + j.val)))
      change (base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) = true
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases hpg : p = gAll
      · left; left
        dsimp only [base, slot]
        simp only [hpg, ↓reduceIte, decide_eq_true_eq]
        exact ⟨i, rfl⟩
      · by_cases hL : ∃ j : Fin M, left j = slot
        · obtain ⟨j, hj⟩ := hL
          have hp : leftPort (tL j) = p := congrArg Prod.fst hj
          have hpat : win (code j) (leftPort (tL j)) = win (code i) p := congrArg Prod.snd hj
          rw [← hp] at hpat
          have hij : i = j := hcode_eq_of_left_win i j hpat.symm
          subst hij
          left; right
          exact Finset.mem_image.2 ⟨i, hiA, hj⟩
        · by_cases hR : ∃ j : Fin M, right j = slot
          · obtain ⟨j, hj⟩ := hR
            have hp : rightPort (tR j) = p := congrArg Prod.fst hj
            have hpat : win (code j) (rightPort (tR j)) = win (code i) p := congrArg Prod.snd hj
            rw [← hp] at hpat
            have hij : i = j := hcode_eq_of_right_win i j hpat.symm
            subst hij
            right
            exact Finset.mem_image.2 ⟨i, hiB, hj⟩
          · left; left
            dsimp only [base]
            simp only [slot, hpg, ↓reduceIte, decide_eq_true_eq]
            exact ⟨fun j hj => hL ⟨j, hj⟩, fun j hj => hR ⟨j, hj⟩⟩

end PEqualNP.Outside.L_lib_574_aux

theorem PEqualNP.Outside.L_lib_574 :
∀ (a b h s q : Nat) (hn : 0 < a+b), 0 < q → 0 < s → s ≤ h →
  q*h < a → (q+1)*h ≤ b →
  let n := a+b
  let M := q^2 * (2^s-1)^(2*(q-1)) * 2^(n-(2*q*s+(h-s)))
  let Word := Fin n → Bool
  let Pat := Fin (n-h) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code := by
  intro a b h s q hn hq hs hsh ha hb
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact PEqualNP.Outside.L_lib_574_aux.main_succ a b h s q' hn hs hsh ha hb
