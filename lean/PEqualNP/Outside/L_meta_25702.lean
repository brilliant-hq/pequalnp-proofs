import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25702

namespace Labels

theorem boolcore : ∀ x1 x2 x3 x4 x5 x6 y1 y2 y3 : Bool,
    xor (xor x1 x5) (xor x3 x6) = xor y1 y3 → xor (xor x2 x5) (xor x4 x6) = xor y2 y3 →
    xor (xor x1 x2) (xor x1 x2) = xor y1 y2 → x1 = x2 → x3 = x4 := by decide

theorem arith (k a h : ℕ) (h1 : a + 2 ≤ h) (h2 : h ≤ k) :
    h * (2 * 2^(k-h)) ≤ (a+1) * 2^(k-a) := by
  obtain ⟨d, rfl⟩ : ∃ d, h = a + 2 + d := ⟨h - (a+2), by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, k = a + 2 + d + e := ⟨k - (a+2+d), by omega⟩
  have e1 : a + 2 + d + e - (a + 2 + d) = e := by omega
  have e2 : a + 2 + d + e - a = (d + 2) + e := by omega
  rw [e1, e2, pow_add]
  have hd : d + 2 ≤ 2^(d+1) := by
    have := @Nat.lt_two_pow_self (d+1)
    omega
  have h3 : 2^(d+2) = 2 * 2^(d+1) := by ring
  have h4 : (a + 2 + d) * 2 ≤ (a+1) * 2^(d+2) := by
    rw [h3]
    nlinarith [Nat.mul_le_mul_left (a+1) hd, Nat.zero_le (a*d)]
  calc (a+2+d) * (2 * 2^e) = ((a+2+d)*2) * 2^e := by ring
    _ ≤ ((a+1) * 2^(d+2)) * 2^e := Nat.mul_le_mul_right _ h4
    _ = (a+1) * (2^(d+2) * 2^e) := by ring

theorem upper (k a : ℕ) (hk : 2^a ≤ k)
    (π : Equiv.Perm (Fin (2^k))) (K L : Finset (Fin (2^k)))
    (h : ∀ i ∈ K, ∀ j ∈ K,
      xor (xor (i.val.testBit ((π i).val % 2^a)) (j.val.testBit ((π j).val % 2^a)))
          (xor (i.val.testBit ((π j).val % 2^a)) (j.val.testBit ((π i).val % 2^a))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) :
    K.card ≤ (a+1)*2^(k-a) := by
  classical
  have ha2 : a < 2^a := Nat.lt_two_pow_self
  obtain ⟨c, hc⟩ : ∃ c : Fin (2^k) → ℕ, ∀ i, c i = (π i).val % 2^a := ⟨_, fun _ => rfl⟩
  simp only [← hc] at h
  have hcA : ∀ i, c i < 2^a := fun i => by rw [hc]; exact Nat.mod_lt _ (Nat.two_pow_pos a)
  have hTk : K.image c ⊆ Finset.range k := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_range.mpr (lt_of_lt_of_le (hcA i) hk)
  have hTcard : (K.image c).card ≤ k := by simpa using Finset.card_le_card hTk
  have hsum : K.card = ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem c hi)
  have h2k : 2^k = 2^a * 2^(k-a) := by
    rw [← pow_add]; congr 1; omega
  have b1 : ∀ p, (K.filter (fun i => c i = p)).card ≤ 2^(k-a) := by
    intro p
    have hle : (K.filter (fun i => c i = p)).card ≤ (Finset.range (2^(k-a))).card := by
      apply Finset.card_le_card_of_injOn (fun i => (π i).val / 2^a)
      · intro i _
        refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
        show (π i).val / 2^a < 2^(k-a)
        apply Nat.div_lt_of_lt_mul
        rw [← h2k]
        exact (π i).isLt
      · intro i hi j hj e
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        rw [hc] at hi' hj'
        have e' : (π i).val / 2^a = (π j).val / 2^a := e
        have e2 : (π i).val = (π j).val := by
          calc (π i).val = 2^a * ((π i).val / 2^a) + (π i).val % 2^a := (Nat.div_add_mod _ _).symm
            _ = 2^a * ((π j).val / 2^a) + (π j).val % 2^a := by rw [e', hi', hj']
            _ = (π j).val := Nat.div_add_mod _ _
        exact π.injective (Fin.ext e2)
    simpa using hle
  have b2 : ∀ p, (K.filter (fun i => c i = p)).card ≤ 2 * 2^(k - (K.image c).card) := by
    intro p
    have hcard : ((Finset.univ : Finset Bool) ×ˢ (Finset.range k \ K.image c).powerset).card
        = 2 * 2^(k - (K.image c).card) := by
      rw [Finset.card_product, Finset.card_powerset, Finset.card_sdiff_of_subset hTk]
      simp
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun i => (i.val.testBit p,
      (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true)))
    · intro i _
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)
    · intro i hi i' hi' e
      obtain ⟨hiK, hci⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      obtain ⟨hi'K, hci'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi')
      have e1 : i.val.testBit p = i'.val.testBit p := congrArg Prod.fst e
      have e2 : (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true)
          = (Finset.range k \ K.image c).filter (fun q => i'.val.testBit q = true) :=
        congrArg Prod.snd e
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro q
      by_cases hqk : k ≤ q
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hqk)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le i'.isLt (Nat.pow_le_pow_right (by norm_num) hqk))]
      · by_cases hqT : q ∈ K.image c
        · obtain ⟨r, hrK, hrc⟩ := Finset.mem_image.mp hqT
          have h1 := h i hiK r hrK
          have h2 := h i' hi'K r hrK
          have h3 := h i hiK i' hi'K
          rw [hci, hrc] at h1
          rw [hci', hrc] at h2
          rw [hci, hci'] at h3
          exact boolcore _ _ _ _ _ _ _ _ _ h1 h2 h3 e1
        · have hq' : q ∈ Finset.range k \ K.image c :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), hqT⟩
          rw [Bool.eq_iff_iff]
          constructor
          · intro hb
            have hm : q ∈ (Finset.range k \ K.image c).filter (fun q => i.val.testBit q = true) :=
              Finset.mem_filter.mpr ⟨hq', hb⟩
            rw [e2] at hm
            exact (Finset.mem_filter.mp hm).2
          · intro hb
            have hm : q ∈ (Finset.range k \ K.image c).filter (fun q => i'.val.testBit q = true) :=
              Finset.mem_filter.mpr ⟨hq', hb⟩
            rw [← e2] at hm
            exact (Finset.mem_filter.mp hm).2
  rw [hsum]
  by_cases hh : (K.image c).card ≤ a + 1
  · calc ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card
        ≤ (K.image c).card • 2^(k-a) := Finset.sum_le_card_nsmul _ _ _ (fun p _ => b1 p)
      _ = (K.image c).card * 2^(k-a) := smul_eq_mul _ _
      _ ≤ (a+1) * 2^(k-a) := Nat.mul_le_mul_right _ hh
  · calc ∑ p ∈ K.image c, (K.filter (fun i => c i = p)).card
        ≤ (K.image c).card • (2 * 2^(k - (K.image c).card)) :=
          Finset.sum_le_card_nsmul _ _ _ (fun p _ => b2 p)
      _ = (K.image c).card * (2 * 2^(k - (K.image c).card)) := smul_eq_mul _ _
      _ ≤ (a+1) * 2^(k-a) := arith k a _ (by omega) hTcard

private theorem trim (N h : ℕ) (φ : Fin N → Fin N) (hinj : Function.Injective φ)
    (K : Finset (Fin N)) : K.card ≤ (K.filter (fun i => (φ i).val < N-h)).card + h := by
  classical
  have bound : (K.filter (fun i => ¬(φ i).val < N-h)).card ≤ (Finset.range h).card := by
    apply Finset.card_le_card_of_injOn (fun i => (φ i).val - (N-h))
    · intro i hi
      have := (φ i).isLt
      have hm := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      apply Finset.mem_range.mpr
      change (φ i).val - (N-h) < h
      omega
    · intro i hi j hj he
      apply hinj
      apply Fin.ext
      have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
      change (φ i).val - (N-h) = (φ j).val - (N-h) at he
      omega
  rw [Finset.card_range] at bound
  have eq := Finset.card_filter_add_card_filter_not (s := K) (fun i => (φ i).val < N-h)
  omega

private theorem xor_switch (u v w z fi fj gi gj : Bool) :
    xor (xor (xor u (xor fi gi)) (xor v (xor fj gj)))
        (xor (xor w (xor fi gj)) (xor z (xor fj gi))) = xor (xor u v) (xor w z) := by
  decide +revert

theorem switchedBorder (k a h : ℕ) (hk : 2^a ≤ k)
    (H : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool)
    (hbulk : ∀ i j, i.val < 2^k-h → j.val < 2^k-h →
      H i j = xor (i.val.testBit (j.val % 2^a)) (xor (f i) (g j)))
    (π : Equiv.Perm (Fin (2^k))) (K L : Finset (Fin (2^k)))
    (hcut : ∀ i ∈ K, ∀ j ∈ K,
      xor (xor (H i (π i)) (H j (π j))) (xor (H i (π j)) (H j (π i))) =
        xor (decide (i ∈ L)) (decide (j ∈ L))) :
    K.card ≤ (a+1)*2^(k-a) + 2*h := by
  classical
  let R := K.filter (fun i => i.val < 2^k-h)
  let B := R.filter (fun i => (π i).val < 2^k-h)
  have h1 : K.card ≤ R.card + h := trim _ h id Function.injective_id K
  have h2 : R.card ≤ B.card + h := trim _ h π π.injective R
  have h3 : B.card ≤ (a+1)*2^(k-a) := by
    apply upper k a hk π B L
    intro i hi j hj
    obtain ⟨⟨hiK,hir⟩, hic⟩ : (i ∈ K ∧ i.val < 2^k-h) ∧ (π i).val < 2^k-h := by
      simpa only [B,R,Finset.mem_filter] using hi
    obtain ⟨⟨hjK,hjr⟩, hjc⟩ : (j ∈ K ∧ j.val < 2^k-h) ∧ (π j).val < 2^k-h := by
      simpa only [B,R,Finset.mem_filter] using hj
    have hc := hcut i hiK j hjK
    rw [hbulk i (π i) hir hic, hbulk j (π j) hjr hjc, hbulk i (π j) hir hjc,
      hbulk j (π i) hjr hic, xor_switch] at hc
    exact hc
  omega

end Labels

namespace Price
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem oe_getD (n m : ℕ) (u : Fin n) (v : Fin m) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + m
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem oe_len (n m : ℕ) (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  rw [oneEach_pt, List.length_ofFn]

def Agree {U X : Type} (V : U → X → Bool) (K : Finset U) (x y : X) := ∀ i ∈ K, V i x = V i y

theorem roll {U X : Type} [DecidableEq U] (V V' : U → X → Bool) (w : U) (D T : Finset U) (c : ℕ)
    (cd : D.card ≤ c+1) (step : ∀ x y, Agree V D x y → V' w x = V' w y)
    (same : ∀ i, i ≠ w → V' i = V i) :
    ∃ S : Finset U, S.card ≤ T.card+c ∧ ∀ x y, Agree V S x y → Agree V' T x y := by
  classical
  by_cases h : w ∈ T
  · refine ⟨T.erase w ∪ D, ?_, ?_⟩
    · have := Finset.card_union_le (T.erase w) D
      have := Finset.card_erase_add_one h
      omega
    · intro x y ha i hi
      by_cases e : i = w
      · subst i; exact step _ _ (fun z hz => ha _ (Finset.mem_union_right _ hz))
      · rw [same i e]; exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩))
  · refine ⟨T, by omega, ?_⟩
    intro x y ha i hi
    rw [same i (fun he => h (he ▸ hi))]; exact ha _ hi

theorem retreat {U X : Type} [DecidableEq U] (V : ℕ → U → X → Bool) (cost : ℕ → ℕ) (l : ℕ)
    (step : ∀ j < l, ∀ T : Finset U, ∃ S : Finset U, S.card ≤ T.card+cost j ∧
      ∀ x y, Agree (V j) S x y → Agree (V (j+1)) T x y) (T : Finset U) :
    ∃ S : Finset U, S.card ≤ T.card + ∑ j ∈ Finset.range l, cost j ∧
      ∀ x y, Agree (V 0) S x y → Agree (V l) T x y := by
  induction l generalizing T with
  | zero => exact ⟨T, by simp, fun _ _ h => h⟩
  | succ l ih =>
    obtain ⟨A,ha,hA⟩ := step l (by omega) T
    obtain ⟨B,hb,hB⟩ := ih (fun j hj => step j (by omega)) A
    exact ⟨B,by rw [Finset.sum_range_succ]; omega, fun x y h => hA _ _ (hB x y h)⟩

def raw {N : ℕ} (C : Circuit) (j i : ℕ) (z : Fin N × Fin N) : Bool :=
  (W (C.gates.take j) (oneEach z.1 z.2)).getD i false

lemma raw0 {N} (C : Circuit) (j i : ℕ) (z : Fin N × Fin N) (hi : i < N+N) :
    raw C j i z = decide (i = z.1.val ∨ i = N+z.2.val) := by
  rw [raw, W_prefix _ _ _ (by rw [oe_len]; exact hi), Bool.eq_iff_iff]
  simp only [oe_getD, decide_eq_true_eq]

lemma atrow {N} (C : Circuit) (j : ℕ) (r : Fin N) (z : Fin N × Fin N) :
    raw C j r.val z = decide (r = z.1) := by
  rw [raw0 _ _ _ _ (by omega)]
  simp only [decide_eq_decide, Fin.ext_iff]; omega

lemma atcol {N} (C : Circuit) (j : ℕ) (r : Fin N) (z : Fin N × Fin N) :
    raw C j (N+r.val) z = decide (r = z.2) := by
  rw [raw0 _ _ _ _ (by omega)]
  simp only [decide_eq_decide, Fin.ext_iff]; omega

lemma rawSucc {N} (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (z : Fin N × Fin N) :
    raw C (j+1) i z = if i = N+N+j then C.gates[j].op.eval (C.gates[j].inputs.map (fun a => raw C j a z))
        else raw C j i z := by
  simp only [raw, List.take_succ_eq_append_getElem hj,W_snoc_getD,oe_len,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]

lemma swapOp (o : GateOp) (h : o ≠ .not) (x y : Bool) : o.eval [x,y] = o.eval [y,x] := by
  cases o <;> cases x <;> cases y <;> simp_all [GateOp.eval]

def func (o : GateOp) (x y : Bool) : Bool := match o with
  | .not => false
  | a => a.eval [x,y]

lemma funcSym (o : GateOp) (x y : Bool) : func o x y = func o y x := by
  cases o <;> cases x <;> cases y <;> rfl

def V {N t} (C : Circuit) (row col : Fin t → Fin N) (F : Fin t → Bool → Bool → Bool)
    (j : ℕ) (i : ℕ ⊕ Fin t) (z : Fin N × Fin N) : Bool := match i with
  | .inl w => raw C j w z
  | .inr e => F e (decide (row e = z.1)) (decide (col e = z.2))

noncomputable section
open Classical
variable {N t : ℕ} (C : Circuit) (row col : Fin t → Fin N) (idx : Fin t → Fin C.gates.length)

def fs (e : Fin t) := func C.gates[(idx e).val].op

def cost (j : ℕ) := if ∃ e, (idx e).val = j then 0 else
  if h : j < C.gates.length then if C.gates[j].inputs.length = 2 then 1 else 0 else 0

lemma chooseIndices (hr : Function.Injective row)
    (hpair : ∀ e, ∃ g ∈ C.gates, g.inputs = [(row e).val,N+(col e).val] ∨
        g.inputs = [N+(col e).val,(row e).val]) :
    ∃ idx : Fin t → Fin C.gates.length, Function.Injective idx ∧
      ∀ e, C.gates[(idx e).val].inputs = [(row e).val,N+(col e).val] ∨
        C.gates[(idx e).val].inputs = [N+(col e).val,(row e).val] := by
  have ex (e : Fin t) : ∃ j : Fin C.gates.length,
      C.gates[j.val].inputs = [(row e).val,N+(col e).val] ∨ C.gates[j.val].inputs = [N+(col e).val,(row e).val] := by
    obtain ⟨g,hg,h⟩ := hpair e
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hg
    exact ⟨⟨i,hi⟩,he ▸ h⟩
  choose ix hix using ex
  refine ⟨ix,?_,hix⟩
  intro a b eq
  have ha := hix a
  rw [eq] at ha
  have h1 := (row a).isLt
  have h2 := (row b).isLt
  apply hr
  apply Fin.ext
  rcases ha with ha | ha <;> rcases hix b with hb | hb <;> rw [ha] at hb <;> simp only [List.cons.injEq, and_true] at hb <;> omega

private def priceIndicator (gs : List Gate) (j : ℕ) : ℕ :=
  if h : j < gs.length then if gs[j].inputs.length=2 then 1 else 0 else 0

private theorem priceIndicatorCount (gs : List Gate) :
    ∑ j ∈ Finset.range gs.length, priceIndicator gs j = gs.countP (fun g => g.inputs.length == 2) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons,Finset.sum_range_succ',List.countP_cons]
    have eq (i : ℕ) : priceIndicator (g::gs) (i+1) = priceIndicator gs i := by
      by_cases h : i < gs.length <;> simp [priceIndicator,h]
    simp_rw [eq]
    rw [ih]
    by_cases hg : g.inputs.length=2 <;> simp [priceIndicator,hg]

lemma cost_identity (inj : Function.Injective idx)
    (shape : ∀ e, C.gates[(idx e).val].inputs = [(row e).val,N+(col e).val] ∨
        C.gates[(idx e).val].inputs = [N+(col e).val,(row e).val]) :
    (∑ j ∈ Finset.range C.gates.length, cost C idx j) + t = C.gates.countP (fun g => g.inputs.length == 2) := by
  let I := Finset.univ.image (fun e : Fin t => (idx e).val)
  have mem (j : ℕ) : j ∈ I ↔ ∃ e, (idx e).val = j := by simp [I]
  have cardI : I.card = t := by
    have injv : Function.Injective (fun e => (idx e).val) := fun _ _ h => inj (Fin.ext h)
    dsimp [I]; rw [Finset.card_image_of_injective _ injv]; simp
  have small : I ⊆ Finset.range C.gates.length := by
    intro j hj; obtain ⟨e,rfl⟩ := (mem _).mp hj; exact Finset.mem_range.mpr (idx e).isLt
  have marks : (∑ j ∈ Finset.range C.gates.length, if j ∈ I then 1 else 0) = t := by
    simpa [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr small] using cardI
  rw [← priceIndicatorCount]
  conv_lhs => rhs; rw [← marks]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j ∈ I
  · obtain ⟨e,he⟩ := (mem _).mp h
    subst j
    have len : C.gates[(idx e).val].inputs.length=2 := by rcases shape e with ha|ha <;> rw [ha] <;> rfl
    simp [cost,priceIndicator,(idx e).isLt,h,len,show ∃ u, (idx u).val = (idx e).val from ⟨e,rfl⟩]
  · simp [cost,priceIndicator,h,mt (mem _).mpr h]

lemma funcOk {o : GateOp} (ho : o ≠ .not) (x y : Bool) : func o x y = o.eval [x,y] := by
  cases o <;> simp_all [func]

theorem backStep
    (shape : ∀ e, C.gates[(idx e).val].inputs = [(row e).val,N+(col e).val] ∨
        C.gates[(idx e).val].inputs = [N+(col e).val,(row e).val])
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (T : Finset (ℕ ⊕ Fin t)) :
    ∃ S : Finset (ℕ ⊕ Fin t), S.card ≤ T.card+cost C idx j ∧
      ∀ x y, Agree (V C row col (fs C idx) j) S x y → Agree (V C row col (fs C idx) (j+1)) T x y := by
  let v := V C row col (fs C idx)
  let w : ℕ ⊕ Fin t := .inl (N+N+j)
  have same (i) (hi : i ≠ w) : v (j+1) i = v j i := by
    cases i with
    | inr => rfl
    | inl a => funext z; exact (rawSucc C j a hj z).trans (if_neg (fun he => hi (congrArg Sum.inl he)))
  have out (z) : v (j+1) w z = C.gates[j].op.eval (C.gates[j].inputs.map fun a => raw C j a z) :=
    (rawSucc C j _ hj z).trans (if_pos rfl)
  by_cases hit : ∃ e, (idx e).val = j
  · obtain ⟨e,he⟩ := hit
    have inp := shape e
    simp only [he] at inp
    let g := C.gates[j]
    by_cases hn : g.op = .not
    · rcases inp with h | h
      · apply roll _ _ w {Sum.inl (row e).val} T _ (by simp) _ same
        intro x y ha
        have ha' := ha _ (Finset.mem_singleton_self _)
        simpa only [out,h,List.map_cons,List.map_nil,show C.gates[j].op = .not from hn, GateOp.eval,List.headD,v,V] using congrArg Bool.not ha'
      · apply roll _ _ w {Sum.inl (N+(col e).val)} T _ (by simp) _ same
        intro x y ha
        have ha' := ha _ (Finset.mem_singleton_self _)
        simpa only [out,h,List.map_cons,List.map_nil,show C.gates[j].op = .not from hn, GateOp.eval,List.headD,v,V] using congrArg Bool.not ha'
    · apply roll _ _ w {Sum.inr e} T _ (by simp) _ same
      intro x y ha
      have eqz (z) : v (j+1) w z = v j (.inr e) z := by
        rw [out]; change _ = func C.gates[(idx e).val].op _ _
        simp only [he]
        rw [funcOk (show C.gates[j].op ≠ .not from hn)]
        rcases inp with h | h
        · simp only [h,List.map_cons,List.map_nil,atrow,atcol]
        · simp only [h,List.map_cons,List.map_nil,atrow,atcol]; exact swapOp _ hn _ _
      rw [eqz,eqz]; exact ha _ (Finset.mem_singleton_self _)
  · let D := C.gates[j].inputs.toFinset.image (Sum.inl : ℕ → ℕ ⊕ Fin t)
    apply roll _ _ w D T _ _ _ same
    · have h1 := Finset.card_image_le (s := C.gates[j].inputs.toFinset) (f := (Sum.inl : ℕ → ℕ ⊕ Fin t))
      have h2 := List.toFinset_card_le C.gates[j].inputs
      have h3 := fan _ (List.getElem_mem hj)
      simp only [cost,if_neg hit,dif_pos hj]; dsimp only [D]; split <;> omega
    · intro x y ha; rw [out,out]; congr 1; apply List.map_congr_left
      intro i hi; exact ha (Sum.inl i) (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hi))

theorem support
    (shape : ∀ e, C.gates[(idx e).val].inputs = [(row e).val,N+(col e).val] ∨
        C.gates[(idx e).val].inputs = [N+(col e).val,(row e).val])
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (cap : (∑ j ∈ Finset.range C.gates.length, cost C idx j) + t ≤ C.gates.countP (fun g => g.inputs.length == 2))
    (H : Fin N → Fin N → Bool) (hr : Represents H C) :
    ∃ (S : Finset (ℕ ⊕ Fin t)) (F : Fin t → Bool → Bool → Bool),
      S.card + t ≤ C.gates.countP (fun g => g.inputs.length == 2) + 1 ∧
      (∀ e x y, F e x y = F e y x) ∧
      ∀ x y : Fin N × Fin N, (∀ i ∈ S, (match i with
        | .inl a => (oneEach x.1 x.2).getD a false = (oneEach y.1 y.2).getD a false
        | .inr e => F e (decide (row e = x.1)) (decide (col e = x.2)) =
                    F e (decide (row e = y.1)) (decide (col e = y.2)))) → H x.1 x.2 = H y.1 y.2 := by
  let T : Finset (ℕ ⊕ Fin t) := {Sum.inl C.output}
  obtain ⟨S,hs,he⟩ := retreat (V C row col (fs C idx)) (cost C idx) C.gates.length
    (backStep C row col idx shape fan) T
  have ht : T.card = 1 := Finset.card_singleton _
  refine ⟨S,fs C idx,by omega, fun e x y => funcSym _ _ _, ?_⟩
  intro x y h
  have h0 : Agree (V C row col (fs C idx) 0) S x y := by
    intro i hi; cases i <;> exact h _ hi
  have hh := he x y h0 (Sum.inl C.output) (Finset.mem_singleton_self _)
  change raw C C.gates.length C.output x = raw C C.gates.length C.output y at hh
  simp only [raw,List.take_length] at hh
  exact (hr x.1 x.2).symm.trans (hh.trans (hr y.1 y.2))

def encode {N t : ℕ} : ((Fin N ⊕ Fin N) ⊕ Fin t) → (ℕ ⊕ Fin t)
  | .inl (.inl i) => .inl i.val
  | .inl (.inr j) => .inl (N+j.val)
  | .inr e => .inr e

theorem encodeInj {N t : ℕ} : Function.Injective (@encode N t) := by
  rintro ((i|j)|e) ((a|b)|k) h <;> simp_all [encode, Fin.ext_iff] <;> omega

theorem separated
    (shape : ∀ e, C.gates[(idx e).val].inputs = [(row e).val,N+(col e).val] ∨
        C.gates[(idx e).val].inputs = [N+(col e).val,(row e).val])
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (cap : (∑ j ∈ Finset.range C.gates.length, cost C idx j) + t ≤ C.gates.countP (fun g => g.inputs.length == 2))
    (H : Fin N → Fin N → Bool) (hr : Represents H C) :
    ∃ (R S : Finset (Fin N)) (A : Finset (Fin t)) (F : Fin t → Bool → Bool → Bool),
      R.card+S.card+A.card+t ≤ C.gates.countP (fun g => g.inputs.length == 2) + 1 ∧
      (∀ e x y, F e x y = F e y x) ∧
      ∀ x y x' y', (∀ i∈R, decide (i=x) = decide (i=x')) →
        (∀ j∈S, decide (j=y) = decide (j=y')) →
        (∀ e∈A, F e (decide (row e=x)) (decide (col e=y)) =
                    F e (decide (row e=x')) (decide (col e=y'))) → H x y = H x' y' := by
  obtain ⟨T,F,ct,hs,h⟩ := support C row col idx shape fan cap H hr
  let R := Finset.univ.filter (fun i : Fin N => Sum.inl i.val ∈ T)
  let S := Finset.univ.filter (fun j : Fin N => Sum.inl (N+j.val) ∈ T)
  let A := Finset.univ.filter (fun e : Fin t => Sum.inr e ∈ T)
  have sub : ((R.disjSum S).disjSum A).image encode ⊆ T := by
    intro z hz; obtain ⟨((i|j)|e),hm,rfl⟩ := Finset.mem_image.mp hz
    · simpa [R,encode] using hm
    · simpa [S,encode] using hm
    · simpa [A,encode] using hm
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ encodeInj] at hc
  simp only [Finset.card_disjSum] at hc
  refine ⟨R,S,A,F,by omega,hs,?_⟩
  intro x y x' y' hx hy he
  apply h (x,y) (x',y'); intro w hw; cases w with
  | inr e => exact he e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
  | inl a =>
    by_cases ha : a < N
    · let i : Fin N := ⟨a,ha⟩
      have h1 := hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
      change (oneEach x y).getD a false = (oneEach x' y').getD a false
      rw [Bool.eq_iff_iff,oe_getD,oe_getD]; simp only [decide_eq_decide,Fin.ext_iff] at h1
      change (a = x.val ↔ a = x'.val) at h1; omega
    · by_cases hb : a < N+N
      · let i : Fin N := ⟨a-N,by omega⟩
        have h2 : N+i.val=a := by dsimp [i]; omega
        have h1 := hy i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [h2] using hw⟩)
        change (oneEach x y).getD a false = (oneEach x' y').getD a false
        rw [Bool.eq_iff_iff,oe_getD,oe_getD]; simp only [decide_eq_decide,Fin.ext_iff] at h1
        change (a-N = y.val ↔ a-N = y'.val) at h1; omega
      · change (oneEach x y).getD a false = (oneEach x' y').getD a false
        rw [Bool.eq_iff_iff,oe_getD,oe_getD]; omega

end
end Price
namespace Labels
open Finset

private lemma oneMissing {N : ℕ} (U : Finset (Fin N))
    (uniq : ∀ x ∉ U, ∀ y ∉ U, x = y) : N ≤ U.card + 1 := by
  classical
  have small : (univ \ U).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    exact uniq x (mem_sdiff.mp hx).2 y (mem_sdiff.mp hy).2
  simp only [card_sdiff, inter_univ, card_univ, Fintype.card_fin] at small
  omega

private lemma oneShore {N t : ℕ} (R : Finset (Fin N)) (r : Fin t → Fin N) (A : Finset (Fin t))
    (uniq : ∀ x ∉ R, ∀ z ∉ R, (∀ e ∈ A, r e ≠ x) → (∀ e ∈ A, r e ≠ z) → x=z) :
    N ≤ R.card + (A.filter (fun e => r e ∉ R)).card + 1 := by
  classical
  let P := A.filter (fun e => r e ∉ R)
  have miss (x) (hx : x ∉ R ∪ P.image r) : x ∉ R ∧ ∀ e ∈ A, r e ≠ x := by
    have hr : x ∉ R := fun h => hx (mem_union_left _ h)
    refine ⟨hr, ?_⟩
    rintro e he rfl
    exact hx (mem_union_right _ (mem_image_of_mem r (mem_filter.mpr ⟨he,hr⟩)))
  have q := oneMissing (R ∪ P.image r) (fun x hx y hy =>
    uniq x (miss x hx).1 y (miss y hy).1 (miss x hx).2 (miss y hy).2)
  have le1 := Finset.card_union_le R (P.image r)
  have le2 := Finset.card_image_le (s := P) (f := r)
  change N ≤ R.card + P.card + 1
  omega

theorem supportCut {N t : ℕ} (H : Fin N → Fin N → Bool)
    (hinjr : Function.Injective H) (hinjc : Function.Injective (fun y x => H x y))
    (r c : Fin t → Fin N) (ir : Function.Injective r) (ic : Function.Injective c)
    (R S : Finset (Fin N)) (A : Finset (Fin t)) (F : Fin t → Bool → Bool → Bool)
    (symm : ∀ e ∈ A, ∀ u v, F e u v = F e v u)
    (det : ∀ (x y x' y' : Fin N),
      (∀ i ∈ R, decide (i=x) = decide (i=x')) →
      (∀ j ∈ S, decide (j=y) = decide (j=y')) →
      (∀ e ∈ A, F e (decide (r e=x)) (decide (c e=y)) =
                 F e (decide (r e=x')) (decide (c e=y'))) → H x y = H x' y') :
    ∃ (π : Equiv.Perm (Fin N)) (K L : Finset (Fin N)),
      2*N ≤ R.card + S.card + A.card + K.card + 2 ∧
      ∀ i ∈ K, ∀ j ∈ K, xor (xor (H i (π i)) (H j (π j)))
        (xor (H i (π j)) (H j (π i))) = xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  classical
  let P := A.filter (fun e => r e ∉ R)
  let Q := A.filter (fun e => c e ∉ S)
  let D := P ∩ Q
  have hR : N ≤ R.card + P.card + 1 := by
    apply oneShore
    intro x hx z hz mx mz
    apply hinjr
    funext y
    apply det
    · intro i hi; have h1 : i ≠ x := fun eq => hx (eq ▸ hi)
      have h2 : i ≠ z := fun eq => hz (eq ▸ hi)
      simp [h1,h2]
    · simp
    · intro e he; simp [mx e he,mz e he]
  have hS : N ≤ S.card + Q.card + 1 := by
    apply oneShore
    intro y hy z hz my mz
    apply hinjc
    funext x
    apply det
    · simp
    · intro i hi; have h1 : i ≠ y := fun eq => hy (eq ▸ hi)
      have h2 : i ≠ z := fun eq => hz (eq ▸ hi)
      simp [h1,h2]
    · intro e he; simp [my e he,mz e he]
  have unionLe : (P ∪ Q).card ≤ A.card := by
    apply card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have sumEq := Finset.card_union_add_card_inter P Q
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair r c ir ic
  let K := D.image r
  let L := univ.filter (fun x => H x (π x) = true)
  refine ⟨π,K,L,?_,?_⟩
  · have hK : K.card = (P ∩ Q).card := Finset.card_image_of_injective _ ir
    omega
  · intro i hi j hj
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hj
    have huR := (mem_filter.mp (mem_inter.mp hu).1).2
    have huS := (mem_filter.mp (mem_inter.mp hu).2).2
    have hvR := (mem_filter.mp (mem_inter.mp hv).1).2
    have hvS := (mem_filter.mp (mem_inter.mp hv).2).2
    have swap : H (r u) (c v) = H (r v) (c u) := by
      apply det
      · intro i hi; have h1 : i ≠ r u := fun eq => huR (eq ▸ hi)
        have h2 : i ≠ r v := fun eq => hvR (eq ▸ hi)
        simp [h1,h2]
      · intro j hj; have h1 : j ≠ c v := fun eq => hvS (eq ▸ hj)
        have h2 : j ≠ c u := fun eq => huS (eq ▸ hj)
        simp [h1,h2]
      · intro e he; simpa only [ir.eq_iff, ic.eq_iff] using symm e he (decide (e=u)) (decide (e=v))
    simp [L,hπ,swap]

end Labels

namespace Price
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem matchingPrice {N t : ℕ} (H : Fin N → Fin N → Bool) (rr : Function.Injective H)
    (cc : Function.Injective (fun j i => H i j)) (C : Circuit)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (rep : Represents H C)
    (row col : Fin t → Fin N) (ir : Function.Injective row) (ic : Function.Injective col)
    (pair : ∀ e, ∃ p ∈ C.gates, p.inputs = [(row e).val,N+(col e).val] ∨
        p.inputs = [N+(col e).val,(row e).val]) :
    ∃ (π : Equiv.Perm (Fin N)) (K L : Finset (Fin N)),
      2*N+t ≤ C.gates.countP (fun g => g.inputs.length == 2) + K.card + 3 ∧
      ∀ i ∈ K, ∀ j ∈ K, xor (xor (H i (π i)) (H j (π j)))
        (xor (H i (π j)) (H j (π i))) = xor (decide (i ∈ L)) (decide (j ∈ L)) := by
  obtain ⟨idx,ij,sh⟩ := chooseIndices C row col ir pair
  have cap := (cost_identity C row col idx ij sh).le
  obtain ⟨R,S,A,F,bd,fs,det⟩ := separated C row col idx sh fan cap H rep
  obtain ⟨π,K,L,hb,cut⟩ := Labels.supportCut H rr cc row col ir ic R S A F (fun e _ => fs e) det
  exact ⟨π,K,L,by omega,cut⟩

end Price

namespace Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def literalInput {n : ℕ} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ List.ofFn (fun i => !x i)

def allowed (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem allowed_append {g h : List Gate} (hg : allowed g) (hh : allowed h) :
    allowed (g ++ h) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hg t ht
  · exact hh t ht

def values (gs : List Gate) (input : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires input

theorem values_append (g h : List Gate) (input : List Bool) :
    values (g ++ h) input = values h (values g input) := by
  exact List.foldl_append

theorem values_length (gs : List Gate) (input : List Bool) :
    (values gs input).length = input.length + gs.length := by
  induction gs generalizing input with
  | nil => simp [values, Circuit.wires]
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons, List.length_cons, ih, List.length_append, List.length_nil]
    omega

theorem values_preserve (gs : List Gate) (input : List Bool) {i : ℕ}
    (hi : i < input.length) : (values gs input).getD i false = input.getD i false := by
  induction gs generalizing input with
  | nil => rfl
  | cons g gs ih =>
    unfold values Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def atWire {n : ℕ} (gs : List Gate) (i : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  i < n + n + gs.length ∧ ∀ x, (values gs (literalInput x)).getD i false = f x

theorem atWire_extend {n : ℕ} {gs : List Gate} (h : List Gate)
    {i : ℕ} {f : (Fin n → Bool) → Bool} (hf : atWire gs i f) : atWire (gs ++ h) i f := by
  refine ⟨by have := hf.1; simp; omega, fun x => ?_⟩
  rw [values_append, values_preserve]
  · exact hf.2 x
  · simpa [values_length, literalInput] using hf.1

theorem atWire_snoc {n : ℕ} (gs : List Gate) (g : Gate) :
    atWire (gs ++ [g]) (n + n + gs.length) (fun x : Fin n → Bool =>
      g.op.eval (g.inputs.map (fun i => (values gs (literalInput x)).getD i false))) := by
  refine ⟨by simp, fun x => ?_⟩
  have hlen : (values gs (literalInput x)).length = n + n + gs.length := by
    simp [values_length, literalInput]
  rw [values_append, ← hlen]
  change (values [g] (values gs (literalInput x))).getD (values gs (literalInput x)).length
    false = g.op.eval (g.inputs.map fun i => (values gs (literalInput x)).getD i false)
  generalize values gs (literalInput x) = l
  simp only [values, Circuit.wires, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp

theorem andWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.and, [i,j]⟩]) (n+n+gs.length) (fun x => f x && g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.and, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, hf.2 x, hg.2 x]

theorem orWire {n : ℕ} {gs : List Gate} {i j : ℕ}
    {f g : (Fin n → Bool) → Bool} (hf : atWire gs i f) (hg : atWire gs j g) :
    atWire (gs ++ [⟨GateOp.or, [i,j]⟩]) (n+n+gs.length) (fun x => f x || g x) := by
  refine ⟨(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).1, fun x => ?_⟩
  rw [(atWire_snoc (n := n) gs ⟨GateOp.or, [i,j]⟩).2 x]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, hf.2 x, hg.2 x]

theorem multiplex {n : ℕ} {gs : List Gate} {i j u v : ℕ}
    {s f g : (Fin n → Bool) → Bool} (hs : atWire gs i s)
    (hn : atWire gs j (fun x => !s x)) (hf : atWire gs u f) (hg : atWire gs v g) :
    ∃ h w, allowed h ∧ h.length = 3 ∧ atWire (gs ++ h) w (fun x => if s x then g x else f x) := by
  let a : Gate := ⟨GateOp.and, [j,u]⟩
  let b : Gate := ⟨GateOp.and, [i,v]⟩
  let c : Gate := ⟨GateOp.or, [n+n+gs.length, n+n+(gs ++ [a]).length]⟩
  have ha := andWire hn hf
  have hb := andWire (atWire_extend [a] hs) (atWire_extend [a] hg)
  have hc := orWire (atWire_extend [b] ha) hb
  refine ⟨[a,b,c], n+n+((gs ++ [a]) ++ [b]).length, ?_, rfl, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp [a,b,c]
  · rw [List.append_assoc, List.append_assoc] at hc
    refine ⟨hc.1, fun x => ?_⟩
    change (values (gs ++ ([a] ++ ([b] ++ [c]))) (literalInput x)).getD
      (n + n + (gs ++ [a] ++ [b]).length) false = _
    rw [hc.2 x]
    cases hsx : s x <;> simp [hsx]

def Build {n : ℕ} (f : (Fin n → Bool) → Bool) (b : ℕ) : Prop :=
  ∀ gs : List Gate, ∃ h w, allowed h ∧ h.length ≤ b ∧ atWire (gs ++ h) w f

theorem bPos {n : ℕ} (i : Fin n) : Build (fun x => x i) 0 := by
  have h : atWire [] i.val (fun x => x i) := by
    have hi := i.isLt
    refine ⟨by simp; omega, fun x => ?_⟩
    simp only [values, Circuit.wires, List.foldl_nil, literalInput, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hi])]
    simp [hi]
  intro gs
  exact ⟨[], i.val, by simp [allowed], by simp, by simpa using atWire_extend gs h⟩

theorem bNeg {n : ℕ} (i : Fin n) : Build (fun x => !x i) 0 := by
  have h : atWire [] (n+i.val) (fun x => !x i) := by
    have hi := i.isLt
    refine ⟨by simp, fun x => ?_⟩
    simp only [values, Circuit.wires, List.foldl_nil, literalInput, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp)]
    simp [hi]
  intro gs
  exact ⟨[], n+i.val, by simp [allowed], by simp, by simpa using atWire_extend gs h⟩

theorem bConst {n : ℕ} (v : Bool) : Build (fun _ : Fin n → Bool => v) 1 := by
  intro gs
  cases v
  · let g : Gate := ⟨.or, []⟩
    exact ⟨[g], _, by simp [allowed, g], by simp, by simpa [g, GateOp.eval] using atWire_snoc (n := n) gs g⟩
  · let g : Gate := ⟨.and, []⟩
    exact ⟨[g], _, by simp [allowed, g], by simp, by simpa [g, GateOp.eval] using atWire_snoc (n := n) gs g⟩

theorem bMono {n a b : ℕ} {f : (Fin n → Bool) → Bool} (hf : Build f a) (h : a ≤ b) : Build f b := by
  intro gs
  obtain ⟨l, w, hl, hlen, hw⟩ := hf gs
  exact ⟨l, w, hl, hlen.trans h, hw⟩

theorem bAnd {n a b : ℕ} {f g : (Fin n → Bool) → Bool}
    (hf : Build f a) (hg : Build g b) : Build (fun x => f x && g x) (a+b+1) := by
  intro gs
  obtain ⟨l, u, hl, hlen, hu⟩ := hf gs
  obtain ⟨r, v, hr, hrlen, hv⟩ := hg (gs ++ l)
  let t : Gate := ⟨.and, [u,v]⟩
  have hw := andWire (atWire_extend r hu) hv
  refine ⟨l ++ r ++ [t], n+n+(gs ++ l ++ r).length, allowed_append (allowed_append hl hr) (by simp [allowed, t]), ?_, ?_⟩
  · simp; omega
  · simpa only [List.append_assoc, t] using hw

theorem bOr {n a b : ℕ} {f g : (Fin n → Bool) → Bool}
    (hf : Build f a) (hg : Build g b) : Build (fun x => f x || g x) (a+b+1) := by
  intro gs
  obtain ⟨l, u, hl, hlen, hu⟩ := hf gs
  obtain ⟨r, v, hr, hrlen, hv⟩ := hg (gs ++ l)
  let t : Gate := ⟨.or, [u,v]⟩
  have hw := orWire (atWire_extend r hu) hv
  refine ⟨l ++ r ++ [t], n+n+(gs ++ l ++ r).length, allowed_append (allowed_append hl hr) (by simp [allowed, t]), ?_, ?_⟩
  · simp; omega
  · simpa only [List.append_assoc, t] using hw

theorem bMux {n a b : ℕ} {f g : (Fin n → Bool) → Bool} (i : Fin n)
    (hf : Build f a) (hg : Build g b) :
    Build (fun x => if x i then g x else f x) (a+b+3) := by
  intro gs
  obtain ⟨l, u, hl, hlen, hu⟩ := hf gs
  obtain ⟨r, v, hr, hrlen, hv⟩ := hg (gs ++ l)
  let p := gs ++ l ++ r
  obtain ⟨s, j, _, hs, hj⟩ := bPos i p
  have hs' : s = [] := List.length_eq_zero_iff.mp (by omega)
  obtain ⟨sn, jn, _, hsn, hjn⟩ := bNeg i p
  have hsn' : sn = [] := List.length_eq_zero_iff.mp (by omega)
  simp only [hs', List.append_nil] at hj
  simp only [hsn', List.append_nil] at hjn
  obtain ⟨t,w,ht,htlen,hw⟩ := multiplex hj hjn (atWire_extend r hu) hv
  exact ⟨l ++ r ++ t, w, allowed_append (allowed_append hl hr) ht, by simp; omega,
    by simpa only [p, List.append_assoc] using hw⟩

theorem bSound {n b : ℕ} {f : (Fin n → Bool) → Bool} (hf : Build f b) : HasLitSize n f b := by
  obtain ⟨h,w,hv,hlen,hw⟩ := hf []
  simp only [List.nil_append] at hw
  exact ⟨⟨h,w⟩, hv, hlen, hw.2⟩

end Upper

namespace Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem muxTableLt {m : ℕ} (x : Fin m → Bool) : tableIndex x < 2 ^ m := by
  have key : ∀ m : ℕ, ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega
  unfold tableIndex
  calc ∑ i : Fin m, (if x i = true then 2 ^ (i : ℕ) else 0) ≤ ∑ i : Fin m, 2 ^ (i : ℕ) :=
        Finset.sum_le_sum fun i _ => by split <;> simp
    _ < 2 ^ m := by rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) m]; exact key m

theorem muxTableSucc {m : ℕ} (x : Fin (m + 1) → Bool) :
    tableIndex x = (if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x) := by
  unfold tableIndex
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  have h2 : (∑ i : Fin m, if x i.succ = true then 2 ^ ((i.succ : Fin (m + 1)) : ℕ) else 0)
      = ∑ i : Fin m, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0) :=
    Finset.sum_congr rfl (fun i _ => by
      by_cases hx : x i.succ = true <;> simp [hx, Fin.tail, pow_succ, mul_comm])
  rw [h2]
  simp

theorem muxTableFull : ∀ (m : ℕ) (x : Fin m → Bool) (j : ℕ),
    (tableIndex x).testBit j = if h : j < m then x ⟨j, h⟩ else false := by
  intro m
  induction m with
  | zero =>
    intro x j
    simp [tableIndex]
  | succ m ih =>
    intro x j
    rw [muxTableSucc]
    cases j with
    | zero =>
      rw [dif_pos (by omega)]
      show _ = x 0
      cases hx : x 0 <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ]
      have e : ((if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x)) / 2
          = tableIndex (Fin.tail x) := by
        split_ifs <;> omega
      rw [e, ih]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (by omega)]; rfl
      · rw [dif_neg hj, dif_neg (by omega)]

theorem muxTableRaw {m : ℕ} (x : Fin m → Bool) (i : Fin m) : (tableIndex x).testBit i = x i := by
  rw [muxTableFull, dif_pos i.isLt]

theorem muxTableBit {k : ℕ} (v : Fin k → Bool) (i : Fin k) :
    (Fin.ofNat (2^k) (tableIndex v)).val.testBit i.val = v i := by
  change (tableIndex v % 2^k).testBit i.val = _
  rw [Nat.mod_eq_of_lt (muxTableLt v), muxTableRaw]

theorem bLookup {n : ℕ} (a : ℕ) (Y : (Fin n → Bool) → ℕ) (sel : Fin a → Fin n)
    (hs : ∀ x (i : Fin a), (Y x).testBit i.val = x (sel i))
    (leaf : ℕ → (Fin n → Bool) → Bool) (b : ℕ) (hleaf : ∀ i, i < 2^a → Build (leaf i) b) :
    Build (fun x => leaf (Y x % 2^a) x) (b*2^a + 3*(2^a-1)) := by
  induction a generalizing leaf with
  | zero => simpa only [pow_zero, Nat.mod_one, Nat.mul_one, Nat.sub_self, Nat.mul_zero, Nat.add_zero] using hleaf 0 (by simp)
  | succ a ih =>
    have pos : 0 < 2^a := Nat.two_pow_pos _
    let lowSel := fun i : Fin a => sel i.castSucc
    have hsel (x) (i : Fin a) : (Y x).testBit i.val = x (lowSel i) := hs x i.castSucc
    have lo := ih lowSel hsel leaf (fun i hi => hleaf i (by rw [pow_succ]; omega))
    have high := ih lowSel hsel (fun i => leaf (i+2^a))
      (fun i hi => hleaf _ (by rw [pow_succ]; omega))
    have both := bMux (sel (Fin.last a)) lo high
    have hf (x : Fin n → Bool) : (if x (sel (Fin.last a)) then leaf (Y x % 2^a + 2^a) x
          else leaf (Y x % 2^a) x) = leaf (Y x % 2^(a+1)) x := by
      rw [← hs x (Fin.last a)]
      change (if (Y x).testBit a then _ else _) = _
      rw [pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
      by_cases h : Y x / 2^a % 2 = 1
      · simp [h]
      · have hz : Y x / 2^a % 2 = 0 := by omega
        simp [hz]
    have hc : b * 2^a + 3*(2^a-1) + (b * 2^a + 3*(2^a-1)) + 3 =
        b*2^(a+1) + 3*(2^(a+1)-1) := by
      rw [pow_succ, ← Nat.mul_assoc]; omega
    rwa [show (fun x : Fin n → Bool => if x (sel (Fin.last a)) then leaf (Y x % 2^a + 2^a) x
       else leaf (Y x % 2^a) x) = _ from funext hf, hc] at both

theorem bAddress (k a : ℕ) (h : 2^a ≤ k) :
    Build (adjFun (k := k) (l := k) (fun x y => x.val.testBit (y.val % 2^a))) (3*(2^a-1)) := by
  let X := fun x : Fin (k+k) → Bool => (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (i.castAdd k))).val
  let Y := fun x : Fin (k+k) → Bool => (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (i.natAdd k))).val
  have hak : a ≤ k := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans h
  let sel := fun i : Fin a => (Fin.castLE hak i).natAdd k
  have hs (x) (i : Fin a) : (Y x).testBit i.val = x (sel i) :=
    muxTableBit (fun j : Fin k => x (j.natAdd k)) (Fin.castLE hak i)
  let leaf := fun i (x : Fin (k+k) → Bool) => (X x).testBit i
  have hl (i : ℕ) (hi : i < 2^a) : Build (leaf i) 0 := by
    let j : Fin k := ⟨i, hi.trans_le h⟩
    have e (x : Fin (k+k) → Bool) : leaf i x = x (j.castAdd k) :=
      muxTableBit (fun u : Fin k => x (u.castAdd k)) j
    rw [show leaf i = _ from funext e]; exact bPos _
  change Build (fun x => leaf (Y x % 2^a) x) (3*(2^a-1))
  simpa only [Nat.zero_mul, Nat.zero_add] using bLookup a Y sel hs leaf 0 hl

end Upper

namespace Upper
open PEqualNP.MetaComplexity

private theorem cmpIndexSucc {k : ℕ} (x : Fin (k+1) → Bool) :
    tableIndex x = tableIndex (fun i => x i.castSucc) + (if x (Fin.last k) then 2^k else 0) := by
  simp [tableIndex, Fin.sum_univ_castSucc]

private theorem cmpIndexLt {k : ℕ} (x : Fin k → Bool) : tableIndex x < 2^k := by
  induction k with
  | zero => simp [tableIndex]
  | succ k ih =>
    rw [cmpIndexSucc, pow_succ]
    have h := ih (fun i => x i.castSucc)
    split <;> omega

private theorem cmpCast {n t : ℕ} {f g : (Fin n → Bool) → Bool}
    (h : Build f t) (e : ∀ x, f x = g x) : Build g t := (funext e) ▸ h

theorem buildCmp {n k : ℕ} (sel : Fin k → Fin n) (T : ℕ) :
    Build (fun x => decide (tableIndex (fun i => x (sel i)) < T)) (k+1) ∧
    Build (fun x => decide (T ≤ tableIndex (fun i => x (sel i)))) (k+1) := by
  induction k generalizing T with
  | zero =>
    simpa [tableIndex] using And.intro
      (bConst (n := n) (decide (0 < T))) (bConst (n := n) (decide (T ≤ 0)))
  | succ k ih =>
    let lo := fun i : Fin k => sel i.castSucc
    let top := sel (Fin.last k)
    by_cases hT : T ≤ 2^k
    · obtain ⟨A,B⟩ := ih lo T
      constructor
      · refine cmpCast (bAnd (a := k+1) (b := 0) A (bNeg top)) (fun x => ?_)
        rw [cmpIndexSucc]
        change (decide (tableIndex (fun i => x (lo i)) < T) && !x top) =
          decide (tableIndex (fun i => x (lo i)) + (if x top then 2^k else 0) < T)
        cases e : x top <;> simp <;> omega
      · refine cmpCast (bOr (a := k+1) (b := 0) B (bPos top)) (fun x => ?_)
        rw [cmpIndexSucc]
        change (decide (T ≤ tableIndex (fun i => x (lo i))) || x top) =
          decide (T ≤ tableIndex (fun i => x (lo i)) + (if x top then 2^k else 0))
        cases e : x top <;> simp <;> omega
    · obtain ⟨A,B⟩ := ih lo (T-2^k)
      constructor
      · refine cmpCast (bOr (a := k+1) (b := 0) A (bNeg top)) (fun x => ?_)
        rw [cmpIndexSucc]
        change (decide (tableIndex (fun i => x (lo i)) < T - 2^k) || !x top) =
          decide (tableIndex (fun i => x (lo i)) + (if x top then 2^k else 0) < T)
        have h := cmpIndexLt (fun i => x (lo i))
        cases e : x top <;> simp <;> omega
      · refine cmpCast (bAnd (a := k+1) (b := 0) B (bPos top)) (fun x => ?_)
        rw [cmpIndexSucc]
        change (decide (T - 2^k ≤ tableIndex (fun i => x (lo i))) && x top) =
          decide (T ≤ tableIndex (fun i => x (lo i)) + (if x top then 2^k else 0))
        have h := cmpIndexLt (fun i => x (lo i))
        cases e : x top <;> simp <;> omega

theorem buildCmpFin {n k : ℕ} (sel : Fin k → Fin n) (T : ℕ) :
    Build (fun x => decide ((Fin.ofNat (2^k) (tableIndex (fun i => x (sel i)))).val < T)) (k+1) ∧
    Build (fun x => decide (T ≤ (Fin.ofNat (2^k) (tableIndex (fun i => x (sel i)))).val)) (k+1) := by
  simpa only [Fin.ofNat, Nat.mod_eq_of_lt (cmpIndexLt _)] using buildCmp sel T

end Upper

namespace Upper

private theorem tag_capacity (k : ℕ) (hk : 2 ≤ k) : k+2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem tag_mod {v N M h : ℕ} (hNM : M ∣ N) (hh : h ≤ M) (hM : M ≤ N)
    (hge : N-h ≤ v) (hlt : v < N) : M-1-v%M = N-1-v := by
  have hd : M ∣ N-M := Nat.dvd_sub hNM dvd_rfl
  have hsum : v = (v-(N-M)) + (N-M) := by omega
  have hm : v % M = v-(N-M) := by
    calc v % M = ((v-(N-M)) + (N-M)) % M := congrArg (· % M) hsum
         _ = v-(N-M) := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
                                  Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bTag {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (S V : (Fin n → Bool) → Fin (2^k))
    (si vi : Fin k → Fin n)
    (hs : ∀ x i, (S x).val.testBit i.val = x (si i))
    (hv : ∀ x i, (V x).val.testBit i.val = x (vi i)) :
    ∃ F, Build F (6*(k+2)) ∧ ∀ x, 2^k-(k+2) ≤ (V x).val → F x =
      (let off := 2^k-1-(V x).val
       if off=0 then false else if off=1 then true else (S x).val.testBit (off-2)) := by
  let t := Nat.clog 2 (k+2)
  have ht : t ≤ k := Nat.clog_le_of_le_pow (tag_capacity k hk)
  have hle : k+2 ≤ 2^t := Nat.le_pow_clog (by decide) _
  have htpos : 0 < t := Nat.clog_pos (by decide) (by omega)
  have hbound : 2^t < 2*(k+2) := by
    have h := Nat.pow_pred_clog_lt_self 2 (x := k+2) (by omega)
    change 2^t.pred < k+2 at h
    have he : t.pred+1 = t := Nat.succ_pred_eq_of_pos htpos
    rw [← he, pow_succ]; omega
  let z : Fin k := ⟨0, by omega⟩
  let leaf := fun (j : ℕ) (x : Fin n → Bool) =>
    let d := 2^t-1-j
    if d < 2 then !x (vi z)
    else if h : d-2 < k then x (si ⟨d-2,h⟩) else x (si z)
  have hL : ∀ j, j < 2^t → Build (leaf j) 0 := by
    intro j hj
    dsimp only [leaf]
    split_ifs with h h' <;> first | exact bNeg _ | exact bPos _
  have hB := bLookup t (fun x => (V x).val) (fun i => vi (i.castLE ht))
      (fun x i => hv x (i.castLE ht)) leaf 0 hL
  refine ⟨_, bMono hB (by omega), ?_⟩
  intro x hx
  have hoff := tag_mod (M := 2^t) (pow_dvd_pow 2 ht) hle (Nat.pow_le_pow_right (by decide) ht) hx (V x).isLt
  dsimp only [leaf]
  rw [hoff]
  have hlt := (V x).isLt
  have hb : 2^k-1-(V x).val-2 < k := by omega
  have hd : 2 ∣ 2^k := dvd_pow_self _ (by omega)
  have hz : (!x (vi z)) = !((V x).val.testBit 0) := congrArg Bool.not (hv x z).symm
  simp only [hb, dite_true, hz, Nat.testBit_zero]
  by_cases h0 : 2^k-1-(V x).val=0
  · have ha : (V x).val % 2 = 1 := by omega
    simp [h0, ha]
  by_cases h1 : 2^k-1-(V x).val=1
  · have ha : (V x).val % 2 = 0 := by omega
    simp [h1, ha]
  have h2 : ¬ 2^k-1-(V x).val < 2 := by omega
  simp only [h2, if_false, h0, h1]
  exact (hs x ⟨_, hb⟩).symm

end Upper

namespace Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem bCmpITE {n a b c : ℕ} (v : (Fin n → Bool) → ℕ) (T : ℕ)
    (hc : Build (fun x => decide (v x < T)) c ∧ Build (fun x => decide (T ≤ v x)) c)
    {f g : (Fin n → Bool) → Bool} (hf : Build f a) (hg : Build g b) :
    Build (fun x => if v x < T then f x else g x) (a+b+2*c+3) := by
  have h := bOr (bAnd hc.1 hf) (bAnd hc.2 hg)
  have he : (fun x => (decide (v x < T) && f x) || (decide (T ≤ v x) && g x)) =
      (fun x => if v x < T then f x else g x) := by
    funext x
    by_cases h : v x < T
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h]
  rw [he] at h
  exact bMono h (by omega)

lemma upperBound : ∀ (k a : ℕ), 2 ≤ a → 2^a ≤ k →
  let N := 2^k
  let r := 2^a
  let h := k+2
  let tag := fun (s v : Fin N) =>
    let off := N-1-v.val
    if off=0 then false else if off=1 then true else s.val.testBit (off-2)
  let G := fun (x y : Fin N) =>
    if x.val < N-h then
      (if y.val < N-h then x.val.testBit (y.val % r) else tag x y)
    else (if y.val < N-h then tag y x else true)
  PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
    (3*(r-1)+24*h) := by
  intro k a ha hr N r h tag G
  let si := fun i : Fin k => i.castAdd k
  let vi := fun i : Fin k => i.natAdd k
  let S := fun x : Fin (k+k) → Bool => Fin.ofNat (2^k) (tableIndex fun i => x (si i))
  let V := fun x : Fin (k+k) → Bool => Fin.ofNat (2^k) (tableIndex fun i => x (vi i))
  let T := N-h
  have hk : 2 ≤ k := le_trans (le_trans ha Nat.lt_two_pow_self.le) hr
  have hs (x) (i : Fin k) : (S x).val.testBit i.val = x (si i) := muxTableBit _ i
  have hv (x) (i : Fin k) : (V x).val.testBit i.val = x (vi i) := muxTableBit _ i
  obtain ⟨F,hF,H⟩ := bTag k hk S V si vi hs hv
  obtain ⟨F',hF',H'⟩ := bTag k hk V S vi si hv hs
  have hcS := buildCmpFin si T
  have hcV := buildCmpFin vi T
  let base := fun x => (S x).val.testBit ((V x).val % r)
  have hbase : Build base (3*(r-1)) := bAddress k a hr
  have h1 := bCmpITE (fun x => (V x).val) T hcV hbase hF
  have h2 := bCmpITE (fun x => (V x).val) T hcV hF' (bConst true)
  have result := bCmpITE (fun x => (S x).val) T hcS h1 h2
  have he : (fun x => if (S x).val < T then
      (if (V x).val < T then base x else F x) else
      (if (V x).val < T then F' x else true)) = adjFun G := by
    funext x
    change _ = (if (S x).val < T then
      (if (V x).val < T then base x else tag (S x) (V x)) else
      (if (V x).val < T then tag (V x) (S x) else true))
    by_cases hS : (S x).val < T <;> by_cases hV : (V x).val < T <;> simp only [hS, hV, if_pos, if_true, if_false]
    · exact H x (Nat.le_of_not_gt hV)
    · exact H' x (Nat.le_of_not_gt hS)
  rw [he] at result
  exact bSound (bMono result (by dsimp only [h]; omega))

end Upper

namespace Dervish25702.Konig

open Finset

universe u v

namespace HallSupport

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  have := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  have := Classical.decEq ι

  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne

  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩

  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  have := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have := Classical.decEq ι

  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩

  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩

  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallSupport

theorem matching_cover {n : ℕ} (R : Fin n → Fin n → Prop) :
    ∃ (t : ℕ) (row col : Fin t → Fin n) (X Y : Finset (Fin n)),
    Function.Injective row ∧ Function.Injective col ∧ (∀ i, R (row i) (col i)) ∧
    X.card + Y.card ≤ t ∧ ∀ i j, R i j → i ∈ X ∨ j ∈ Y := by
  classical
  let nb := fun i : Fin n => univ.filter (R i)
  let B := fun S : Finset (Fin n) => S.biUnion nb
  let gain := fun S : Finset (Fin n) => S.card + n - (B S).card
  obtain ⟨S,_,hm⟩ := exists_max_image (univ : Finset (Finset (Fin n))) gain univ_nonempty
  let c := (B S).card
  have hBn (T : Finset (Fin n)) : (B T).card ≤ n := by simpa using (B T).card_le_univ
  have hmax (T : Finset (Fin n)) := hm T (mem_univ T)
  have hc : c ≤ S.card := by
    have h := hmax ∅
    simp [gain,B] at h
    have := hBn S
    dsimp [c,B] at *
    omega
  let d := S.card - c
  let adj := fun i : Fin n => (nb i).disjSum (univ : Finset (Fin d))
  have hall (T : Finset (Fin n)) : T.card ≤ (T.biUnion adj).card := by
    rcases T.eq_empty_or_nonempty with rfl|hT
    · simp
    have beq : T.biUnion adj = (B T).disjSum (univ : Finset (Fin d)) := by
      ext w; cases w with
      | inl y => simp [adj,B]
      | inr y => simpa [adj] using (show ∃ i, i ∈ T from hT)
    rw [beq,card_disjSum,card_univ,Fintype.card_fin]
    have hm' := hmax T
    change T.card + n - (B T).card ≤ S.card + n - c at hm'
    have hTn := hBn T
    dsimp [d]; omega
  obtain ⟨F,inj,edge⟩ := HallSupport.hall_hard_inductive hall
  let U := univ.filter fun i : Fin n => ∃ y : Fin n, F i = Sum.inl y
  have real (i : U) : ∃ y : Fin n, F i = Sum.inl y := (mem_filter.mp i.property).2
  choose C hC using real
  let V := univ \ U
  have fake (i : V) : ∃ y : Fin d, F i = Sum.inr y := by
    cases he : F i with
    | inr y => exact ⟨y,rfl⟩
    | inl y => exact False.elim ((mem_sdiff.mp i.property).2 (mem_filter.mpr ⟨mem_univ _,y,he⟩))
  choose D hD using fake
  have smallV : V.card ≤ d := by
    have hi : Function.Injective D := by
      intro a b e; apply Subtype.ext; apply inj; rw [hD a,hD b,e]
    simpa using Fintype.card_le_of_injective D hi
  have tbound : (univ \ S).card + c ≤ U.card := by
    have su := S.card_le_univ
    have uu := U.card_le_univ
    simp only [card_sdiff,inter_univ,card_univ,Fintype.card_fin] at su uu ⊢
    dsimp [V] at smallV; simp only [card_sdiff,inter_univ,card_univ,Fintype.card_fin] at smallV
    dsimp [d] at smallV; omega
  let eU : Fin U.card ≃ U := U.equivFin.symm
  refine ⟨U.card,fun i => (eU i).val,fun i => C (eU i),univ \ S,B S,?_,?_,?_,tbound,?_⟩
  · exact Subtype.val_injective.comp eU.injective
  · intro a b h; apply eU.injective; apply Subtype.ext; apply inj; rw [hC (eU a),hC (eU b)]
    exact congrArg Sum.inl h
  · intro i
    have h := edge ((eU i).val)
    rw [hC (eU i)] at h
    exact (mem_filter.mp (inl_mem_disjSum.mp h)).2
  · intro i j h; by_cases hi : i ∈ S
    · exact Or.inr (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨mem_univ _,hi⟩)
end Dervish25702.Konig

namespace Dervish25702
open PEqualNP.CircuitLowerBounds

def rawPair {N : ℕ} (C : Circuit) (i j : Fin N) :=
  ∃ p ∈ C.gates, p.inputs = [i.val,N+j.val] ∨ p.inputs = [N+j.val,i.val]

theorem cover_of_price {N : ℕ} (C : Circuit) (b : ℕ)
    (price : ∀ t (row col : Fin t → Fin N), Function.Injective row → Function.Injective col →
        (∀ i, rawPair C (row i) (col i)) → 2*N+t ≤ C.gates.countP (fun p => p.inputs.length == 2) + b) :
    ∃ X Y : Finset (Fin N), 2*N + X.card + Y.card ≤ C.gates.countP (fun p => p.inputs.length == 2) + b ∧
      ∀ (i j : Fin N) (p : Gate), p ∈ C.gates →
        (p.inputs = [i.val,N+j.val] ∨ p.inputs = [N+j.val,i.val]) → i ∈ X ∨ j ∈ Y := by
  obtain ⟨t,r,c,X,Y,hr,hc,hm,sz,cov⟩ := Konig.matching_cover (rawPair (N:=N) C)
  have h := price t r c hr hc hm
  exact ⟨X,Y,by omega, fun i j p hp h => cov i j ⟨p,hp,h⟩⟩
end Dervish25702

namespace Inject25702

private def tag {N : ℕ} (x y : Fin N) : Bool :=
  let d := N-1-y.val
  if d = 0 then false else if d = 1 then true else x.val.testBit (d-2)

private def pad {k : ℕ} (F : Fin (2^k) → Fin (2^k) → Bool) (x y : Fin (2^k)) :=
  if x.val < 2^k-(k+2) then
    (if y.val < 2^k-(k+2) then F x y else tag x y)
  else (if y.val < 2^k-(k+2) then tag y x else true)

private theorem margin (k : ℕ) (hk : 4 ≤ k) : 2^(k-1)+(k+2) < 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : k-1+1 = k := by omega
    have e := congrArg (fun n => (2:ℕ)^n) h
    simp only [pow_succ] at e ⊢
    simp only [Nat.add_sub_cancel] at *
    omega

private theorem injectRow {k : ℕ} (hk : 4 ≤ k)
    (F : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool) :
    Function.Injective (fun x y => xor (pad F x y) (xor (f x) (g y))) := by
  let N := 2^k
  let T := N-(k+2)
  have hs : 2^(k-1) + (k+2) < N := margin k hk
  have hPos : 0 < 2^(k-1) := pow_pos (by decide) _
  have hkN : k+2 < N := by omega
  have hN : 0 < N := by omega
  let v (d : ℕ) : Fin N := ⟨N-1-d, by exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hN (by decide))⟩
  have vd (d : ℕ) (hd : d < k+2) : N-1-(v d).val = d := by
    change N-1-(N-1-d) = d
    exact Nat.sub_sub_self (by omega)
  have vo (d : ℕ) (hd : d < k+2) : ¬(v d).val < T := by dsimp [v,T]; omega
  have p1 (x : Fin N) : pad F x (v 1) = true := by
    have h := vo 1 (by omega)
    have e := vd 1 (by omega)
    change (if x.val < T then (if (v 1).val < T then _ else tag x (v 1)) else (if (v 1).val < T then _ else true)) = true
    simp [h,tag,show 2^k = N by rfl,e]
  intro x z he
  have hh (y : Fin N) : xor (pad F x y) (xor (f x) (g y)) = xor (pad F z y) (xor (f z) (g y)) := congrFun he y
  have hv := hh (v 1)
  rw [p1,p1] at hv
  have hf := Bool.xor_left_inj.mp (Bool.xor_right_inj.mp hv)
  have raw (y : Fin N) : pad F x y = pad F z y := by
    have h := hh y
    rw [hf] at h
    exact Bool.xor_left_inj.mp h
  have p0 (s : Fin N) : pad F s (v 0) = !(decide (s.val < T)) := by
    have h := vo 0 (by omega)
    have e := vd 0 (by omega)
    change (if s.val < T then (if (v 0).val < T then _ else tag s (v 0)) else (if (v 0).val < T then _ else true)) = _
    by_cases hp : s.val < T <;> simp [hp,h,tag,show 2^k = N by rfl,e]
  have same := raw (v 0)
  rw [p0,p0] at same
  have hiff : x.val < T ↔ z.val < T := by simpa using same
  apply Fin.ext
  by_cases hx : x.val < T
  · have hz := hiff.mp hx
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · have hd : i+2 < k+2 := by omega
      have r := raw (v (i+2))
      change (if x.val < T then (if (v (i+2)).val < T then _ else tag x _) else _) = (if z.val < T then (if (v (i+2)).val < T then _ else tag z _) else _) at r
      simpa [hx,hz,vo _ hd,tag,show 2^k=N by rfl,vd _ hd] using r
    · have hn : N ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hn), Nat.testBit_lt_two_pow (lt_of_lt_of_le z.isLt hn)]
  · have hz := mt hiff.mpr hx
    have t (y : Fin N) (hy : y.val < T) : tag y x = tag y z := by
      have r := raw y
      change (if x.val < T then _ else (if y.val < T then tag y x else true)) = (if z.val < T then _ else (if y.val < T then tag y z else true)) at r
      simpa [hx,hz,hy] using r
    let d := N-1-x.val
    let e := N-1-z.val
    have dx : d < k+2 := by dsimp [T] at hx; dsimp [d]; omega
    have dz : e < k+2 := by dsimp [T] at hz; dsimp [e]; omega
    have tz := t ⟨0, by omega⟩ (by change 0 < N-(k+2); omega)
    change (if d=0 then false else if d=1 then true else (0:ℕ).testBit _) = (if e=0 then false else if e=1 then true else (0:ℕ).testBit _) at tz
    have one : d=1 ↔ e=1 := by
      by_cases hd : d=0 <;> by_cases he : e=0 <;> by_cases hd' : d=1 <;> by_cases he' : e=1 <;> simp_all
    have ti (i : ℕ) (hi : i < k) : (if d=0 then false else if d=1 then true else (2^i : ℕ).testBit (d-2)) = (if e=0 then false else if e=1 then true else (2^i : ℕ).testBit (e-2)) := by
      have hp : 2^i ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact t ⟨2^i, by omega⟩ (by change 2^i < N-(k+2); omega)
    by_contra hn
    have hde : d ≠ e := by dsimp [d,e]; have := x.isLt; have := z.isLt; omega
    have hd1 : d ≠ 1 := by intro h; exact hde (h.trans (one.mp h).symm)
    have he1 : e ≠ 1 := mt one.mpr hd1
    by_cases hd0 : d = 0
    · have he0 : e ≠ 0 := by omega
      have hb := ti (e-2) (by omega)
      change (if d=0 then false else if d=1 then true else (2^_ : ℕ).testBit _) = (if e=0 then false else if e=1 then true else (2^(e-2) : ℕ).testBit (e-2)) at hb
      simp [hd0,he0,he1,Nat.testBit_two_pow] at hb
    · have hb := ti (d-2) (by omega)
      change (if d=0 then false else if d=1 then true else (2^(d-2) : ℕ).testBit (d-2)) = (if e=0 then false else if e=1 then true else (2^(d-2) : ℕ).testBit (e-2)) at hb
      by_cases he0 : e=0
      · simp [he0,hd0,hd1,Nat.testBit_two_pow] at hb
      · have hne : d-2 ≠ e-2 := by omega
        simp [hd0,he0,he1,hd1,Nat.testBit_two_pow,hne] at hb

private theorem injectBoth {k : ℕ} (hk : 4 ≤ k)
    (F : Fin (2^k) → Fin (2^k) → Bool) (f g : Fin (2^k) → Bool) :
    Function.Injective (fun x y => xor (pad F x y) (xor (f x) (g y))) ∧
    Function.Injective (fun y x => xor (pad F x y) (xor (f x) (g y))) := by
  refine ⟨injectRow hk F f g, ?_⟩
  have eqv : (fun y x => xor (pad F x y) (xor (f x) (g y))) =
      (fun y x => xor (pad (fun s t => F t s) y x) (xor (g y) (f x))) := by
    funext y x
    rw [Bool.xor_comm (f x) (g y)]
    by_cases h : x.val < 2^k-(k+2) <;> by_cases h' : y.val < 2^k-(k+2) <;> simp [pad,h,h']
  rw [eqv]
  exact injectRow hk _ g f

theorem switched : ∀ (k a : ℕ), 2 ≤ a → 2^a ≤ k →
  let N := 2^k
  let r := 2^a
  let h := k+2
  let tag := fun (s v : Fin N) =>
    let off := N-1-v.val
    if off=0 then false else if off=1 then true else s.val.testBit (off-2)
  let G := fun (x y : Fin N) =>
    if x.val < N-h then
      (if y.val < N-h then x.val.testBit (y.val % r) else tag x y)
    else (if y.val < N-h then tag y x else true)
  ∀ (f g : Fin N → Bool),
    let H := fun left right => xor (G left right) (xor (f left) (g right))
    Function.Injective H ∧ Function.Injective (fun col row => H row col) := by
  intro k a ha hk
  dsimp only
  intro f g
  have h4 : 2^2 ≤ 2^a := Nat.pow_le_pow_right (by decide) ha
  exact injectBoth (le_trans h4 hk) (fun x y => x.val.testBit (y.val % 2^a)) f g

end Inject25702

end PEqualNP.Outside.L_meta_25702

theorem PEqualNP.Outside.L_meta_25702 : (∀ (k a : ℕ), 2 ≤ a → 2^a ≤ k →
  let N := 2^k
  let r := 2^a
  let h := k+2
  let tag := fun (s v : Fin N) =>
    let off := N-1-v.val
    if off=0 then false else if off=1 then true else s.val.testBit (off-2)
  let G := fun (x y : Fin N) =>
    if x.val < N-h then
      (if y.val < N-h then x.val.testBit (y.val % r) else tag x y)
    else (if y.val < N-h then tag y x else true)
  PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
    (3*(r-1)+24*h) ∧
  ∀ (f g : Fin N → Bool),
    let H := fun left right => xor (G left right) (xor (f left) (g right))
    Function.Injective H ∧ Function.Injective (fun col row => H row col) ∧
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) → PEqualNP.Represents.Represents H C →
      ∃ X Y : Finset (Fin N),
        2*N + X.card + Y.card ≤ C.gates.countP (fun gate => gate.inputs.length == 2) +
          (a+1)*2^(k-a) + 2*h + 3 ∧
        ∀ (i j : Fin N) (p : PEqualNP.CircuitLowerBounds.Gate), p ∈ C.gates →
          (p.inputs = [i.val,N+j.val] ∨ p.inputs = [N+j.val,i.val]) →
          i ∈ X ∨ j ∈ Y) := by
  intro k a ha hk N r h tag G
  refine ⟨PEqualNP.Outside.L_meta_25702.Upper.upperBound k a ha hk, ?_⟩
  intro f g H
  obtain ⟨hr,hc⟩ := PEqualNP.Outside.L_meta_25702.Inject25702.switched k a ha hk f g
  refine ⟨hr,hc,?_⟩
  intro C fan hRep
  have cover := PEqualNP.Outside.L_meta_25702.Dervish25702.cover_of_price (N := N) C ((a+1)*2^(k-a) + 2*h + 3) (by
    intro t row col ir ic pair
    obtain ⟨π,K,L,bd,hcut⟩ := PEqualNP.Outside.L_meta_25702.Price.matchingPrice H hr hc C fan hRep row col ir ic pair
    have hbulk : ∀ (i j : Fin N), i.val < 2^k-h → j.val < 2^k-h →
        H i j = xor (i.val.testBit (j.val % 2^a)) (xor (f i) (g j)) := by
      intro i j hi hj
      simp only [H,G,hi,hj,if_true,r,N]
    have lbd := PEqualNP.Outside.L_meta_25702.Labels.switchedBorder k a h hk H f g hbulk π K L hcut
    omega)
  simpa only [Nat.add_assoc] using cover
