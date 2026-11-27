import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29724_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def tplMat (n m : ℕ) (fr fc : Bool) (i : Fin n) (j : Fin m) : Bool :=
  if i.val < 4 ∧ j.val < 4 then
    match i.val, j.val with
    | 0, 2 => true
    | 1, 3 => true
    | 2, 0 => true
    | 2, 2 => true
    | 2, 3 => true
    | 3, 1 => true
    | 3, 2 => true
    | _, _ => false
  else if i.val < 4 then
    decide (i.val = 2) || (fc && decide (i.val = 3 ∧ j.val = 4))
  else if j.val < 4 then
    decide (j.val = 2) || (fr && decide (j.val = 3 ∧ i.val = 4))
  else
    let sr := 4 + if fr then 1 else 0
    let sc := 4 + if fc then 1 else 0
    decide (sr ≤ i.val ∧ sc ≤ j.val ∧ i.val - sr = j.val - sc)

def matchGatesAux (N r0 c0 : ℕ) : ℕ → ℕ → ℕ → List Gate × ℕ
  | 0, _, cur => ([], cur)
  | k + 1, t, cur =>
    let p : Gate := ⟨.and, [r0 + t, c0 + t]⟩
    let o : Gate := ⟨.or, [cur, N]⟩
    let (rest, fin) := matchGatesAux (N + 2) r0 c0 k (t + 1) (N + 1)
    (p :: o :: rest, fin)

def tplBase (n m : ℕ) : List Gate :=
  [⟨.or, [1, n + 1]⟩, ⟨.not, [n + m]⟩, ⟨.or, [3, n + 3]⟩, ⟨.or, [2, n + 2]⟩]

def tplSw (n m : ℕ) (fr fc : Bool) : List Gate × ℕ :=
  match fr, fc with
  | false, false => ([], n + m)
  | true, false => ([⟨.or, [n + m, 4]⟩], n + m + 4)
  | false, true => ([⟨.or, [n + m, n + 4]⟩], n + m + 4)
  | true, true => ([⟨.or, [n + m, 4]⟩, ⟨.or, [n + m + 4, n + 4]⟩], n + m + 5)

def tplN1 (n m : ℕ) (fr fc : Bool) : ℕ := n + m + 4 + (tplSw n m fr fc).1.length

def tplCoreGates (n m : ℕ) (fr fc : Bool) : List Gate :=
  tplBase n m ++ (tplSw n m fr fc).1 ++
    [⟨.and, [n + m + 1, n + m + 3]⟩, ⟨.and, [n + m + 2, (tplSw n m fr fc).2]⟩,
      ⟨.or, [tplN1 n m fr fc, tplN1 n m fr fc + 1]⟩]

def tplCirc (n m : ℕ) (fr fc : Bool) : Circuit :=
  let sr := 4 + if fr then 1 else 0
  let sc := 4 + if fc then 1 else 0
  let res := matchGatesAux (n + m + (tplCoreGates n m fr fc).length) sr (n + sc) (n - sr) 0 (tplN1 n m fr fc + 2)
  ⟨tplCoreGates n m fr fc ++ res.1, res.2⟩

theorem tplCirc_size (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    (tplCirc n m fr fc).size = n + m - 1 := by
  have hlen (N r0 c0 k t cur : ℕ) : (matchGatesAux N r0 c0 k t cur).1.length = 2 * k := by
    induction k generalizing N t cur with
    | zero => rfl
    | succ k ih => simp [matchGatesAux, ih]; omega
  unfold tplCirc tplCoreGates tplBase tplSw
  simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
  rw [hlen]
  cases fr <;> cases fc <;> simp at hn hm heq ⊢ <;> omega

theorem tplCirc_fanIn (n m : ℕ) (fr fc : Bool) : FanInTwo (tplCirc n m fr fc) := by
  have hf (N r0 c0 k t cur : ℕ) :
      ∀ g ∈ (matchGatesAux N r0 c0 k t cur).1,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    induction k generalizing N t cur with
    | zero => intro g hg; cases hg
    | succ k ih =>
      intro g hg
      simp only [matchGatesAux, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ih _ _ _ g hg
  intro g hg
  unfold tplCirc tplCoreGates tplBase at hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (hg | hg) | hg
  · rcases hg with (rfl | rfl | rfl | rfl) | hg
    all_goals try exact ⟨by simp, by simp⟩
    cases fr <;> cases fc <;> simp [tplSw] at hg
    · rcases hg with rfl; exact ⟨by simp, by simp⟩
    · rcases hg with rfl; exact ⟨by simp, by simp⟩
    · rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
  · rcases hg with rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  · exact hf _ _ _ _ _ _ g hg

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem step_len (x : List Bool) (g : Gate) : (step x g).length = x.length + 1 := by
  simp [step]

theorem getD_step_lt (x : List Bool) (g : Gate) (i : ℕ) (hi : i < x.length) :
    (step x g).getD i false = x.getD i false := by
  rw [step, snoc, if_pos hi]

theorem getD_step_eq (x : List Bool) (g : Gate) :
    (step x g).getD x.length false = compute x g := by
  rw [step, snoc, if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem foldl_step_len (gs : List Gate) : ∀ x : List Bool, (gs.foldl step x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih =>
    intro x
    rw [List.foldl_cons, ih (step x g), step_len]
    simp only [List.length_cons]
    omega

theorem foldl_step_pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl step x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih (step x g) w (by rw [step_len]; omega), getD_step_lt _ _ _ h]

theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem compute_and (x : List Bool) (a b : ℕ) :
    compute x ⟨.and, [a, b]⟩ = (x.getD a false && x.getD b false) := by
  simp [compute, GateOp.eval]

theorem compute_or (x : List Bool) (a b : ℕ) :
    compute x ⟨.or, [a, b]⟩ = (x.getD a false || x.getD b false) := by
  simp [compute, GateOp.eval]

theorem compute_not (x : List Bool) (a : ℕ) :
    compute x ⟨.not, [a]⟩ = !x.getD a false := by
  simp [compute, GateOp.eval]

theorem matchGatesAux_step (r0 c0 N t cur : ℕ) (W : List Bool)
    (hW : W.length = N) (hcur : cur < N) (hr0 : r0 + t < N) (hc0 : c0 + t < N) :
    let p : Gate := ⟨.and, [r0 + t, c0 + t]⟩
    let o : Gate := ⟨.or, [cur, N]⟩
    let W2 := step (step W p) o
    W2.length = N + 2 ∧
    (∀ w < N, W2.getD w false = W.getD w false) ∧
    W2.getD (N + 1) false = (W.getD cur false || (W.getD (r0 + t) false && W.getD (c0 + t) false)) := by
  dsimp only
  let p : Gate := ⟨.and, [r0 + t, c0 + t]⟩
  let o : Gate := ⟨.or, [cur, N]⟩
  let W1 := step W p
  let W2 := step W1 o
  have hW1 : W1.length = N + 1 := by rw [step_len, hW]
  have hW1_pre (w : ℕ) (hw : w < N) : W1.getD w false = W.getD w false :=
    getD_step_lt W p w (by rw [hW]; exact hw)
  have hW1_N : W1.getD N false = (W.getD (r0 + t) false && W.getD (c0 + t) false) := by
    have e := getD_step_eq W p; rw [hW] at e; change W1.getD N false = _ at e
    rw [e, compute_and]
  refine ⟨by rw [step_len, hW1], ?_, ?_⟩
  · intro w hw
    exact (getD_step_lt W1 o w (by rw [hW1]; omega)).trans (hW1_pre w hw)
  · have e := getD_step_eq W1 o; rw [hW1] at e; change W2.getD (N + 1) false = _ at e
    rw [e, compute_or, hW1_pre cur hcur, hW1_N]

theorem matchGatesAux_eval (r0 c0 : ℕ) :
    ∀ (k N t cur : ℕ) (W : List Bool),
      W.length = N → cur < N → (∀ q < k, r0 + t + q < N ∧ c0 + t + q < N) →
      ((matchGatesAux N r0 c0 k t cur).1.foldl step W).getD (matchGatesAux N r0 c0 k t cur).2 false =
        (W.getD cur false ||
          decide (∃ q < k, W.getD (r0 + t + q) false = true ∧ W.getD (c0 + t + q) false = true)) := by
  intro k
  induction k with
  | zero =>
    intro N t cur W _ _ _
    simp [matchGatesAux]
  | succ k ih =>
    intro N t cur W hW hcur hrc
    have hlt0 := hrc 0 (Nat.zero_lt_succ k)
    rw [Nat.add_zero] at hlt0
    obtain ⟨hW2, hW2_pre, hW2_out⟩ := matchGatesAux_step r0 c0 N t cur W hW hcur hlt0.1 hlt0.2
    let p : Gate := ⟨.and, [r0 + t, c0 + t]⟩
    let o : Gate := ⟨.or, [cur, N]⟩
    let W2 := step (step W p) o
    have ihstep := ih (N + 2) (t + 1) (N + 1) W2 hW2 (by omega) (fun q hq => by
      have h1 := hrc (q + 1) (Nat.succ_lt_succ hq)
      omega)
    have hrec1 : (matchGatesAux N r0 c0 (k + 1) t cur).1 =
        p :: o :: (matchGatesAux (N + 2) r0 c0 k (t + 1) (N + 1)).1 := rfl
    have hrec2 : (matchGatesAux N r0 c0 (k + 1) t cur).2 =
        (matchGatesAux (N + 2) r0 c0 k (t + 1) (N + 1)).2 := rfl
    rw [hrec1, hrec2, List.foldl_cons, List.foldl_cons]
    change ((matchGatesAux (N + 2) r0 c0 k (t + 1) (N + 1)).1.foldl step W2).getD
        (matchGatesAux (N + 2) r0 c0 k (t + 1) (N + 1)).2 false = _
    rw [ihstep, hW2_out]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((hc | ⟨hr0, hc0⟩) | ⟨q, hqk, hq1, hq2⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨0, Nat.zero_lt_succ k, by rw [Nat.add_zero]; exact hr0, by rw [Nat.add_zero]; exact hc0⟩
      · have hqlt := hrc (q + 1) (Nat.succ_lt_succ hqk)
        have h1 : W2.getD (r0 + (t + 1) + q) false = W.getD (r0 + (t + 1) + q) false := hW2_pre _ (by omega)
        have h2 : W2.getD (c0 + (t + 1) + q) false = W.getD (c0 + (t + 1) + q) false := hW2_pre _ (by omega)
        rw [h1] at hq1; rw [h2] at hq2
        have er : r0 + t + (q + 1) = r0 + (t + 1) + q := by omega
        have ec : c0 + t + (q + 1) = c0 + (t + 1) + q := by omega
        exact Or.inr ⟨q + 1, Nat.succ_lt_succ hqk, er ▸ hq1, ec ▸ hq2⟩
    · rintro (hc | ⟨q, hqk, hq1, hq2⟩)
      · exact Or.inl (Or.inl hc)
      · cases q with
        | zero =>
          rw [Nat.add_zero] at hq1 hq2
          exact Or.inl (Or.inr ⟨hq1, hq2⟩)
        | succ q =>
          have hqlt := hrc (q + 1) hqk
          have h1 : W2.getD (r0 + (t + 1) + q) false = W.getD (r0 + (t + 1) + q) false := hW2_pre _ (by omega)
          have h2 : W2.getD (c0 + (t + 1) + q) false = W.getD (c0 + (t + 1) + q) false := hW2_pre _ (by omega)
          have er : r0 + t + (q + 1) = r0 + (t + 1) + q := by omega
          have ec : c0 + t + (q + 1) = c0 + (t + 1) + q := by omega
          exact Or.inr ⟨q, Nat.lt_of_succ_lt_succ hqk, h1.symm ▸ (er ▸ hq1), h2.symm ▸ (ec ▸ hq2)⟩

theorem tpl_q0 : ∀ a b : Fin 4,
    ((!decide (a.val = 1 ∨ b.val = 1) && decide (a.val = 2 ∨ b.val = 2)) ||
      (decide (a.val = 3 ∨ b.val = 3) && decide (a.val = 1 ∨ b.val = 1))) =
    (match a.val, b.val with
      | 0, 2 | 1, 3 | 2, 0 | 2, 2 | 2, 3 | 3, 1 | 3, 2 => true
      | _, _ => false) := by decide

theorem tpl_q1 : ∀ (a : Fin 4) (fc j4 : Bool),
    ((!decide (a.val = 1) && decide (a.val = 2)) ||
      (decide (a.val = 3) && (decide (a.val = 1) || (fc && j4)))) =
    (decide (a.val = 2) || (fc && decide (a.val = 3) && j4)) := by decide

theorem tpl_q2 : ∀ (b : Fin 4) (fr i4 : Bool),
    ((!decide (b.val = 1) && decide (b.val = 2)) ||
      (decide (b.val = 3) && (decide (b.val = 1) || (fr && i4)))) =
    (decide (b.val = 2) || (fr && decide (b.val = 3) && i4)) := by decide

def tplSpec (n m : ℕ) (fr fc : Bool) (i : Fin n) (j : Fin m) : Bool :=
  ((!decide (i.val = 1 ∨ j.val = 1) && decide (i.val = 2 ∨ j.val = 2)) ||
    (decide (i.val = 3 ∨ j.val = 3) &&
      (decide (i.val = 1 ∨ j.val = 1) || (fr && decide (i.val = 4)) || (fc && decide (j.val = 4))))) ||
    decide ((4 + if fr then 1 else 0) ≤ i.val ∧ (4 + if fc then 1 else 0) ≤ j.val ∧
      i.val - (4 + if fr then 1 else 0) = j.val - (4 + if fc then 1 else 0))

theorem tplSpec_eq_tplMat (n m : ℕ) (fr fc : Bool) (i : Fin n) (j : Fin m) :
    tplSpec n m fr fc i j = tplMat n m fr fc i j := by
  unfold tplSpec tplMat
  by_cases hi4 : i.val < 4 <;> by_cases hj4 : j.val < 4
  · simp only [hi4, hj4, and_self, ite_true]
    have hs1 : ¬ ((4 + if fr then 1 else 0) ≤ i.val) := by omega
    have hi4f : decide (i.val = 4) = false := decide_eq_false (by omega)
    have hj4f : decide (j.val = 4) = false := decide_eq_false (by omega)
    simp only [hs1, false_and, decide_false, Bool.or_false, hi4f, hj4f, Bool.and_false]
    exact tpl_q0 ⟨i.val, hi4⟩ ⟨j.val, hj4⟩
  · simp only [hi4, hj4, and_false, ite_true, ite_false]
    have hs1 : ¬ ((4 + if fr then 1 else 0) ≤ i.val) := by omega
    have hi4f : decide (i.val = 4) = false := decide_eq_false (by omega)
    have hj1 : j.val ≠ 1 := by omega
    have hj2 : j.val ≠ 2 := by omega
    have hj3 : j.val ≠ 3 := by omega
    simp only [hs1, false_and, decide_false, Bool.or_false, hi4f, Bool.and_false, hj1, hj2, hj3, or_false]
    simpa [Bool.and_assoc] using tpl_q1 ⟨i.val, hi4⟩ fc (decide (j.val = 4))
  · simp only [hi4, hj4, false_and, ite_true, ite_false]
    have hs2 : ¬ ((4 + if fc then 1 else 0) ≤ j.val) := by omega
    have hj4f : decide (j.val = 4) = false := decide_eq_false (by omega)
    have hi1 : i.val ≠ 1 := by omega
    have hi2 : i.val ≠ 2 := by omega
    have hi3 : i.val ≠ 3 := by omega
    simp only [hs2, false_and, and_false, decide_false, Bool.or_false, hj4f, Bool.and_false, hi1, hi2, hi3, false_or]
    simpa [Bool.and_assoc] using tpl_q2 ⟨j.val, hj4⟩ fr (decide (i.val = 4))
  · simp only [hi4, hj4, and_self, ite_false]
    have hi1 : i.val ≠ 1 := by omega
    have hi2 : i.val ≠ 2 := by omega
    have hi3 : i.val ≠ 3 := by omega
    have hj1 : j.val ≠ 1 := by omega
    have hj2 : j.val ≠ 2 := by omega
    have hj3 : j.val ≠ 3 := by omega
    simp only [hi1, hi2, hi3, hj1, hj2, hj3, or_self, decide_false, Bool.not_false,
      Bool.false_and, Bool.and_false, Bool.or_self, Bool.false_or]

theorem tplBase_eval (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (x : List Bool) (hx : x.length = n + m) :
    let N := n + m
    let base : List Gate := [⟨.or, [1, n + 1]⟩, ⟨.not, [N]⟩, ⟨.or, [3, n + 3]⟩, ⟨.or, [2, n + 2]⟩]
    let W := base.foldl step x
    W.length = N + 4 ∧
    (∀ w < N, W.getD w false = x.getD w false) ∧
    W.getD N false = (x.getD 1 false || x.getD (n + 1) false) ∧
    W.getD (N + 1) false = !(x.getD 1 false || x.getD (n + 1) false) ∧
    W.getD (N + 2) false = (x.getD 3 false || x.getD (n + 3) false) ∧
    W.getD (N + 3) false = (x.getD 2 false || x.getD (n + 2) false) := by
  dsimp only
  let N := n + m
  let g0 : Gate := ⟨.or, [1, n + 1]⟩
  let g1 : Gate := ⟨.not, [N]⟩
  let g2 : Gate := ⟨.or, [3, n + 3]⟩
  let g3 : Gate := ⟨.or, [2, n + 2]⟩
  let w1 := step x g0
  let w2 := step w1 g1
  let w3 := step w2 g2
  let w4 := step w3 g3
  have hl1 : w1.length = N + 1 := by rw [step_len, hx]
  have hl2 : w2.length = N + 2 := by rw [step_len, hl1]
  have hl3 : w3.length = N + 3 := by rw [step_len, hl2]
  have hl4 : w4.length = N + 4 := by rw [step_len, hl3]
  have hp1 (w : ℕ) (hw : w < N) : w1.getD w false = x.getD w false := getD_step_lt x g0 w (by rw [hx]; exact hw)
  have hp2 (w : ℕ) (hw : w < N + 1) : w2.getD w false = w1.getD w false := getD_step_lt w1 g1 w (by rw [hl1]; exact hw)
  have hp3 (w : ℕ) (hw : w < N + 2) : w3.getD w false = w2.getD w false := getD_step_lt w2 g2 w (by rw [hl2]; exact hw)
  have hp4 (w : ℕ) (hw : w < N + 3) : w4.getD w false = w3.getD w false := getD_step_lt w3 g3 w (by rw [hl3]; exact hw)
  have hv0 : w1.getD N false = (x.getD 1 false || x.getD (n + 1) false) := by
    have e := getD_step_eq x g0; rw [hx] at e; change w1.getD N false = _ at e
    rw [e, compute_or]
  have hv1 : w2.getD (N + 1) false = !(x.getD 1 false || x.getD (n + 1) false) := by
    have e := getD_step_eq w1 g1; rw [hl1] at e; change w2.getD (N + 1) false = _ at e
    rw [e, compute_not, hv0]
  have hv2 : w3.getD (N + 2) false = (x.getD 3 false || x.getD (n + 3) false) := by
    have e := getD_step_eq w2 g2; rw [hl2] at e; change w3.getD (N + 2) false = _ at e
    rw [e, compute_or, hp2 3 (by omega), hp2 (n + 3) (by omega), hp1 3 (by omega), hp1 (n + 3) (by omega)]
  have hv3 : w4.getD (N + 3) false = (x.getD 2 false || x.getD (n + 2) false) := by
    have e := getD_step_eq w3 g3; rw [hl3] at e; change w4.getD (N + 3) false = _ at e
    rw [e, compute_or, hp3 2 (by omega), hp3 (n + 2) (by omega), hp2 2 (by omega), hp2 (n + 2) (by omega),
      hp1 2 (by omega), hp1 (n + 2) (by omega)]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  refine ⟨hl4, ?_, ?_, ?_, ?_, hv3⟩
  · intro w hw
    rw [hp4 w (by omega), hp3 w (by omega), hp2 w (by omega), hp1 w hw]
  · rw [hp4 N (by omega), hp3 N (by omega), hp2 N (by omega), hv0]
  · rw [hp4 (N + 1) (by omega), hp3 (N + 1) (by omega), hv1]
  · rw [hp4 (N + 2) (by omega), hv2]

theorem tplCore_eval (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (x : List Bool) (hx : x.length = n + m) :
    let W := (tplCoreGates n m fr fc).foldl step x
    (∀ w < n + m, W.getD w false = x.getD w false) ∧
    W.getD (tplN1 n m fr fc + 2) false =
      ((!(x.getD 1 false || x.getD (n + 1) false) && (x.getD 2 false || x.getD (n + 2) false)) ||
        ((x.getD 3 false || x.getD (n + 3) false) &&
          ((x.getD 1 false || x.getD (n + 1) false) || (fr && x.getD 4 false) || (fc && x.getD (n + 4) false)))) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  dsimp only
  let N := n + m
  let p : List Gate × ℕ := tplSw n m fr fc
  let N1 := N + 4 + p.1.length
  let gL : Gate := ⟨.and, [N + 1, N + 3]⟩
  let gR : Gate := ⟨.and, [N + 2, p.2]⟩
  let gC : Gate := ⟨.or, [N1, N1 + 1]⟩
  have hcg : tplCoreGates n m fr fc =
      [⟨.or, [1, n + 1]⟩, ⟨.not, [N]⟩, ⟨.or, [3, n + 3]⟩, ⟨.or, [2, n + 2]⟩] ++ p.1 ++ [gL, gR, gC] := rfl
  have hn1eq : tplN1 n m fr fc = N1 := rfl
  rw [hcg, hn1eq]
  let Wbase := ([⟨.or, [1, n + 1]⟩, ⟨.not, [N]⟩, ⟨.or, [3, n + 3]⟩, ⟨.or, [2, n + 2]⟩] : List Gate).foldl step x
  obtain ⟨hbl, hb_pre, hb0, hb1, hb2, hb3⟩ := tplBase_eval n m hn4 hm4 x hx
  let Wsw := p.1.foldl step Wbase
  have hsw_len : Wsw.length = N1 := by dsimp [Wsw]; rw [foldl_step_len, hbl]
  have hsw_pre (w : ℕ) (hw : w < N + 4) : Wsw.getD w false = Wbase.getD w false :=
    foldl_step_pre p.1 Wbase w (by rw [hbl]; exact hw)
  have hswW_lt : p.2 < N1 := by
    cases fr <;> cases fc <;> simp only [p, tplSw, N1, N, List.length_nil, List.length_cons] <;> omega
  have hswV : Wsw.getD p.2 false =
      ((x.getD 1 false || x.getD (n + 1) false) || (fr && x.getD 4 false) || (fc && x.getD (n + 4) false)) := by
    cases fr <;> cases fc
    · change Wbase.getD N false = _; rw [hb0]; simp only [Bool.false_and, Bool.or_false]
    · have hm5 : 5 ≤ m := by simpa using hm
      change (step Wbase ⟨.or, [N, n + 4]⟩).getD (N + 4) false = _
      have e := getD_step_eq Wbase ⟨.or, [N, n + 4]⟩; rw [hbl] at e
      rw [e, compute_or, hb0, hb_pre (n + 4) (by omega)]
      simp only [Bool.false_and, Bool.or_false, Bool.true_and]
    · have hn5 : 5 ≤ n := by simpa using hn
      change (step Wbase ⟨.or, [N, 4]⟩).getD (N + 4) false = _
      have e := getD_step_eq Wbase ⟨.or, [N, 4]⟩; rw [hbl] at e
      rw [e, compute_or, hb0, hb_pre 4 (by omega)]
      simp only [Bool.false_and, Bool.or_false, Bool.true_and]
    · have hn5 : 5 ≤ n := by simpa using hn
      have hm5 : 5 ≤ m := by simpa using hm
      let w4 := step Wbase ⟨.or, [N, 4]⟩
      have hl4 : w4.length = N + 5 := by rw [step_len, hbl]
      have hv4 : w4.getD (N + 4) false = ((x.getD 1 false || x.getD (n + 1) false) || x.getD 4 false) := by
        have e := getD_step_eq Wbase ⟨.or, [N, 4]⟩; rw [hbl] at e; change w4.getD (N + 4) false = _ at e
        rw [e, compute_or, hb0, hb_pre 4 (by omega)]
      have hc4 : w4.getD (n + 4) false = x.getD (n + 4) false := by
        change (step Wbase ⟨.or, [N, 4]⟩).getD (n + 4) false = _
        rw [getD_step_lt Wbase ⟨.or, [N, 4]⟩ (n + 4) (by rw [hbl]; omega), hb_pre (n + 4) (by omega)]
      change (step w4 ⟨.or, [N + 4, n + 4]⟩).getD (N + 5) false = _
      have e := getD_step_eq w4 ⟨.or, [N + 4, n + 4]⟩; rw [hl4] at e
      rw [e, compute_or, hv4, hc4]; simp only [Bool.true_and]
  let wl := step Wsw gL
  let wr := step wl gR
  let wc := step wr gC
  have hll : wl.length = N1 + 1 := by rw [step_len, hsw_len]
  have hrl : wr.length = N1 + 2 := by rw [step_len, hll]
  have hpl (w : ℕ) (hw : w < N1) : wl.getD w false = Wsw.getD w false := getD_step_lt Wsw gL w (by rw [hsw_len]; exact hw)
  have hpr (w : ℕ) (hw : w < N1 + 1) : wr.getD w false = wl.getD w false := getD_step_lt wl gR w (by rw [hll]; exact hw)
  have hpc (w : ℕ) (hw : w < N1 + 2) : wc.getD w false = wr.getD w false := getD_step_lt wr gC w (by rw [hrl]; exact hw)
  have hwlV : wl.getD N1 false =
      (!(x.getD 1 false || x.getD (n + 1) false) && (x.getD 2 false || x.getD (n + 2) false)) := by
    have e := getD_step_eq Wsw gL; rw [hsw_len] at e; change wl.getD N1 false = _ at e
    rw [e, compute_and, hsw_pre (N + 1) (by omega), hsw_pre (N + 3) (by omega), hb1, hb3]
  have hwrV : wr.getD (N1 + 1) false =
      ((x.getD 3 false || x.getD (n + 3) false) &&
        ((x.getD 1 false || x.getD (n + 1) false) || (fr && x.getD 4 false) || (fc && x.getD (n + 4) false))) := by
    have e := getD_step_eq wl gR; rw [hll] at e; change wr.getD (N1 + 1) false = _ at e
    rw [e, compute_and, hpl (N + 2) (by dsimp [N1]; omega), hpl p.2 hswW_lt,
      hsw_pre (N + 2) (by omega), hb2, hswV]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [hpc w (by dsimp [N1]; omega), hpr w (by dsimp [N1]; omega), hpl w (by dsimp [N1]; omega),
      hsw_pre w (by omega), hb_pre w hw]
  · have e := getD_step_eq wr gC; rw [hrl] at e
    change (step wr gC).getD (N1 + 2) false = _
    rw [e, compute_or, hpr N1 (by omega), hwlV, hwrV]

theorem tplCirc_eval_gen (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0))
    (x : List Bool) (hxlen : x.length = n + m) :
    (tplCirc n m fr fc).eval x =
      (((!(x.getD 1 false || x.getD (n + 1) false) && (x.getD 2 false || x.getD (n + 2) false)) ||
        ((x.getD 3 false || x.getD (n + 3) false) &&
          ((x.getD 1 false || x.getD (n + 1) false) || (fr && x.getD 4 false) || (fc && x.getD (n + 4) false)))) ||
        decide (∃ q < n - (4 + if fr then 1 else 0),
          x.getD (4 + (if fr then 1 else 0) + q) false = true ∧
          x.getD (n + (4 + if fc then 1 else 0) + q) false = true)) := by
  have hk_m : n - (4 + if fr then 1 else 0) = m - (4 + if fc then 1 else 0) := by
    cases fr <;> cases fc <;> simp at hn hm heq ⊢ <;> omega
  let sr := 4 + if fr then 1 else 0
  let sc := 4 + if fc then 1 else 0
  let k := n - sr
  have hcore_len : (tplCoreGates n m fr fc).length = 7 + (tplSw n m fr fc).1.length := by
    unfold tplCoreGates tplBase; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hN1 : tplN1 n m fr fc = n + m + 4 + (tplSw n m fr fc).1.length := rfl
  have hmG := matchGatesAux_eval sr (n + sc) k (n + m + (tplCoreGates n m fr fc).length) 0
    (tplN1 n m fr fc + 2) ((tplCoreGates n m fr fc).foldl step x)
    (by rw [foldl_step_len, hxlen])
    (by rw [hcore_len, hN1]; omega)
    (fun q hq => by rw [hcore_len]; constructor <;> omega)
  change (((tplCirc n m fr fc).gates.foldl step x).getD (tplCirc n m fr fc).output false) = _
  unfold tplCirc
  dsimp only
  rw [List.foldl_append, hmG]
  obtain ⟨hpre, hcoreV⟩ := tplCore_eval n m fr fc hn hm x hxlen
  rw [hcoreV]
  apply congrArg (fun b => ((!(x.getD 1 false || x.getD (n + 1) false) && (x.getD 2 false || x.getD (n + 2) false)) ||
        ((x.getD 3 false || x.getD (n + 3) false) &&
          ((x.getD 1 false || x.getD (n + 1) false) || (fr && x.getD 4 false) || (fc && x.getD (n + 4) false)))) || b)
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hq1, hq2⟩
    refine ⟨q, hq, ?_, ?_⟩
    · rw [Nat.add_zero] at hq1; rw [← hpre (sr + q) (by omega)]; exact hq1
    · rw [Nat.add_zero] at hq2; rw [← hpre (n + sc + q) (by omega)]; exact hq2
  · rintro ⟨q, hq, hq1, hq2⟩
    refine ⟨q, hq, ?_, ?_⟩
    · rw [Nat.add_zero, hpre (sr + q) (by omega)]; exact hq1
    · rw [Nat.add_zero, hpre (n + sc + q) (by omega)]; exact hq2

theorem tplCirc_eval (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0))
    (i : Fin n) (j : Fin m) :
    (tplCirc n m fr fc).eval (oneEach i j) = tplMat n m fr fc i j := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  have hxrow (a : ℕ) (ha : a < n) : (oneEach i j).getD a false = decide (i.val = a) := by
    rw [each_value]; apply Bool.eq_iff_iff.2; have := i.isLt; have := j.isLt; simp; omega
  have hxcol (b : ℕ) (hb : b < m) : (oneEach i j).getD (n + b) false = decide (j.val = b) := by
    rw [each_value]; apply Bool.eq_iff_iff.2; have := i.isLt; have := j.isLt; simp; omega
  rw [tplCirc_eval_gen n m fr fc hn hm heq (oneEach i j) (by simp [oneEach])]
  have hx4r : (fr && (oneEach i j).getD 4 false) = (fr && decide (i.val = 4)) := by
    cases fr
    · simp only [Bool.false_and]
    · have hn5 : 5 ≤ n := by simpa using hn
      rw [hxrow 4 (by omega)]
  have hx4c : (fc && (oneEach i j).getD (n + 4) false) = (fc && decide (j.val = 4)) := by
    cases fc
    · simp only [Bool.false_and]
    · have hm5 : 5 ≤ m := by simpa using hm
      rw [hxcol 4 (by omega)]
  rw [hxrow 1 (by omega), hxcol 1 (by omega), hxrow 2 (by omega), hxcol 2 (by omega),
    hxrow 3 (by omega), hxcol 3 (by omega), hx4r, hx4c]
  have hk_m : n - (4 + if fr then 1 else 0) = m - (4 + if fc then 1 else 0) := by
    cases fr <;> cases fc <;> simp at hn hm heq ⊢ <;> omega
  have hdiag : decide (∃ q < n - (4 + if fr then 1 else 0),
      (oneEach i j).getD (4 + (if fr then 1 else 0) + q) false = true ∧
      (oneEach i j).getD (n + (4 + if fc then 1 else 0) + q) false = true) =
      decide ((4 + if fr then 1 else 0) ≤ i.val ∧ (4 + if fc then 1 else 0) ≤ j.val ∧
        i.val - (4 + if fr then 1 else 0) = j.val - (4 + if fc then 1 else 0)) := by
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hq1, hq2⟩
      rw [hxrow (4 + (if fr then 1 else 0) + q) (by omega)] at hq1
      rw [show n + (4 + if fc then 1 else 0) + q = n + (4 + (if fc then 1 else 0) + q) by omega,
        hxcol (4 + (if fc then 1 else 0) + q) (by omega)] at hq2
      simp only [decide_eq_true_eq] at hq1 hq2
      omega
    · rintro ⟨hisr, hjsc, hdiff⟩
      refine ⟨i.val - (4 + if fr then 1 else 0), by have := i.isLt; omega, ?_, ?_⟩
      · rw [hxrow _ (by have := i.isLt; omega)]; simp only [decide_eq_true_eq]; omega
      · rw [show n + (4 + if fc then 1 else 0) + (i.val - (4 + if fr then 1 else 0)) =
            n + ((4 + if fc then 1 else 0) + (i.val - (4 + if fr then 1 else 0))) by omega,
          hxcol _ (by have := j.isLt; omega)]
        simp only [decide_eq_true_eq]; omega
  rw [hdiag]
  exact tplSpec_eq_tplMat n m fr fc i j

def quadMat (a b : Fin 4) : Bool :=
  match a.val, b.val with
  | 0, 2 | 1, 3 | 2, 0 | 2, 2 | 2, 3 | 3, 1 | 3, 2 => true
  | _, _ => false

theorem quadMat_injR : ∀ a b : Fin 4, (∀ c : Fin 4, quadMat a c = quadMat b c) → a = b := by decide
theorem quadMat_injC : ∀ a b : Fin 4, (∀ c : Fin 4, quadMat c a = quadMat c b) → a = b := by decide

theorem tplMat_lt4 {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m} (hi : i.val < 4) (hj : j.val < 4) :
    tplMat n m fr fc i j = quadMat ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  unfold tplMat; rw [if_pos ⟨hi, hj⟩]; rfl

theorem tplMat_row4 {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m} (hi : i.val < 4) (hj : ¬ (j.val < 4)) :
    tplMat n m fr fc i j = (decide (i.val = 2) || (fc && decide (i.val = 3 ∧ j.val = 4))) := by
  unfold tplMat; rw [if_neg (fun h => hj h.2), if_pos hi]

theorem tplMat_col4 {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m} (hi : ¬ (i.val < 4)) (hj : j.val < 4) :
    tplMat n m fr fc i j = (decide (j.val = 2) || (fr && decide (j.val = 3 ∧ i.val = 4))) := by
  unfold tplMat; rw [if_neg (fun h => hi h.1), if_neg hi, if_pos hj]

theorem tplMat_diag {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m} (hi : ¬ (i.val < 4)) (hj : ¬ (j.val < 4)) :
    tplMat n m fr fc i j = decide ((4 + if fr then 1 else 0) ≤ i.val ∧ (4 + if fc then 1 else 0) ≤ j.val ∧
      i.val - (4 + if fr then 1 else 0) = j.val - (4 + if fc then 1 else 0)) := by
  unfold tplMat; rw [if_neg (fun h => hi h.1), if_neg hi, if_neg hj]

theorem quadMat_val (a b : Fin 4) :
    quadMat a b = decide ((a.val = 0 ∧ b.val = 2) ∨ (a.val = 1 ∧ b.val = 3) ∨
      (a.val = 2 ∧ (b.val = 0 ∨ b.val = 2 ∨ b.val = 3)) ∨ (a.val = 3 ∧ (b.val = 1 ∨ b.val = 2))) := by
  revert a b; decide

theorem diag_bound (n m : ℕ) (fr fc : Bool)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0))
    (i : ℕ) (hisr : 4 + (if fr then 1 else 0) ≤ i) (hi : i < n) :
    4 + (if fc then 1 else 0) + (i - (4 + if fr then 1 else 0)) < m := by
  cases fr <;> cases fc <;> simp at heq hisr ⊢ <;> omega

theorem tplMat_row4_false {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m}
    (hi : i.val < 4) (hj : ¬ (j.val < 4)) (hne2 : i.val ≠ 2) (hne3 : i.val ≠ 3) :
    tplMat n m fr fc i j = false := by
  rw [tplMat_row4 fr fc hi hj]; simp [hne2, hne3]

theorem tplMat_col4_false {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m}
    (hi : ¬ (i.val < 4)) (hj : j.val < 4) (hne2 : j.val ≠ 2) (hne3 : j.val ≠ 3) :
    tplMat n m fr fc i j = false := by
  rw [tplMat_col4 fr fc hi hj]; simp [hne2, hne3]

theorem tplMat_row4_two {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m}
    (hi : i.val < 4) (hj : ¬ (j.val < 4)) (hi2 : i.val = 2) :
    tplMat n m fr fc i j = true := by
  rw [tplMat_row4 fr fc hi hj]; simp [hi2]

theorem tplMat_col4_two {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m}
    (hi : ¬ (i.val < 4)) (hj : j.val < 4) (hj2 : j.val = 2) :
    tplMat n m fr fc i j = true := by
  rw [tplMat_col4 fr fc hi hj]; simp [hj2]

theorem tplMat_diag_true {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m}
    (hi : ¬ (i.val < 4)) (hj : ¬ (j.val < 4))
    (hsr : 4 + (if fr then 1 else 0) ≤ i.val) (hsc : 4 + (if fc then 1 else 0) ≤ j.val)
    (heq : i.val - (4 + if fr then 1 else 0) = j.val - (4 + if fc then 1 else 0)) :
    tplMat n m fr fc i j = true := by
  rw [tplMat_diag fr fc hi hj]; simp [hsr, hsc, heq]

theorem tplMat_quad_at {n m : ℕ} (fr fc : Bool) {i : Fin n} {j : Fin m} {a b : ℕ}
    (ha : i.val = a) (hb : j.val = b) (ha4 : a < 4) (hb4 : b < 4) :
    tplMat n m fr fc i j = quadMat ⟨a, ha4⟩ ⟨b, hb4⟩ := by
  rw [tplMat_lt4 fr fc (ha ▸ ha4) (hb ▸ hb4)]
  congr 1; exact Fin.ext ha; exact Fin.ext hb

theorem tplMat_lt4_ne_ge4 (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0))
    (i1 i2 : Fin n) (h1 : i1.val < 4) (h2 : ¬ (i2.val < 4)) :
    tplMat n m fr fc i1 ≠ tplMat n m fr fc i2 := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  intro h
  have ha (j : Fin m) : tplMat n m fr fc i1 j = tplMat n m fr fc i2 j := congrFun h j
  have hi1_c : i1.val = 0 ∨ i1.val = 1 ∨ i1.val = 2 ∨ i1.val = 3 := by omega
  rcases hi1_c with e | e | e | e
  · by_cases hf4 : fr = true ∧ i2.val = 4
    · have q := ha ⟨3, by omega⟩
      rw [tplMat_quad_at fr fc (a := 0) (b := 3) e rfl (by decide) (by decide),
        tplMat_col4 fr fc h2 (by show 3 < 4; decide)] at q
      change false = _ at q
      simp [hf4.1, hf4.2] at q
    · have hisr : 4 + (if fr then 1 else 0) ≤ i2.val := by cases fr <;> simp at hf4 ⊢ <;> omega
      have hjlt := diag_bound n m fr fc heq i2.val hisr i2.isLt
      have hj4 : ¬ (4 + (if fc then 1 else 0) + (i2.val - (4 + if fr then 1 else 0)) < 4) := by
        exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
      have q := ha ⟨_, hjlt⟩
      rw [tplMat_row4_false fr fc h1 hj4 (by omega) (by omega),
        tplMat_diag_true fr fc h2 hj4 hisr (by exact Nat.le_add_right _ _)
          (Nat.add_sub_cancel_left _ _).symm] at q
      cases q
  · have q := ha ⟨2, by omega⟩
    rw [tplMat_quad_at fr fc (a := 1) (b := 2) e rfl (by decide) (by decide),
      tplMat_col4_two fr fc h2 (by show 2 < 4; decide) rfl] at q
    cases q
  · have q := ha ⟨0, by omega⟩
    rw [tplMat_quad_at fr fc (a := 2) (b := 0) e rfl (by decide) (by decide),
      tplMat_col4_false fr fc h2 (by show 0 < 4; decide) (by show 0 ≠ 2; decide) (by show 0 ≠ 3; decide)] at q
    cases q
  · have q := ha ⟨1, by omega⟩
    rw [tplMat_quad_at fr fc (a := 3) (b := 1) e rfl (by decide) (by decide),
      tplMat_col4_false fr fc h2 (by show 1 < 4; decide) (by show 1 ≠ 2; decide) (by show 1 ≠ 3; decide)] at q
    cases q

theorem tplMat_injR (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    Function.Injective (tplMat n m fr fc) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  intro i1 i2 h
  have ha (j : Fin m) : tplMat n m fr fc i1 j = tplMat n m fr fc i2 j := congrFun h j
  by_cases h1 : i1.val < 4 <;> by_cases h2 : i2.val < 4
  · have := quadMat_injR ⟨i1.val, h1⟩ ⟨i2.val, h2⟩ (fun c => by
      rcases c with ⟨cv, hcv⟩
      have q := ha ⟨cv, by omega⟩
      rw [tplMat_lt4 fr fc h1 hcv, tplMat_lt4 fr fc h2 hcv] at q
      exact q)
    exact Fin.ext (Fin.mk.inj this)
  · exact absurd h (tplMat_lt4_ne_ge4 n m fr fc hn hm heq i1 i2 h1 h2)
  · exact absurd h.symm (tplMat_lt4_ne_ge4 n m fr fc hn hm heq i2 i1 h2 h1)
  · by_cases hf1 : fr = true ∧ i1.val = 4
    · have q := ha ⟨3, by omega⟩
      rw [tplMat_col4 fr fc h1 (by show 3 < 4; decide), tplMat_col4 fr fc h2 (by show 3 < 4; decide)] at q
      simp [hf1.1, hf1.2] at q
      exact Fin.ext (hf1.2.trans q.symm)
    · have hisr1 : 4 + (if fr then 1 else 0) ≤ i1.val := by cases fr <;> simp at hf1 ⊢ <;> omega
      have hjlt := diag_bound n m fr fc heq i1.val hisr1 i1.isLt
      have hj4 : ¬ (4 + (if fc then 1 else 0) + (i1.val - (4 + if fr then 1 else 0)) < 4) := by
        exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
      have q := ha ⟨_, hjlt⟩
      rw [tplMat_diag_true fr fc h1 hj4 hisr1 (by exact Nat.le_add_right _ _)
          (Nat.add_sub_cancel_left (4 + if fc then 1 else 0) (i1.val - (4 + if fr then 1 else 0))).symm,
        tplMat_diag fr fc h2 hj4] at q
      have q_and := decide_eq_true_eq.mp q.symm
      have hisr2 : 4 + (if fr then 1 else 0) ≤ i2.val := q_and.1
      have q' := q_and.2.2
      rw [Nat.add_sub_cancel_left] at q'
      exact Fin.ext (by omega)

theorem tplMat_col_lt4_ne_ge4 (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0))
    (j1 j2 : Fin m) (h1 : j1.val < 4) (h2 : ¬ (j2.val < 4)) :
    (fun i : Fin n => tplMat n m fr fc i j1) ≠ (fun i : Fin n => tplMat n m fr fc i j2) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  intro h
  have ha (i : Fin n) : tplMat n m fr fc i j1 = tplMat n m fr fc i j2 := congrFun h i
  have hj1_c : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 ∨ j1.val = 3 := by omega
  rcases hj1_c with e | e | e | e
  · by_cases hf4 : fc = true ∧ j2.val = 4
    · have q := ha ⟨3, by omega⟩
      rw [tplMat_quad_at fr fc (a := 3) (b := 0) rfl e (by decide) (by decide),
        tplMat_row4 fr fc (by show 3 < 4; decide) h2] at q
      change false = _ at q
      simp [hf4.1, hf4.2] at q
    · have hjsc : 4 + (if fc then 1 else 0) ≤ j2.val := by cases fc <;> simp at hf4 ⊢ <;> omega
      have hilt := diag_bound m n fc fr heq.symm j2.val hjsc j2.isLt
      have hi4 : ¬ (4 + (if fr then 1 else 0) + (j2.val - (4 + if fc then 1 else 0)) < 4) := by
        exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
      have q := ha ⟨_, hilt⟩
      rw [tplMat_col4_false fr fc hi4 h1 (by omega) (by omega),
        tplMat_diag_true fr fc hi4 h2 (by exact Nat.le_add_right _ _) hjsc
          (Nat.add_sub_cancel_left (4 + if fr then 1 else 0) (j2.val - (4 + if fc then 1 else 0)))] at q
      cases q
  · have q := ha ⟨2, by omega⟩
    rw [tplMat_quad_at fr fc (a := 2) (b := 1) rfl e (by decide) (by decide),
      tplMat_row4_two fr fc (by show 2 < 4; decide) h2 rfl] at q
    cases q
  · have q := ha ⟨0, by omega⟩
    rw [tplMat_quad_at fr fc (a := 0) (b := 2) rfl e (by decide) (by decide),
      tplMat_row4_false fr fc (by show 0 < 4; decide) h2 (by show 0 ≠ 2; decide) (by show 0 ≠ 3; decide)] at q
    cases q
  · have q := ha ⟨1, by omega⟩
    rw [tplMat_quad_at fr fc (a := 1) (b := 3) rfl e (by decide) (by decide),
      tplMat_row4_false fr fc (by show 1 < 4; decide) h2 (by show 1 ≠ 2; decide) (by show 1 ≠ 3; decide)] at q
    cases q

theorem tplMat_injC (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    Function.Injective (fun (j : Fin m) (i : Fin n) => tplMat n m fr fc i j) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  intro j1 j2 h
  have ha (i : Fin n) : tplMat n m fr fc i j1 = tplMat n m fr fc i j2 := congrFun h i
  by_cases h1 : j1.val < 4 <;> by_cases h2 : j2.val < 4
  · have := quadMat_injC ⟨j1.val, h1⟩ ⟨j2.val, h2⟩ (fun c => by
      rcases c with ⟨cv, hcv⟩
      have q := ha ⟨cv, by omega⟩
      rw [tplMat_lt4 fr fc hcv h1, tplMat_lt4 fr fc hcv h2] at q
      exact q)
    exact Fin.ext (Fin.mk.inj this)
  · exact absurd h (tplMat_col_lt4_ne_ge4 n m fr fc hn hm heq j1 j2 h1 h2)
  · exact absurd h.symm (tplMat_col_lt4_ne_ge4 n m fr fc hn hm heq j2 j1 h2 h1)
  · by_cases hf1 : fc = true ∧ j1.val = 4
    · have q := ha ⟨3, by omega⟩
      rw [tplMat_row4 fr fc (by show 3 < 4; decide) h1, tplMat_row4 fr fc (by show 3 < 4; decide) h2] at q
      simp [hf1.1, hf1.2] at q
      exact Fin.ext (hf1.2.trans q.symm)
    · have hjsc1 : 4 + (if fc then 1 else 0) ≤ j1.val := by cases fc <;> simp at hf1 ⊢ <;> omega
      have hilt := diag_bound m n fc fr heq.symm j1.val hjsc1 j1.isLt
      have hi4 : ¬ (4 + (if fr then 1 else 0) + (j1.val - (4 + if fc then 1 else 0)) < 4) := by
        exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
      have q := ha ⟨_, hilt⟩
      rw [tplMat_diag_true fr fc hi4 h1 (by exact Nat.le_add_right _ _) hjsc1
          (Nat.add_sub_cancel_left (4 + if fr then 1 else 0) (j1.val - (4 + if fc then 1 else 0))),
        tplMat_diag fr fc hi4 h2] at q
      have q_and := decide_eq_true_eq.mp q.symm
      have hjsc2 : 4 + (if fc then 1 else 0) ≤ j2.val := q_and.2.1
      have q' := q_and.2.2
      rw [Nat.add_sub_cancel_left] at q'
      exact Fin.ext (by omega)

theorem tplMat_incR (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    let A := tplMat n m fr fc
    ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  dsimp only
  intro i
  by_cases hi4 : i.val < 4
  · have hi_c : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hi_c with e | e | e | e
    · refine ⟨⟨1, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨2, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 0) (b := 2) e rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 1) (b := 2) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 1) (b := 3) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 0) (b := 3) e rfl (by decide) (by decide)] at q; cases q
    · refine ⟨⟨0, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 1) (b := 3) e rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 0) (b := 3) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨2, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 0) (b := 2) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 1) (b := 2) e rfl (by decide) (by decide)] at q; cases q
    · refine ⟨⟨3, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨0, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 2) (b := 0) e rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 3) (b := 0) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 3) (b := 1) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 2) (b := 1) e rfl (by decide) (by decide)] at q; cases q
    · refine ⟨⟨2, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 3) (b := 1) e rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 2) (b := 1) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨0, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 2) (b := 0) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 3) (b := 0) e rfl (by decide) (by decide)] at q; cases q
  · refine ⟨⟨3, by omega⟩, ?_⟩; rintro (h | h)
    · by_cases hf4 : fr = true ∧ i.val = 4
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_col4 fr fc hi4 (by show 3 < 4; decide)]; simp [hf4.1, hf4.2])
        rw [tplMat_quad_at fr fc (a := 3) (b := 3) rfl rfl (by decide) (by decide)] at q; cases q
      · have hisr : 4 + (if fr then 1 else 0) ≤ i.val := by cases fr <;> simp at hf4 ⊢ <;> omega
        have hjlt := diag_bound n m fr fc heq i.val hisr i.isLt
        have hj4 : ¬ (4 + (if fc then 1 else 0) + (i.val - (4 + if fr then 1 else 0)) < 4) := by
          exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
        have q := h ⟨_, hjlt⟩ (tplMat_diag_true fr fc hi4 hj4 hisr (by exact Nat.le_add_right _ _)
          (Nat.add_sub_cancel_left (4 + if fc then 1 else 0) (i.val - (4 + if fr then 1 else 0))).symm)
        rw [tplMat_row4 fr fc (by show 3 < 4; decide) hj4] at q
        cases fc <;> simp at q <;> omega
    · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 3) (b := 1) rfl rfl (by decide) (by decide)]; rfl)
      rw [tplMat_col4_false fr fc hi4 (by show 1 < 4; decide) (by show 1 ≠ 2; decide) (by show 1 ≠ 3; decide)] at q; cases q

theorem tplMat_incC (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    let A := tplMat n m fr fc
    ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)) := by
  have hn4 : 4 ≤ n := by cases fr <;> simp at hn <;> omega
  have hm4 : 4 ≤ m := by cases fc <;> simp at hm <;> omega
  dsimp only
  intro j
  by_cases hj4 : j.val < 4
  · have hj_c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hj_c with e | e | e | e
    · refine ⟨⟨1, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨2, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 2) (b := 0) rfl e (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 2) (b := 1) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 3) (b := 1) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 3) (b := 0) rfl e (by decide) (by decide)] at q; cases q
    · refine ⟨⟨0, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 3) (b := 1) rfl e (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 3) (b := 0) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨2, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 2) (b := 0) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 2) (b := 1) rfl e (by decide) (by decide)] at q; cases q
    · refine ⟨⟨3, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨0, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 0) (b := 2) rfl e (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 0) (b := 3) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 1) (b := 3) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 1) (b := 2) rfl e (by decide) (by decide)] at q; cases q
    · refine ⟨⟨2, by omega⟩, ?_⟩; rintro (h | h)
      · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 1) (b := 3) rfl e (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 1) (b := 2) rfl rfl (by decide) (by decide)] at q; cases q
      · have q := h ⟨0, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 0) (b := 2) rfl rfl (by decide) (by decide)]; rfl)
        rw [tplMat_quad_at fr fc (a := 0) (b := 3) rfl e (by decide) (by decide)] at q; cases q
  · refine ⟨⟨3, by omega⟩, ?_⟩; rintro (h | h)
    · by_cases hf4 : fc = true ∧ j.val = 4
      · have q := h ⟨3, by omega⟩ (by rw [tplMat_row4 fr fc (by show 3 < 4; decide) hj4]; simp [hf4.1, hf4.2])
        rw [tplMat_quad_at fr fc (a := 3) (b := 3) rfl rfl (by decide) (by decide)] at q; cases q
      · have hjsc : 4 + (if fc then 1 else 0) ≤ j.val := by cases fc <;> simp at hf4 ⊢ <;> omega
        have hilt := diag_bound m n fc fr heq.symm j.val hjsc j.isLt
        have hi4 : ¬ (4 + (if fr then 1 else 0) + (j.val - (4 + if fc then 1 else 0)) < 4) := by
          exact Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right 4 _) (Nat.le_add_right _ _))
        have q := h ⟨_, hilt⟩ (tplMat_diag_true fr fc hi4 hj4 (by exact Nat.le_add_right _ _) hjsc
          (Nat.add_sub_cancel_left (4 + if fr then 1 else 0) (j.val - (4 + if fc then 1 else 0))))
        rw [tplMat_col4 fr fc hi4 (by show 3 < 4; decide)] at q
        cases fr <;> simp at q <;> omega
    · have q := h ⟨1, by omega⟩ (by rw [tplMat_quad_at fr fc (a := 1) (b := 3) rfl rfl (by decide) (by decide)]; rfl)
      rw [tplMat_row4_false fr fc (by show 1 < 4; decide) hj4 (by show 1 ≠ 2; decide) (by show 1 ≠ 3; decide)] at q; cases q

theorem tplMat_good (n m : ℕ) (fr fc : Bool)
    (hn : (if fr then 5 else 4) ≤ n) (hm : (if fc then 5 else 4) ≤ m)
    (heq : n - (if fr then 1 else 0) = m - (if fc then 1 else 0)) :
    let A := tplMat n m fr fc
    let lr := fun i k : Fin n => ∀ j, A i j = true → A k j = true
    let lc := fun j l : Fin m => ∀ i, A i j = true → A i l = true
    Function.Injective A ∧ Function.Injective (fun j i => A i j) ∧
    (∀ i, ∃ k, ¬ (lr i k ∨ lr k i)) ∧ (∀ j, ∃ l, ¬ (lc j l ∨ lc l j)) ∧
    ∃ C : Circuit, FanInTwo C ∧ Represents A C ∧ C.size ≤ n + m - 1 ∧ ∃ g ∈ C.gates, g.op = .not := by
  refine ⟨tplMat_injR n m fr fc hn hm heq, tplMat_injC n m fr fc hn hm heq,
    tplMat_incR n m fr fc hn hm heq, tplMat_incC n m fr fc hn hm heq,
    tplCirc n m fr fc, tplCirc_fanIn n m fr fc,
    fun i j => tplCirc_eval n m fr fc hn hm heq i j,
    le_of_eq (tplCirc_size n m fr fc hn hm heq),
    ⟨.not, [n + m]⟩, ?_, rfl⟩
  simp [tplCirc, tplCoreGates, tplBase]

private theorem pigeon2 {x y a b c : ℕ}
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) (hc : c = x ∨ c = y)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · rcases hc with rfl | rfl
    · exact hac rfl
    · exact hbc rfl
  · rcases hc with rfl | rfl
    · exact hbc rfl
    · exact hac rfl
  · exact hab rfl

private theorem pigeon3 {a b c d : ℕ}
    (ha : a = 1 ∨ a = 2 ∨ a = 4) (hb : b = 1 ∨ b = 2 ∨ b = 4)
    (hc : c = 1 ∨ c = 2 ∨ c = 4) (hd : d = 1 ∨ d = 2 ∨ d = 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  rcases ha with rfl | rfl | rfl
  · exact pigeon2 (hb.resolve_left (fun h => hab h.symm))
      (hc.resolve_left (fun h => hac h.symm)) (hd.resolve_left (fun h => had h.symm)) hbc hbd hcd
  · exact pigeon2 (hb.elim (Or.inl) (fun h => h.elim (fun h2 => absurd h2.symm hab) Or.inr))
      (hc.elim (Or.inl) (fun h => h.elim (fun h2 => absurd h2.symm hac) Or.inr))
      (hd.elim (Or.inl) (fun h => h.elim (fun h2 => absurd h2.symm had) Or.inr)) hbc hbd hcd
  · exact pigeon2 (hb.elim Or.inl (fun h => h.elim Or.inr (fun h4 => absurd h4.symm hab)))
      (hc.elim Or.inl (fun h => h.elim Or.inr (fun h4 => absurd h4.symm hac)))
      (hd.elim Or.inl (fun h => h.elim Or.inr (fun h4 => absurd h4.symm had))) hbc hbd hcd

theorem tplMat_distinct (n : ℕ) (hn : 5 ≤ n) :
    ¬ ∃ (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n)),
      ∀ i j, tplMat n n false false i j = tplMat n n true true (e i) (f j) := by
  rintro ⟨e, f, h⟩
  let r := e.symm ⟨3, by omega⟩
  have hchar (j : Fin n) : tplMat n n false false r j = tplMat n n true true ⟨3, by omega⟩ (f j) := by
    simpa [r] using h r j
  have hc1 : tplMat n n false false r (f.symm ⟨1, by omega⟩) = true := by
    rw [hchar, Equiv.apply_symm_apply, tplMat_quad_at true true (a := 3) (b := 1) rfl rfl (by decide) (by decide)]; rfl
  have hc2 : tplMat n n false false r (f.symm ⟨2, by omega⟩) = true := by
    rw [hchar, Equiv.apply_symm_apply, tplMat_quad_at true true (a := 3) (b := 2) rfl rfl (by decide) (by decide)]; rfl
  have hc4 : tplMat n n false false r (f.symm ⟨4, by omega⟩) = true := by
    rw [hchar, Equiv.apply_symm_apply, tplMat_row4 true true (by show 3 < 4; decide) (by dsimp; omega)]; simp
  have hf_vals (j : Fin n) (hj : tplMat n n false false r j = true) :
      (f j).val = 1 ∨ (f j).val = 2 ∨ (f j).val = 4 := by
    rw [hchar] at hj
    by_cases hfj : (f j).val < 4
    · rw [tplMat_lt4 true true (by show 3 < 4; decide) hfj, quadMat_val] at hj
      simp only [decide_eq_true_eq] at hj; omega
    · rw [tplMat_row4 true true (by show 3 < 4; decide) hfj] at hj
      simp at hj; exact Or.inr (Or.inr hj)
  by_cases hr4 : r.val < 4
  · have hrc : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
    rcases hrc with er | er | er | er
    · have only2 (j : Fin n) (hj : tplMat n n false false r j = true) : j.val = 2 := by
        by_cases hj4 : j.val < 4
        · rw [tplMat_lt4 false false hr4 hj4, quadMat_val] at hj
          simp only [decide_eq_true_eq] at hj; omega
        · rw [tplMat_row4 false false hr4 hj4] at hj; simp [er] at hj
      exact absurd (congrArg Fin.val (f.symm.injective (Fin.ext ((only2 _ hc1).trans (only2 _ hc2).symm)))) (by simp)
    · have only3 (j : Fin n) (hj : tplMat n n false false r j = true) : j.val = 3 := by
        by_cases hj4 : j.val < 4
        · rw [tplMat_lt4 false false hr4 hj4, quadMat_val] at hj
          simp only [decide_eq_true_eq] at hj; omega
        · rw [tplMat_row4 false false hr4 hj4] at hj; simp [er] at hj
      exact absurd (congrArg Fin.val (f.symm.injective (Fin.ext ((only3 _ hc1).trans (only3 _ hc2).symm)))) (by simp)
    · have q0 := hf_vals ⟨0, by omega⟩ (by rw [tplMat_quad_at false false (a := 2) (b := 0) er rfl (by decide) (by decide)]; rfl)
      have q2 := hf_vals ⟨2, by omega⟩ (by rw [tplMat_quad_at false false (a := 2) (b := 2) er rfl (by decide) (by decide)]; rfl)
      have q3 := hf_vals ⟨3, by omega⟩ (by rw [tplMat_quad_at false false (a := 2) (b := 3) er rfl (by decide) (by decide)]; rfl)
      have q4 := hf_vals ⟨4, by omega⟩ (by rw [tplMat_row4_two false false hr4 (by dsimp; omega) er])
      have neq {a b : Fin n} (hab : a.val ≠ b.val) : (f a).val ≠ (f b).val :=
        fun eq => hab (congrArg Fin.val (f.injective (Fin.ext eq)))
      have n02 := neq (show (⟨0, by omega⟩ : Fin n).val ≠ (⟨2, by omega⟩ : Fin n).val by simp)
      have n03 := neq (show (⟨0, by omega⟩ : Fin n).val ≠ (⟨3, by omega⟩ : Fin n).val by simp)
      have n04 := neq (show (⟨0, by omega⟩ : Fin n).val ≠ (⟨4, by omega⟩ : Fin n).val by simp)
      have n23 := neq (show (⟨2, by omega⟩ : Fin n).val ≠ (⟨3, by omega⟩ : Fin n).val by simp)
      have n24 := neq (show (⟨2, by omega⟩ : Fin n).val ≠ (⟨4, by omega⟩ : Fin n).val by simp)
      have n34 := neq (show (⟨3, by omega⟩ : Fin n).val ≠ (⟨4, by omega⟩ : Fin n).val by simp)
      exact pigeon3 q0 q2 q3 q4 n02 n03 n04 n23 n24 n34
    · have only12 (j : Fin n) (hj : tplMat n n false false r j = true) : j.val = 1 ∨ j.val = 2 := by
        by_cases hj4 : j.val < 4
        · rw [tplMat_lt4 false false hr4 hj4, quadMat_val] at hj
          simp only [decide_eq_true_eq] at hj; omega
        · rw [tplMat_row4 false false hr4 hj4] at hj; simp [er] at hj
      have o1 := only12 _ hc1
      have o2 := only12 _ hc2
      have o4 := only12 _ hc4
      have ne12 : (f.symm ⟨1, by omega⟩).val ≠ (f.symm ⟨2, by omega⟩).val :=
        fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
      have ne14 : (f.symm ⟨1, by omega⟩).val ≠ (f.symm ⟨4, by omega⟩).val :=
        fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
      have ne24 : (f.symm ⟨2, by omega⟩).val ≠ (f.symm ⟨4, by omega⟩).val :=
        fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
      exact pigeon2 o1 o2 o4 ne12 ne14 ne24
  · have only2r (j : Fin n) (hj : tplMat n n false false r j = true) : j.val = 2 ∨ j.val = r.val := by
      by_cases hj4 : j.val < 4
      · rw [tplMat_col4 false false hr4 hj4] at hj; simp at hj; exact Or.inl hj
      · rw [tplMat_diag false false hr4 hj4] at hj; simp at hj; exact Or.inr (by omega)
    have o1 := only2r _ hc1
    have o2 := only2r _ hc2
    have o4 := only2r _ hc4
    have ne12 : (f.symm ⟨1, by omega⟩).val ≠ (f.symm ⟨2, by omega⟩).val :=
      fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
    have ne14 : (f.symm ⟨1, by omega⟩).val ≠ (f.symm ⟨4, by omega⟩).val :=
      fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
    have ne24 : (f.symm ⟨2, by omega⟩).val ≠ (f.symm ⟨4, by omega⟩).val :=
      fun eq => absurd (congrArg Fin.val (f.symm.injective (Fin.ext eq))) (by simp)
    exact pigeon2 o1 o2 o4 ne12 ne14 ne24

end PEqualNP.Outside.L_meta_29724_aux

namespace PEqualNP.Outside.L_meta_29724_classif

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

-- Block A: Normalized circuit evaluation, minimal cones, slots/used counting, Unate

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool :=
  x ++ [compute x g]

theorem step_len (x : List Bool) (g : Gate) : (step x g).length = x.length + 1 := by
  simp [step]

theorem getD_step_lt (x : List Bool) (g : Gate) {i : ℕ} (hi : i < x.length) :
    (step x g).getD i false = x.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_step_eq (x : List Bool) (g : Gate) :
    (step x g).getD x.length false = compute x g := by
  simp [step, List.getD_eq_getElem?_getD]

theorem foldl_step_len (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step_len]; omega

theorem foldl_step_pre (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step x g).length := by rw [step_len]; omega
    rw [List.foldl_cons, ih (step x g) hi']
    exact getD_step_lt x g hi

theorem getD_foldl_ge (gs : List Gate) (x : List Bool) {i : ℕ} (hi : x.length + gs.length ≤ i) :
    (gs.foldl step x).getD i false = false := by
  apply List.getD_eq_default
  rw [foldl_step_len]
  exact hi

theorem wireAt_list (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
          if i < x.length + j then (gs.foldl step x).getD i false else false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      rw [List.foldl_cons, foldl_step_pre gs (step x g) (by rw [step_len]; omega), getD_step_eq]
      dsimp [compute]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [foldl_step_pre gs (step x g) (by rw [step_len]; omega), getD_step_lt x g hi]
      · exact List.getD_eq_default x false (Nat.le_of_not_lt hi)
    | succ j =>
      have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
      have hstep : (step x g).length + j = x.length + (j + 1) := by rw [step_len]; omega
      have hres := ih (step x g) j hj'
      rw [hstep] at hres
      simpa [List.foldl_cons] using hres

theorem gate_formula (C : Circuit) {N j : ℕ} (x : List Bool)
    (hx : x.length = N) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N + j then (C.wires x).getD i false else false) := by
  have h := wireAt_list C.gates x j hj
  rw [hx] at h
  exact h

def trimGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

def trim (C : Circuit) : Circuit :=
  ⟨C.gates.map trimGate, C.output⟩

theorem trimGate_eval (g : Gate) (x : List Bool) :
    compute x (trimGate g) = compute x g := by
  cases g with
  | mk op inp =>
    cases op <;> try rfl
    cases inp <;> rfl

theorem trim_size (C : Circuit) : (trim C).size = C.size := by
  simp [trim, Circuit.size]

theorem trim_eval (C : Circuit) (x : List Bool) :
    (trim C).eval x = C.eval x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  change ((C.gates.map trimGate).foldl step x).getD C.output false = _
  rw [h]
  rfl

theorem trim_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (trim C) := by
  intro g hg
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ha', hs⟩ := h a ha
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

theorem trim_unary (C : Circuit) :
    ∀ g ∈ (trim C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg he
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

theorem trim_has_not (C : Circuit) (h : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (trim C).gates, g.op = .not := by
  obtain ⟨g, hg, ho⟩ := h
  refine ⟨trimGate g, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
  rcases g with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

def before (C : Circuit) (N j u : ℕ) : Prop :=
  u ∈ (gateAt C j).inputs ∧ u < N + j

def closed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length) ∧
  ∀ j ∈ L, ∀ u, before C N j u → N ≤ u → u - N ∈ L

theorem minimal_closed (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    ∃ L : Finset ℕ, r ∈ L ∧ closed N C L ∧
      ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let P (L : Finset ℕ) : Prop := r ∈ L ∧ closed N C L
  have hfull : P (Finset.range C.gates.length) := by
    refine ⟨Finset.mem_range.mpr hr, fun j hj => Finset.mem_range.mp hj, fun j hj u hbef hu => ?_⟩
    rw [Finset.mem_range]
    have := Finset.mem_range.mp hj
    have := hbef.2
    omega
  let S : Set ℕ := {k | ∃ L : Finset ℕ, L.card = k ∧ P L}
  have hS : S.Nonempty :=
    ⟨(Finset.range C.gates.length).card, Finset.range C.gates.length, rfl, hfull⟩
  obtain ⟨kmin, hkmin, hmin⟩ := WellFounded.has_min Nat.lt_wfRel.wf S hS
  obtain ⟨L, rfl, hrL, hL⟩ := hkmin
  refine ⟨L, hrL, hL, fun i hi hne => ?_⟩
  by_contra! hno
  have hiL : L.erase i ⊂ L := Finset.erase_ssubset hi
  have hcard : (L.erase i).card < L.card := Finset.card_lt_card hiL
  have hsub : P (L.erase i) := by
    refine ⟨Finset.mem_erase.mpr ⟨hne.symm, hrL⟩,
      fun j hj => hL.1 j (Finset.mem_of_mem_erase hj),
      fun j hj u hbef hu => ?_⟩
    have hj' := Finset.mem_of_mem_erase hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, hL.2 j hj' u hbef hu⟩
    intro eq
    have hev : N + i = u := by omega
    rw [← hev] at hbef
    exact hno j hj' hbef
  exact hmin (L.erase i).card ⟨L.erase i, rfl, hsub⟩ hcard

def inputSlots (N : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((gateAt C j).inputs.toFinset.filter (· < N + j)).image (fun u => (j, u))

def slots (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) :=
  L.biUnion (inputSlots N C)

def used (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (slots N C L).image Prod.snd

theorem mem_slot {N : ℕ} {C : Circuit} {L : Finset ℕ} {j u : ℕ} :
    (j, u) ∈ slots N C L ↔ j ∈ L ∧ before C N j u := by
  simp [slots, inputSlots, before]

theorem mem_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {u : ℕ} :
    u ∈ used N C L ↔ ∃ j ∈ L, before C N j u := by
  simp [used, mem_slot]

theorem inputSlots_card (N : ℕ) (C : Circuit) (j : ℕ) :
    (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N + j)).card := by
  unfold inputSlots
  exact Finset.card_image_of_injOn (fun a _ b _ h => congrArg Prod.snd h)

def rawUsed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (used N C L).filter (· < N)

def missingRows (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => i.val ∉ used (n + m) C L

def missingCols (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j : Fin m => n + j.val ∉ used (n + m) C L

def isNotGate (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .not => true
  | _ => false

theorem isNotGate_eq_true {C : Circuit} {j : ℕ} :
    isNotGate C j = true ↔ (gateAt C j).op = .not := by
  unfold isNotGate
  cases (gateAt C j).op <;> simp

def activeNot (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  L.filter fun j => isNotGate C j

theorem mem_activeNot {C : Circuit} {L : Finset ℕ} {j : ℕ} :
    j ∈ activeNot C L ↔ j ∈ L ∧ (gateAt C j).op = .not := by
  simp [activeNot, isNotGate_eq_true]

theorem missing_rows_le {n m : ℕ} {C : Circuit} {L : Finset ℕ} :
    (missingRows n m C L).card ≤ n := by
  unfold missingRows
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem missing_cols_le {n m : ℕ} {C : Circuit} {L : Finset ℕ} :
    (missingCols n m C L).card ≤ m := by
  unfold missingCols
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem input_partition (n m : ℕ) (C : Circuit) (L : Finset ℕ) :
    (rawUsed (n + m) C L).card + (missingRows n m C L).card + (missingCols n m C L).card = n + m := by
  classical
  let R := Finset.univ.filter fun i : Fin n => i.val ∈ used (n + m) C L
  let K := Finset.univ.filter fun j : Fin m => n + j.val ∈ used (n + m) C L
  have hR : R.card + (missingRows n m C L).card = n := by
    simpa [R, missingRows] using Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin n => i.val ∈ used (n + m) C L)
  have hK : K.card + (missingCols n m C L).card = m := by
    simpa [K, missingCols] using Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun j : Fin m => n + j.val ∈ used (n + m) C L)
  let Ri := R.image (fun i : Fin n => i.val)
  let Ki := K.image (fun j : Fin m => n + j.val)
  have hRi : Ri.card = R.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => Fin.ext h)
  have hKi : Ki.card = K.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => Fin.ext (by omega))
  have hdis : Disjoint Ri Ki := by
    apply Finset.disjoint_left.mpr
    intro w hw1 hw2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp hw2
    have := i.isLt
    omega
  have heq : rawUsed (n + m) C L = Ri ∪ Ki := by
    ext w
    simp only [rawUsed, Finset.mem_filter, Finset.mem_union, Ri, Ki, R, K,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hwu, hwn⟩
      by_cases hwn' : w < n
      · left; exact ⟨⟨w, hwn'⟩, hwu, rfl⟩
      · have hge : n ≤ w := Nat.le_of_not_lt hwn'
        have hwm : w - n < m := by have := hwn; omega
        have heqw : n + (w - n) = w := Nat.add_sub_of_le hge
        right; exact ⟨⟨w - n, hwm⟩, by simpa [heqw] using hwu, heqw⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨hi, by have := i.isLt; omega⟩
      · exact ⟨hj, by have := j.isLt; omega⟩
  have hraw : (rawUsed (n + m) C L).card = R.card + K.card := by
    rw [heq, Finset.card_union_of_disjoint hdis, hRi, hKi]
  omega

theorem slots_count_low {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i)) :
    (rawUsed N C L).card + (L.card - 1) ≤ (used N C L).card := by
  let I := (L.erase r).image (N + ·)
  have hdis : Disjoint (rawUsed N C L) I := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'
    have := (Finset.mem_filter.mp hw).2
    omega
  have hsub : rawUsed N C L ∪ I ⊆ used N C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact (Finset.mem_filter.mp h).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hi
      exact mem_used.mpr (huse i hm hn)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injOn (fun a _ b _ h => by omega),
    Finset.card_erase_of_mem hr] at hc
  exact hc

theorem slots_count_high {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) :
    (slots N C L).card + (activeNot C L).card ≤ 2 * L.card := by
  classical
  have hmem (j : ℕ) (hj : j ∈ L) : gateAt C j ∈ C.gates := by
    have hb := hL.1 j hj
    rw [gateAt, List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem _
  have hw (j : ℕ) : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
    unfold inputSlots
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
  have hpoint (j : ℕ) (hj : j ∈ L) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hm := hmem j hj
    by_cases h : (gateAt C j).op = .not
    · have k := (hw j).trans (hNot _ hm h)
      simp [h]; omega
    · simpa [h] using (hw j).trans (hC _ hm).2
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  have hn : (activeNot C L).card = ∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0 := by
    unfold activeNot
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => by simp [isNotGate_eq_true]
  change (slots N C L).card ≤ ∑ j ∈ L, (inputSlots N C j).card at hslots
  have hsum : (∑ j ∈ L, ((inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0))) ≤
      ∑ _j ∈ L, (2 : ℕ) := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← hn] at hsum
  calc
    _ ≤ (∑ j ∈ L, (inputSlots N C j).card) + (activeNot C L).card := Nat.add_le_add_right hslots _
    _ ≤ ∑ _j ∈ L, (2 : ℕ) := hsum
    _ = _ := by simp [Nat.mul_comm]

theorem unique_reader_of_inj {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hinj : Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ)))
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (he : before C N j w) (hf : before C N k w) : j = k :=
  congrArg Prod.fst (hinj (mem_slot.mpr ⟨hj, he⟩) (mem_slot.mpr ⟨hk, hf⟩) rfl)

-- Network paths, value, relay, unchanged, cut_agree, Unate

def edgeTo (N : ℕ) (C : Circuit) (L : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ j ∈ L, v = N + j ∧ before C N j u

def reaches (N : ℕ) (C : Circuit) (L : Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (edgeTo N C L)

theorem edgeTo_lt {N : ℕ} {C : Circuit} {L : Finset ℕ} {u v : ℕ} :
    edgeTo N C L u v → u < v := by
  rintro ⟨j, _, rfl, _, h⟩
  exact h

theorem reaches_le {N : ℕ} {C : Circuit} {L : Finset ℕ} {u v : ℕ}
    (h : reaches N C L u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ he ih => exact ih.trans (edgeTo_lt he).le

def live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N + j

theorem parent_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hu : before C N j u) : live N L u := by
  by_cases h : u < N
  · exact Or.inl h
  · exact Or.inr ⟨u - N, hL.2 j hj u hu (Nat.le_of_not_lt h), by omega⟩

def value (N : ℕ) (C : Circuit) (x : ℕ → Bool) (fix : ℕ → Option Bool) : ℕ → Bool
  | w =>
    if w < N then x w
    else
      match fix w with
      | some b => b
      | none =>
        let j := w - N
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun u =>
          if _hu : u < w then value N C x fix u else false)

def relay (f : ℕ) (b : Bool) (w : ℕ) : Option Bool :=
  if w = f then some b else none

theorem val_raw {N : ℕ} {C : Circuit} {x : ℕ → Bool} {fix : ℕ → Option Bool} {w : ℕ}
    (hw : w < N) : value N C x fix w = x w := by
  rw [value, if_pos hw]

theorem val_gate {N : ℕ} {C : Circuit} {x : ℕ → Bool} {fix : ℕ → Option Bool} {j : ℕ}
    (hf : fix (N + j) = none) :
    value N C x fix (N + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun u =>
        if u < N + j then value N C x fix u else false) := by
  rw [value, if_neg (by omega), hf]
  simp only [Nat.add_sub_cancel_left]
  rfl

theorem val_relay_at {N : ℕ} {C : Circuit} {x : ℕ → Bool} {f : ℕ} {b : Bool} (hf : N ≤ f) :
    value N C x (relay f b) f = b := by
  rw [value, if_neg (by omega)]
  simp [relay]

theorem val_fixed {N : ℕ} {C : Circuit} {x : ℕ → Bool} {fix : ℕ → Option Bool} {w : ℕ} {b : Bool}
    (hw : N ≤ w) (hb : fix w = some b) : value N C x fix w = b := by
  rw [value, if_neg (by omega), hb]

theorem val_original {N : ℕ} (C : Circuit) {x : List Bool} (hx : x.length = N)
    {L : Finset ℕ} (hL : closed N C L) {w : ℕ} (hw : live N L w) :
    value N C (fun i => x.getD i false) (fun _ => none) w = (C.wires x).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low]
      change x.getD w false = (C.gates.foldl step x).getD w false
      rw [foldl_step_pre C.gates x (hx ▸ low)]
    · rw [val_gate rfl, gate_formula C x hx (hL.1 j hj)]
      congr 1
      apply List.map_congr_left
      intro u hu
      split_ifs with hlt
      · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩)
      · rfl

theorem eval_eq_value {N : ℕ} (C : Circuit) {x : List Bool} (hx : x.length = N)
    {L : Finset ℕ} (hL : closed N C L) {r : ℕ} (hr : r ∈ L) (hout : C.output = N + r) :
    C.eval x = value N C (fun i => x.getD i false) (fun _ => none) (N + r) := by
  rw [val_original C hx hL (Or.inr ⟨r, hr, rfl⟩)]
  exact congrArg (fun idx => (C.wires x).getD idx false) hout

theorem reaches_root_of_closed {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i)) :
    ∀ i ∈ L, reaches N C L (N + i) (N + r) := by
  have hstep : ∀ d i, i ∈ L → C.gates.length - i = d → reaches N C L (N + i) (N + r) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro i hi hd
      by_cases e : i = r
      · rw [e]; exact Relation.ReflTransGen.refl
      · obtain ⟨j, hj, hbef⟩ := huse i hi e
        have hlt : i < j := by have := hbef.2; omega
        have hjlt : j < C.gates.length := hL.1 j hj
        have hilt : i < C.gates.length := hL.1 i hi
        have hd' : C.gates.length - j < d := by omega
        exact Relation.ReflTransGen.head ⟨j, hj, rfl, hbef⟩ (ih _ hd' j hj rfl)
  exact fun i hi => hstep (C.gates.length - i) i hi rfl

theorem every_gate_reaches_root {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i))
    {w : ℕ} (hw : live N L w) (hwn : ¬ w < N) :
    reaches N C L w (N + r) := by
  rcases hw with low | ⟨i, hi, rfl⟩
  · exact False.elim (hwn low)
  · exact reaches_root_of_closed hL huse i hi

theorem used_reaches_root {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i))
    {w : ℕ} (hw : w ∈ used N C L) : reaches N C L w (N + r) := by
  obtain ⟨j, hj, hbef⟩ := mem_used.mp hw
  exact Relation.ReflTransGen.head ⟨j, hj, rfl, hbef⟩ (reaches_root_of_closed hL huse j hj)

theorem value_agree_of_reaches {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L)
    {x y : ℕ → Bool} (hx : ∀ w < N, reaches N C L w (N + r) → x w = y w)
    {w : ℕ} (hw : live N L w) (hreach : reaches N C L w (N + r)) :
    value N C x (fun _ => none) w = value N C y (fun _ => none) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
      exact hx w low hreach
    · rw [val_gate rfl, val_gate rfl]
      congr 1; apply List.map_congr_left; intro u hu
      split_ifs with hlt
      · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (Relation.ReflTransGen.head ⟨j, hj, rfl, hu, hlt⟩ hreach)
      · rfl

theorem cut_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (f : ℕ) (hsingle : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (x y : ℕ → Bool) (fix_x fix_y : ℕ → Option Bool)
    (hraw : ∀ v < N, ¬ reaches N C L v f → x v = y v)
    (hfix : ∀ v, N ≤ v → v ≠ f → fix_x v = fix_y v)
    (hf : value N C x fix_x f = value N C y fix_y f)
    {w : ℕ} (hw : live N L w) (hout : w = f ∨ ¬ reaches N C L w f) :
    value N C x fix_x w = value N C y fix_y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hout with rfl | haway
    · exact hf
    · rcases hw with low | ⟨j, hj, rfl⟩
      · rw [val_raw low, val_raw low]
        exact hraw w low haway
      · have hne : N + j ≠ f := fun e => haway (e ▸ Relation.ReflTransGen.refl)
        rw [value, if_neg (by omega), value, if_neg (by omega), hfix (N + j) (by omega) hne]
        simp only [Nat.add_sub_cancel_left]
        cases hfx : fix_y (N + j) with
        | some b => rfl
        | none =>
          dsimp
          congr 1
          apply List.map_congr_left
          intro u hu
          split_ifs with hlt
          · have e : edgeTo N C L u (N + j) := ⟨j, hj, rfl, hu, hlt⟩
            have huout : u = f ∨ ¬ reaches N C L u f := by
              by_cases huf : u = f
              · exact Or.inl huf
              · right
                intro hp
                rcases hp.cases_head with rfl | ⟨b, heb, hbf⟩
                · exact huf rfl
                · have hbj := hsingle u huf b (N + j) heb e
                  rw [hbj] at hbf
                  exact haway hbf
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) huout
          · rfl

theorem eval_monotone_of_no_not {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hNoNot : ∀ j ∈ L, (gateAt C j).op ≠ .not)
    (hFan : FanInTwo C)
    {x y : ℕ → Bool} {fix : ℕ → Option Bool}
    (hraw : ∀ w < N, x w = true → y w = true)
    (hfix : ∀ w, fix w = none)
    {w : ℕ} (hw : live N L w) :
    value N C x fix w = true → value N C y fix w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low] at hx ⊢
      exact hraw w low hx
    · rw [val_gate (hfix _)] at hx ⊢
      have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
        exact List.getElem_mem _
      have hne := hNoNot j hj
      have h_and_or : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
        rcases (hFan _ hmem).1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · exact False.elim (hne ho)
      rcases h_and_or with ha | ho
      · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
        intro u hu
        have hxu := hx u hu
        split_ifs with hlt
        · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (by simpa [hlt] using hxu)
        · rw [if_neg hlt] at hxu; cases hxu
      · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
        obtain ⟨u, hu, hxu⟩ := hx
        refine ⟨u, hu, ?_⟩
        split_ifs with hlt
        · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (by simpa [hlt] using hxu)
        · rw [if_neg hlt] at hxu; cases hxu

-- Block B: Unate, TreeOK, deduce_matching

def activeReach (N : ℕ) (C : Circuit) (L : Finset ℕ) (skip : Option ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun a b => skip ≠ some a ∧ edgeTo N C L a b)

theorem activeReach_le {N : ℕ} {C : Circuit} {L : Finset ℕ} {skip : Option ℕ} {u v : ℕ}
    (h : activeReach N C L skip u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ he ih => exact ih.trans (edgeTo_lt he.2).le

private theorem path_last_eq_helper (R : ℕ → Prop) (stepP : ℕ → ℕ → Prop)
    (hmono : ∀ a b, stepP a b → a < b)
    (huniq : ∀ a b c, R a → stepP a b → stepP a c → b = c)
    {s u v w : ℕ}
    (hu : Relation.ReflTransGen (fun a b => R a ∧ stepP a b) s u)
    (hv : Relation.ReflTransGen (fun a b => R a ∧ stepP a b) s v)
    (hru : R u) (hrv : R v) (huw : stepP u w) (hvw : stepP v w) : u = v := by
  let P := fun a b => R a ∧ stepP a b
  have hpm {a b} (hp : Relation.ReflTransGen P a b) : a ≤ b := by
    induction hp with
    | refl => exact le_rfl
    | tail _ he ih => exact ih.trans (hmono _ _ he.2).le
  have hdet : ∀ {s₀ x y : ℕ}, Relation.ReflTransGen P s₀ x → Relation.ReflTransGen P s₀ y →
      P x w → P y w → x = y := by
    intro s₀ x y hx hy hxw hyw
    revert hy
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro hy
      rcases hy.cases_head with rfl | ⟨a, ha, hy⟩
      · rfl
      · have := huniq _ _ _ hxw.1 ha.2 hxw.2
        subst a
        have := hpm hy
        have := hmono _ _ hyw.2
        omega
    | @head s' a ha hax ih =>
      intro hy
      rcases hy.cases_head with rfl | ⟨b, hb, hy⟩
      · have := huniq _ _ _ ha.1 ha.2 hyw.2
        subst a
        have := hmono _ _ hxw.2
        have := hpm hax
        omega
      · have := huniq _ _ _ ha.1 ha.2 hb.2
        subst b
        exact ih hy
  exact hdet hu hv ⟨hru, huw⟩ ⟨hrv, hvw⟩

theorem activeReach_last_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {skip : Option ℕ} {s : ℕ}
    (huniq : ∀ a b c, activeReach N C L skip s a → skip ≠ some a →
      edgeTo N C L a b → edgeTo N C L a c → b = c)
    {u v w : ℕ} (hu : activeReach N C L skip s u) (hv : activeReach N C L skip s v)
    (hsu : skip ≠ some u) (hsv : skip ≠ some v)
    (huw : edgeTo N C L u w) (hvw : edgeTo N C L v w) : u = v := by
  let R : ℕ → Prop := fun a => activeReach N C L skip s a ∧ skip ≠ some a
  have est {z} (hz : activeReach N C L skip s z) :
      Relation.ReflTransGen (fun a b => R a ∧ edgeTo N C L a b) s z := by
    induction hz with
    | refl => exact .refl
    | tail h1 h2 ih => exact .tail ih ⟨⟨h1, h2.1⟩, h2.2⟩
  exact path_last_eq_helper R (edgeTo N C L) (fun _ _ h => edgeTo_lt h)
    (fun a b c hr => huniq a b c hr.1 hr.2) (est hu) (est hv) ⟨hu, hsu⟩ ⟨hv, hsv⟩ huw hvw

def UnateChanges (N i : ℕ) (skip : Option ℕ) (x y : ℕ → Bool) : Prop :=
  (∀ w < N, w ≠ i → x w = y w) ∧
  (∀ w, skip = some w → x w = y w) ∧
  (x i = true → y i = true)

theorem unate_unchanged {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {skip : Option ℕ} {fix : ℕ → Option Bool}
    (hfix : ∀ v, skip = some v ↔ fix v ≠ none) (hskipN : ∀ v, skip = some v → N ≤ v)
    {i : ℕ} {x y : ℕ → Bool} (hraw : ∀ w < N, w ≠ i → x w = y w)
    {w : ℕ} (hw : live N L w) (haway : ¬ activeReach N C L skip i w) :
    value N C x fix w = value N C y fix w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
      exact hraw w low (fun h => haway (h ▸ Relation.ReflTransGen.refl))
    · by_cases hsk : skip = some (N + j)
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp ((hfix (N + j)).mp hsk)
        rw [val_fixed (by omega) hb, val_fixed (by omega) hb]
      · have hf : fix (N + j) = none := by
          by_contra hne
          exact hsk ((hfix (N + j)).mpr hne)
        rw [val_gate hf, val_gate hf]
        congr 1; apply List.map_congr_left; intro u hu
        split_ifs with hlt
        · by_cases hsu : skip = some u
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp ((hfix u).mp hsu)
            have huN := hskipN u hsu
            rw [val_fixed huN hb, val_fixed huN hb]
          · have e : edgeTo N C L u (N + j) := ⟨j, hj, rfl, hu, hlt⟩
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (fun hp => haway (.tail hp ⟨hsu, e⟩))
        · rfl

private theorem eval_pos_map (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {vx vy : ℕ → Bool} (h : ∀ v ∈ g.inputs, vx v = true → vy v = true) :
    g.op.eval (g.inputs.map vx) = true → g.op.eval (g.inputs.map vy) = true := by
  rcases hop with ho | ho
  · simp only [ho, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx v hv => h v hv (hx v hv)
  · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, h v hv hx⟩

private theorem eval_neg_singleton {u : ℕ} {vx vy : ℕ → Bool}
    (h : vy u = true → vx u = true) :
    GateOp.not.eval ([u].map vx) = true → GateOp.not.eval ([u].map vy) = true := by
  simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
  intro hx
  cases hy : vy u
  · rfl
  · rw [h hy] at hx; cases hx

private theorem unate_step_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {u₀ : ℕ} {vx vy : ℕ → Bool}
    (h_other : ∀ v ∈ g.inputs, v ≠ u₀ → vx v = vy v)
    (h_u0 : vx u₀ = true → vy u₀ = true) :
    g.op.eval (g.inputs.map vx) = true → g.op.eval (g.inputs.map vy) = true := by
  apply eval_pos_map g hop
  intro v hv hvx
  by_cases hvu : v = u₀
  · rw [hvu]; exact h_u0 (hvu ▸ hvx)
  · rw [← h_other v hv hvu]; exact hvx

private theorem unate_gate_pos {N j u₀ : ℕ} {C : Circuit} {fix : ℕ → Option Bool}
    (x y : ℕ → Bool) (hf : fix (N + j) = none) (hu_lt : u₀ < N + j)
    (hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
    (h_other : ∀ v ∈ (gateAt C j).inputs, v ≠ u₀ →
      (if v < N + j then value N C x fix v else false) =
      (if v < N + j then value N C y fix v else false))
    (su : Bool)
    (hsu : (su = true → value N C x fix u₀ = true → value N C y fix u₀ = true) ∧
           (su = false → value N C y fix u₀ = true → value N C x fix u₀ = true)) :
    (su = true → value N C x fix (N + j) = true → value N C y fix (N + j) = true) ∧
    (su = false → value N C y fix (N + j) = true → value N C x fix (N + j) = true) := by
  cases su
  · refine ⟨(fun h => Bool.noConfusion h), fun _ => ?_⟩
    rw [val_gate hf, val_gate hf]
    exact unate_step_pos (gateAt C j) hop
      (fun v hv hvne => (h_other v hv hvne).symm)
      (fun hv => by rw [if_pos hu_lt] at hv ⊢; exact hsu.2 rfl hv)
  · refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    rw [val_gate hf, val_gate hf]
    exact unate_step_pos (gateAt C j) hop
      h_other
      (fun hv => by rw [if_pos hu_lt] at hv ⊢; exact hsu.1 rfl hv)

private theorem unate_gate_not {N j u₀ : ℕ} {C : Circuit} {fix : ℕ → Option Bool}
    (x y : ℕ → Bool) (hf : fix (N + j) = none) (hu_lt : u₀ < N + j)
    (ho : (gateAt C j).op = .not) (hin1 : (gateAt C j).inputs = [u₀])
    (su : Bool)
    (hsu : (su = true → value N C x fix u₀ = true → value N C y fix u₀ = true) ∧
           (su = false → value N C y fix u₀ = true → value N C x fix u₀ = true)) :
    ((!su) = true → value N C x fix (N + j) = true → value N C y fix (N + j) = true) ∧
    ((!su) = false → value N C y fix (N + j) = true → value N C x fix (N + j) = true) := by
  cases su
  · refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    rw [val_gate hf, val_gate hf, ho, hin1]
    exact eval_neg_singleton (fun hv => by rw [if_pos hu_lt] at hv ⊢; exact hsu.2 rfl hv)
  · refine ⟨(fun h => Bool.noConfusion h), fun _ => ?_⟩
    rw [val_gate hf, val_gate hf, ho, hin1]
    exact eval_neg_singleton (fun hv => by rw [if_pos hu_lt] at hv ⊢; exact hsu.1 rfl hv)

private theorem activeReach_step_tail {N : ℕ} {C : Circuit} {L : Finset ℕ} {skip : Option ℕ} {s t : ℕ}
    (h : activeReach N C L skip s t) :
    s = t ∨ ∃ u, activeReach N C L skip s u ∧ skip ≠ some u ∧ edgeTo N C L u t := by
  induction h with
  | refl => exact Or.inl rfl
  | tail h1 h2 _ => exact Or.inr ⟨_, h1, h2⟩

theorem single_path_unate {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    {skip : Option ℕ} {fix : ℕ → Option Bool}
    (hfix : ∀ v, skip = some v ↔ fix v ≠ none) (hskipN : ∀ v, skip = some v → N ≤ v)
    {i : ℕ} (hiN : i < N)
    (huniq : ∀ a b c, activeReach N C L skip i a → skip ≠ some a →
      edgeTo N C L a b → edgeTo N C L a c → b = c)
    {w : ℕ} (hw : live N L w) :
    ∃ s : Bool, ∀ x y : ℕ → Bool, (∀ v < N, v ≠ i → x v = y v) → (x i = true → y i = true) →
      ((s = true → value N C x fix w = true → value N C y fix w = true) ∧
       (s = false → value N C y fix w = true → value N C x fix w = true)) := by
  classical
  revert hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hreach : activeReach N C L skip i w
    · rcases hw with low | ⟨j, hj, rfl⟩
      · have heq : i = w := by
          rcases hreach.cases_head with rfl | ⟨b, hb, hbw⟩
          · rfl
          · rcases hb.2 with ⟨k, _, rfl, _⟩
            have := activeReach_le hbw
            omega
        subst heq
        exact ⟨true, fun x y _ hi => ⟨fun _ => by rw [val_raw hiN, val_raw hiN]; exact hi, fun h => by cases h⟩⟩
      · by_cases hsk : skip = some (N + j)
        · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp ((hfix (N + j)).mp hsk)
          exact ⟨true, fun x y _ _ =>
            ⟨fun _ => by rw [val_fixed (by omega) hb, val_fixed (by omega) hb]; exact id,
             fun h => by cases h⟩⟩
        · have hf : fix (N + j) = none := by
            by_contra hne; exact hsk ((hfix (N + j)).mpr hne)
          rcases activeReach_step_tail hreach with heq | ⟨u₀, hiu, hsu₀, hbef₀⟩
          · exact False.elim (by omega)
          · obtain ⟨j', _, heqj, hu_in, hu_lt⟩ := hbef₀
            have heqj' : j' = j := by omega
            rw [heqj'] at hu_in hu_lt
            obtain ⟨su, hsu⟩ := ih u₀ hu_lt (parent_live hL hj ⟨hu_in, hu_lt⟩)
            have hmem : gateAt C j ∈ C.gates := by
              rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
              exact List.getElem_mem _
            have h_other : ∀ v ∈ (gateAt C j).inputs, v ≠ u₀ →
                ∀ x y : ℕ → Bool, (∀ z < N, z ≠ i → x z = y z) →
                (if v < N + j then value N C x fix v else false) =
                (if v < N + j then value N C y fix v else false) := by
              intro v hv hvne x y hraw
              split_ifs with hvlt
              · by_cases hsv : skip = some v
                · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp ((hfix v).mp hsv)
                  have hvN := hskipN v hsv
                  rw [val_fixed hvN hb, val_fixed hvN hb]
                · have hvaway : ¬ activeReach N C L skip i v := fun hp => by
                    have ev : edgeTo N C L v (N + j) := ⟨j, hj, rfl, hv, hvlt⟩
                    have e₀ : edgeTo N C L u₀ (N + j) := ⟨j, hj, rfl, hu_in, hu_lt⟩
                    exact hvne (activeReach_last_eq huniq hp hiu hsv hsu₀ ev e₀)
                  exact unate_unchanged hL hfix hskipN hraw (parent_live hL hj ⟨hv, hvlt⟩) hvaway
              · rfl
            rcases (hFan _ hmem).1 with ho | ho | ho
            · exact ⟨su, fun x y hraw hxi => unate_gate_pos x y hf hu_lt (Or.inl ho)
                (fun v hv hvne => h_other v hv hvne x y hraw) su (hsu x y hraw hxi)⟩
            · exact ⟨su, fun x y hraw hxi => unate_gate_pos x y hf hu_lt (Or.inr ho)
                (fun v hv hvne => h_other v hv hvne x y hraw) su (hsu x y hraw hxi)⟩
            · have hlen1 := hNot (gateAt C j) hmem ho
              have hin1 : (gateAt C j).inputs = [u₀] := by
                rcases hinp : (gateAt C j).inputs with _ | ⟨a, tl⟩
                · rw [hinp] at hu_in; cases hu_in
                · have hlen0 : tl.length = 0 := by
                    rw [hinp] at hlen1
                    exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hlen1)
                  rw [List.length_eq_zero_iff] at hlen0
                  subst hlen0
                  rw [hinp] at hu_in
                  simp only [List.mem_singleton] at hu_in
                  simp [hu_in]
              exact ⟨!su, fun x y hraw hxi => unate_gate_not x y hf hu_lt ho hin1 su (hsu x y hraw hxi)⟩
    · refine ⟨true, fun x y hraw _ => ⟨fun _ hx => ?_, fun h => by cases h⟩⟩
      rw [← unate_unchanged hL hfix hskipN hraw hw hreach]
      exact hx

-- TreeOK & deduce_matching

section TreeAndMatching

variable {α : Type} [DecidableEq α]

def bits (s : Finset α) (i : α) : Bool := decide (i ∈ s)

def Local (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def hits (f : (α → Bool) → Bool) (a : α) : Prop := f (bits {a}) = true

def edge (f : (α → Bool) → Bool) (a b : α) : Prop := f (bits {a, b}) = true

def Rectangles (f : (α → Bool) → Bool) : Prop :=
  ∀ a b c d, f (bits {a}) = false → f (bits {b}) = false →
    f (bits {c}) = false → f (bits {d}) = false →
    edge f a b → edge f c b → edge f c d → edge f a d

def Spec (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  s.Nonempty ∧ Local s f ∧ f (bits ∅) = false ∧ f (fun _ => true) = true ∧ Rectangles f

def TreeOK (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ (∀ x, f x = true) ∨ Spec s f

theorem pair_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a b : α}
    (ha : a ∉ s) : f (bits {a, b}) = f (bits {b}) := by
  apply hf; intro i hi; have hia : i ≠ a := fun h => ha (h ▸ hi); simp [bits, hia]

theorem single_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a : α}
    (ha : a ∉ s) : f (bits {a}) = f (bits ∅) := by
  apply hf; intro i hi; have hia : i ≠ a := fun h => ha (h ▸ hi); simp [bits, hia]

theorem hit_in {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    (hzero : f (bits ∅) = false) {a : α} (ha : hits f a) : a ∈ s := by
  by_contra h; change f (bits {a}) = true at ha; rw [single_without hf h, hzero] at ha; cases ha

theorem edge_comm {f : (α → Bool) → Bool} {a b : α} : edge f a b ↔ edge f b a := by
  simp only [edge, Finset.pair_comm a b]

theorem edge_inside {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    {a b : α} (ha : f (bits {a}) = false) (hb : f (bits {b}) = false)
    (hab : edge f a b) : a ∈ s ∧ b ∈ s := by
  have left {i j : α} (h0 : f (bits {j}) = false) (h : edge f i j) : i ∈ s := by
    by_contra hi; change f (bits {i, j}) = true at h; rw [pair_without hf hi, h0] at h; cases h
  exact ⟨left hb hab, left ha (edge_comm.mp hab)⟩

theorem or_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (rf : Rectangles f) (rg : Rectangles g) : Rectangles (fun x => f x || g x) := by
  intro a b c d ha hb hc hd hab hcb hcd
  have sf {i : α} (h : (f (bits {i}) || g (bits {i})) = false) : f (bits {i}) = false :=
    (Bool.or_eq_false_iff.mp h).1
  have sg {i : α} (h : (f (bits {i}) || g (bits {i})) = false) : g (bits {i}) = false :=
    (Bool.or_eq_false_iff.mp h).2
  have hnot {i : α} (hi : i ∈ s) (hj : i ∈ t) : False := Finset.disjoint_left.mp hdis hi hj
  change (f (bits {a, b}) || g (bits {a, b})) = true at hab
  change (f (bits {c, b}) || g (bits {c, b})) = true at hcb
  change (f (bits {c, d}) || g (bits {c, d})) = true at hcd
  apply Bool.or_eq_true_iff.mpr
  rcases Bool.or_eq_true_iff.mp hab with hab | hab
  · have hb' := (edge_inside hf (sf ha) (sf hb) hab).2
    have hcb' : edge f c b := (Bool.or_eq_true_iff.mp hcb).resolve_right
      (fun h => hnot hb' (edge_inside hg (sg hc) (sg hb) h).2)
    have hc' := (edge_inside hf (sf hc) (sf hb) hcb').1
    have hcd' : edge f c d := (Bool.or_eq_true_iff.mp hcd).resolve_right
      (fun h => hnot hc' (edge_inside hg (sg hc) (sg hd) h).1)
    exact Or.inl (rf a b c d (sf ha) (sf hb) (sf hc) (sf hd) hab hcb' hcd')
  · have hb' := (edge_inside hg (sg ha) (sg hb) hab).2
    have hcb' : edge g c b := (Bool.or_eq_true_iff.mp hcb).resolve_left
      (fun h => hnot (edge_inside hf (sf hc) (sf hb) h).2 hb')
    have hc' := (edge_inside hg (sg hc) (sg hb) hcb').1
    have hcd' : edge g c d := (Bool.or_eq_true_iff.mp hcd).resolve_left
      (fun h => hnot (edge_inside hf (sf hc) (sf hd) h).1 hc')
    exact Or.inr (rg a b c d (sg ha) (sg hb) (sg hc) (sg hd) hab hcb' hcd')

theorem and_edge {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) (a b : α) :
    edge (fun x => f x && g x) a b ↔ (hits f a ∧ hits g b) ∨ (hits f b ∧ hits g a) := by
  have dis {i : α} (hs : i ∈ s) (ht : i ∈ t) : False := Finset.disjoint_left.mp hdis hs ht
  have lands {r : Finset α} {h : (α → Bool) → Bool} (hl : Local r h)
      (hz : h (bits ∅) = false) {i j : α} (hij : edge h i j) : i ∈ r ∨ j ∈ r := by
    by_contra hn; change h (bits {i, j}) = true at hij
    rw [pair_without hl (fun hi => hn (Or.inl hi)), single_without hl (fun hj => hn (Or.inr hj)), hz] at hij
    cases hij
  have align {i j : α} (hi : i ∈ s) (hj : j ∈ t) :
      (edge f i j ∧ edge g i j) ↔ hits f i ∧ hits g j := by
    have e₁ : f (bits {i, j}) = f (bits {i}) := by
      rw [Finset.pair_comm i j, pair_without hf (fun hs => dis hs hj)]
    have e₂ : g (bits {i, j}) = g (bits {j}) := pair_without hg (fun ht => dis hi ht)
    unfold edge hits; rw [e₁, e₂]
  change (f (bits {a, b}) && g (bits {a, b})) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rcases lands hf zf h.1 with ha | hb
    · have hb' := (lands hg zg h.2).resolve_left (fun ha' => dis ha ha')
      exact Or.inl ((align ha hb').mp h)
    · have ha' := (lands hg zg h.2).resolve_right (fun hb' => dis hb hb')
      exact Or.inr ((align hb ha').mp ⟨edge_comm.mp h.1, edge_comm.mp h.2⟩)
  · rintro (h | h)
    · exact (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
    · have hh := (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
      exact ⟨edge_comm.mp hh.1, edge_comm.mp hh.2⟩

theorem and_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) :
    Rectangles (fun x => f x && g x) := by
  intro a b c d _ _ _ _ hab hcb hcd
  have ha (i j : α) := and_edge hdis hf hg zf zg i j
  have hn {i : α} (h₁ : hits f i) (h₂ : hits g i) : False :=
    Finset.disjoint_left.mp hdis (hit_in hf zf h₁) (hit_in hg zg h₂)
  apply (ha a d).mpr
  rcases (ha a b).mp hab with hab | hab
  · have hcb := ((ha c b).mp hcb).resolve_right (fun h => hn h.1 hab.2)
    have hcd := ((ha c d).mp hcd).resolve_right (fun h => hn hcb.1 h.2)
    exact Or.inl ⟨hab.1, hcd.2⟩
  · have hcb := ((ha c b).mp hcb).resolve_left (fun h => hn hab.1 h.2)
    have hcd := ((ha c d).mp hcd).resolve_left (fun h => hn h.1 hcb.2)
    exact Or.inr ⟨hcd.1, hab.2⟩

def connect (isAnd : Bool) (f g : (α → Bool) → Bool) (x : α → Bool) : Bool :=
  if isAnd then f x && g x else f x || g x

theorem spec_mono {s t : Finset α} {f : (α → Bool) → Bool} (hsub : s ⊆ t) (hf : Spec s f) : Spec t f :=
  ⟨⟨hf.1.choose, hsub hf.1.choose_spec⟩,
   fun x y h => hf.2.1 x y (fun i hi => h i (hsub hi)),
   hf.2.2⟩

theorem combined_spec {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hdis : Disjoint s t) (hf : Spec s f) (hg : Spec t g) :
    Spec (s ∪ t) (connect isAnd f g) := by
  rcases hf with ⟨⟨a, ha⟩, lf, zf, onesF, rf⟩
  rcases hg with ⟨_, lg, zg, onesG, rg⟩
  refine ⟨⟨a, Finset.mem_union_left _ ha⟩, ?_, ?_, ?_, ?_⟩
  · intro x y h
    simp only [connect, lf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      lg x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · cases isAnd <;> simp [connect, zf, zg]
  · cases isAnd <;> simp [connect, onesF, onesG]
  · cases isAnd with
    | false => exact or_rectangles hdis lf lg rf rg
    | true => exact and_rectangles hdis lf lg zf zg

theorem combined_treeOK {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hdis : Disjoint s t) (hf : TreeOK s f) (hg : TreeOK t g) :
    TreeOK (s ∪ t) (connect isAnd f g) := by
  rcases hf with hf0 | hf1 | hfs
  · cases isAnd with
    | false =>
      rcases hg with hg0 | hg1 | hgs
      · left; intro x; simp [connect, hf0 x, hg0 x]
      · right; left; intro x; simp [connect, hf0 x, hg1 x]
      · right; right; rw [show connect false f g = g by funext x; simp [connect, hf0 x]]
        exact spec_mono Finset.subset_union_right hgs
    | true => left; intro x; simp [connect, hf0 x]
  · cases isAnd with
    | false => right; left; intro x; simp [connect, hf1 x]
    | true =>
      rcases hg with hg0 | hg1 | hgs
      · left; intro x; simp [connect, hf1 x, hg0 x]
      · right; left; intro x; simp [connect, hf1 x, hg1 x]
      · right; right; rw [show connect true f g = g by funext x; simp [connect, hf1 x]]
        exact spec_mono Finset.subset_union_right hgs
  · rcases hg with hg0 | hg1 | hgs
    · cases isAnd with
      | false =>
        right; right; rw [show connect false f g = f by funext x; simp [connect, hg0 x]]
        exact spec_mono Finset.subset_union_left hfs
      | true => left; intro x; simp [connect, hg0 x]
    · cases isAnd with
      | false => right; left; intro x; simp [connect, hg1 x]
      | true =>
        right; right; rw [show connect true f g = f by funext x; simp [connect, hg1 x]]
        exact spec_mono Finset.subset_union_left hfs
    · right; right; exact combined_spec isAnd hdis hfs hgs

end TreeAndMatching

theorem treeOK_value {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C)
    (skip : Option ℕ) (fix : ℕ → Option Bool)
    (hfix : ∀ v, skip = some v ↔ fix v ≠ none) (hskipN : ∀ v, skip = some v → N ≤ v)
    (hNoNot : ∀ j ∈ L, fix (N + j) = none → (gateAt C j).op ≠ .not)
    (hTwo : ∀ j ∈ L, fix (N + j) = none → ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a, b] ∧ a < N + j ∧ b < N + j)
    (huniq : ∀ a, skip ≠ some a → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {w : ℕ} (hw : live N L w) :
    ∃ s : Finset (Fin N), (∀ i ∈ s, activeReach N C L skip i.val w ∧ skip ≠ some w) ∧
      TreeOK s (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix w) := by
  classical
  revert hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with low | ⟨j, hj, rfl⟩
    · let i₀ : Fin N := ⟨w, low⟩
      refine ⟨{i₀}, fun i hi => ?_, ?_⟩
      · obtain rfl := Finset.mem_singleton.mp hi
        exact ⟨.refl, fun h => by have := hskipN w h; omega⟩
      · have hfn : (fun x : Fin N → Bool =>
            value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix w) = fun x => x i₀ := by
          funext x; rw [val_raw low, dif_pos low]
        rw [hfn]
        right; right
        refine ⟨⟨i₀, by simp⟩, fun x y h => h i₀ (by simp), by simp [bits], rfl, ?_⟩
        intro a b c d ha hb _ _ hab _ _
        simp only [bits, edge, Finset.mem_singleton, Finset.mem_insert, decide_eq_false_iff_not,
          decide_eq_true_eq] at ha hb hab
        tauto
    · by_cases hsk : skip = some (N + j)
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp ((hfix (N + j)).mp hsk)
        refine ⟨∅, fun _ h => by simp at h, ?_⟩
        cases b
        · left; intro x; exact val_fixed (by omega) hb
        · right; left; intro x; exact val_fixed (by omega) hb
      · have hf : fix (N + j) = none := by by_contra hne; exact hsk ((hfix (N + j)).mpr hne)
        obtain ⟨a, b, hab, hin, ha_lt, hb_lt⟩ := hTwo j hj hf
        have ha_mem : a ∈ (gateAt C j).inputs := by simp [hin]
        have hb_mem : b ∈ (gateAt C j).inputs := by simp [hin]
        obtain ⟨sa, hsa_sub, ha_ok⟩ := ih a ha_lt (parent_live hL hj ⟨ha_mem, ha_lt⟩)
        obtain ⟨sb, hsb_sub, hb_ok⟩ := ih b hb_lt (parent_live hL hj ⟨hb_mem, hb_lt⟩)
        have hdis : Disjoint sa sb := by
          apply Finset.disjoint_left.mpr
          intro i hia hib
          obtain ⟨hra, hska⟩ := hsa_sub i hia
          obtain ⟨hrb, hskb⟩ := hsb_sub i hib
          have e_a : edgeTo N C L a (N + j) := ⟨j, hj, rfl, ha_mem, ha_lt⟩
          have e_b : edgeTo N C L b (N + j) := ⟨j, hj, rfl, hb_mem, hb_lt⟩
          exact hab (activeReach_last_eq (fun x y z _ h1 h2 h3 => huniq x h1 y z h2 h3)
            hra hrb hska hskb e_a e_b)
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
          exact List.getElem_mem _
        have hno := hNoNot j hj hf
        have h_or_and : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          rcases (hFan _ hmem).1 with ho | ho | ho
          · exact Or.inl ho
          · exact Or.inr ho
          · exact False.elim (hno ho)
        let isAnd := decide ((gateAt C j).op = .and)
        have hfn_eq : (fun x : Fin N → Bool =>
            value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix (N + j)) =
            connect isAnd
              (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix a)
              (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix b) := by
          funext x
          rw [val_gate hf, hin]
          rcases h_or_and with ho | ho <;> simp [isAnd, ho, GateOp.eval, connect, ha_lt, hb_lt]
        refine ⟨sa ∪ sb, fun i hi => ?_, ?_⟩
        · rcases Finset.mem_union.mp hi with hia | hib
          · obtain ⟨hra, hska⟩ := hsa_sub i hia
            exact ⟨.tail hra ⟨hska, j, hj, rfl, ha_mem, ha_lt⟩, hsk⟩
          · obtain ⟨hrb, hskb⟩ := hsb_sub i hib
            exact ⟨.tail hrb ⟨hskb, j, hj, rfl, hb_mem, hb_lt⟩, hsk⟩
        · rw [hfn_eq]
          exact combined_treeOK isAnd hdis ha_ok hb_ok

theorem deduce_matching {α β : Type} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (C : Finset β) (M : α → β → Bool)
    (hinjR : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → ∃ c ∈ C, M r₁ c ≠ M r₂ c)
    (hinjC : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → ∃ r ∈ R, M r c₁ ≠ M r c₂)
    (hneR : ∀ r ∈ R, ∃ c ∈ C, M r c = true)
    (hneC : ∀ c ∈ C, ∃ r ∈ R, M r c = true)
    (hrect : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
      M r₁ c₁ = true → M r₂ c₁ = true → M r₂ c₂ = true → M r₁ c₂ = true) :
    ∃ (e : {r // r ∈ R} ≃ {c // c ∈ C}), ∀ r : {r // r ∈ R}, ∀ c : {c // c ∈ C},
      M r.1 c.1 = decide (e r = c) := by
  classical
  have uniqC : ∀ r ∈ R, ∀ c₁ ∈ C, ∀ c₂ ∈ C, M r c₁ = true → M r c₂ = true → c₁ = c₂ := by
    intro r hr c₁ hc₁ c₂ hc₂ h1 h2
    by_contra hne
    obtain ⟨r', hr', hdiff⟩ := hinjC c₁ hc₁ c₂ hc₂ hne
    cases hr'c1 : M r' c₁ <;> cases hr'c2 : M r' c₂
    · rw [hr'c1, hr'c2] at hdiff; exact hdiff rfl
    · have := hrect r' hr' r hr c₂ hc₂ c₁ hc₁ hr'c2 h2 h1
      rw [this] at hr'c1; cases hr'c1
    · have := hrect r' hr' r hr c₁ hc₁ c₂ hc₂ hr'c1 h1 h2
      rw [this] at hr'c2; cases hr'c2
    · rw [hr'c1, hr'c2] at hdiff; exact hdiff rfl
  have uniqR : ∀ c ∈ C, ∀ r₁ ∈ R, ∀ r₂ ∈ R, M r₁ c = true → M r₂ c = true → r₁ = r₂ := by
    intro c hc r₁ hr₁ r₂ hr₂ h1 h2
    by_contra hne
    obtain ⟨c', hc', hdiff⟩ := hinjR r₁ hr₁ r₂ hr₂ hne
    cases hr1c' : M r₁ c' <;> cases hr2c' : M r₂ c'
    · rw [hr1c', hr2c'] at hdiff; exact hdiff rfl
    · exact False.elim (by
        have hh := hrect r₁ hr₁ r₂ hr₂ c hc c' hc' h1 h2 hr2c'
        rw [hh] at hr1c'; cases hr1c')
    · have hh := hrect r₂ hr₂ r₁ hr₁ c hc c' hc' h2 h1 hr1c'
      rw [hh] at hr2c'; cases hr2c'
    · rw [hr1c', hr2c'] at hdiff; exact hdiff rfl
  let f : {r // r ∈ R} → {c // c ∈ C} := fun r =>
    ⟨(hneR r.1 r.2).choose, (hneR r.1 r.2).choose_spec.1⟩
  let g : {c // c ∈ C} → {r // r ∈ R} := fun c =>
    ⟨(hneC c.1 c.2).choose, (hneC c.1 c.2).choose_spec.1⟩
  have hf_true (r : {r // r ∈ R}) : M r.1 (f r).1 = true := (hneR r.1 r.2).choose_spec.2
  have hg_true (c : {c // c ∈ C}) : M (g c).1 c.1 = true := (hneC c.1 c.2).choose_spec.2
  refine ⟨⟨f, g, fun r => Subtype.ext (uniqR (f r).1 (f r).2 _ (g (f r)).2 r.1 r.2 (hg_true (f r)) (hf_true r)),
      fun c => Subtype.ext (uniqC (g c).1 (g c).2 _ (f (g c)).2 c.1 c.2 (hf_true (g c)) (hg_true c))⟩,
    fun r c => ?_⟩
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_eq]
    exact Subtype.ext (uniqC r.1 r.2 (f r).1 (f r).2 c.1 c.2 (hf_true r) h)
  · intro h
    rw [decide_eq_true_eq] at h
    rw [← h]
    exact hf_true r

-- Block C.1: Circuit Normalization & Unique Collision Structure

def Good (n m : ℕ) (A : Fin n → Fin m → Bool) : Prop :=
  let lr := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let lc := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  Function.Injective A ∧ Function.Injective (fun j i => A i j) ∧
  (∀ i, ∃ k, ¬ (lr i k ∨ lr k i)) ∧ (∀ j, ∃ l, ¬ (lc j l ∨ lc l j)) ∧
  ∃ C : Circuit, FanInTwo C ∧ Represents A C ∧ C.size ≤ n + m - 1 ∧ ∃ g ∈ C.gates, g.op = .not

def oneEachRaw (n m : ℕ) (i : Fin n) (j : Fin m) (w : ℕ) : Bool :=
  decide (w = i.val ∨ w = n + j.val)

theorem oneEach_getD (n m : ℕ) (i : Fin n) (j : Fin m) (w : ℕ) :
    (oneEach i j).getD w false = oneEachRaw n m i j w := by
  unfold oneEach oneEachRaw
  by_cases hw : w < n + m
  · by_cases hwn : w < n
    · rw [List.getD_append _ _ _ _ (by simp [hwn])]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hwn, ↓reduceDIte, Option.getD_some,
        Fin.ext_iff]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · exact Or.inl
      · rintro (rfl | h)
        · rfl
        · omega
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        show w - n < m by omega, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      have hge : n ≤ w := Nat.le_of_not_lt hwn
      have : n + (w - n) = w := Nat.add_sub_of_le hge
      constructor
      · intro h; right; omega
      · rintro (h | h)
        · have := i.isLt; omega
        · omega
  · rw [List.getD_eq_default _ false (by simp [oneEach]; omega)]
    apply Eq.symm
    simp only [decide_eq_false_iff_not, not_or]
    exact ⟨by have := i.isLt; omega, by have := j.isLt; omega⟩

theorem oneEach_eval {n m : ℕ} (C : Circuit) {L : Finset ℕ} (hL : closed (n + m) C L)
    {r : ℕ} (hr : r ∈ L) (hout : C.output = n + m + r)
    {A : Fin n → Fin m → Bool} (hrep : Represents A C) (i : Fin n) (j : Fin m) :
    value (n + m) C (oneEachRaw n m i j) (fun _ => none) (n + m + r) = A i j := by
  have hlen : (oneEach i j).length = n + m := by simp [oneEach]
  have hv := eval_eq_value C hlen hL hr hout
  rw [← hrep i j, hv]
  congr 1
  funext w
  exact (oneEach_getD n m i j w).symm

theorem no_empty_or_full_row {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hinc : ∀ i : Fin n, ∃ k : Fin n, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (i : Fin n) : (∃ j, A i j = true) ∧ (∃ j, A i j = false) := by
  obtain ⟨k, hk⟩ := hinc i
  constructor
  · by_contra hno
    apply hk; left; intro j hj
    exact False.elim (hno ⟨j, hj⟩)
  · by_contra hno
    apply hk; right; intro j _
    by_contra hf
    have hft : A i j = false := Bool.eq_false_iff.mpr hf
    exact hno ⟨j, hft⟩

theorem no_empty_or_full_col {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hinc : ∀ j : Fin m, ∃ l : Fin m, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (j : Fin m) : (∃ i, A i j = true) ∧ (∃ i, A i j = false) :=
  no_empty_or_full_row (n := m) (m := n) (A := fun j i => A i j) hinc j

theorem oneEach_len {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by simp [oneEach]

theorem circuit_eval_lt (C : Circuit) (x : List Bool) (ho : C.output < x.length) :
    C.eval x = x.getD C.output false :=
  foldl_step_pre C.gates x ho

theorem circuit_eval_ge (C : Circuit) (x : List Bool) (ho : x.length + C.size ≤ C.output) :
    C.eval x = false :=
  getD_foldl_ge C.gates x ho

theorem root_bounds_good {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) {A : Fin n → Fin m → Bool}
    (hg : Good n m A) {E : Circuit} (hrep : Represents A E) :
    n + m ≤ E.output ∧ E.output < n + m + E.size := by
  have hrow := no_empty_or_full_row hg.2.2.1
  have hcol := no_empty_or_full_col hg.2.2.2.1
  constructor
  · by_contra hlt
    have ho : E.output < n + m := Nat.lt_of_not_le hlt
    by_cases hn_out : E.output < n
    · let c0 : Fin m := ⟨0, by omega⟩
      let c1 : Fin m := ⟨1, by omega⟩
      have hc : c0 ≠ c1 := by intro h; have := congrArg Fin.val h; contradiction
      apply hc
      apply hg.2.1
      funext i
      dsimp only
      have he0 := circuit_eval_lt E (oneEach i c0) (by rw [oneEach_len]; exact ho)
      have he1 := circuit_eval_lt E (oneEach i c1) (by rw [oneEach_len]; exact ho)
      rw [← hrep i c0, ← hrep i c1, he0, he1, oneEach_getD, oneEach_getD]
      apply Bool.eq_iff_iff.mpr
      simp only [oneEachRaw, decide_eq_true_eq]
      have h0 : E.output ≠ n + c0.val := by dsimp [c0]; omega
      have h1 : E.output ≠ n + c1.val := by dsimp [c1]; omega
      exact ⟨fun h => Or.inl (h.resolve_right h0), fun h => Or.inl (h.resolve_right h1)⟩
    · let r0 : Fin n := ⟨0, by omega⟩
      let r1 : Fin n := ⟨1, by omega⟩
      have hr : r0 ≠ r1 := by intro h; have := congrArg Fin.val h; contradiction
      apply hr
      apply hg.1
      funext j
      have he0 := circuit_eval_lt E (oneEach r0 j) (by rw [oneEach_len]; exact ho)
      have he1 := circuit_eval_lt E (oneEach r1 j) (by rw [oneEach_len]; exact ho)
      rw [← hrep r0 j, ← hrep r1 j, he0, he1, oneEach_getD, oneEach_getD]
      apply Bool.eq_iff_iff.mpr
      simp only [oneEachRaw, decide_eq_true_eq]
      have h0 : E.output ≠ r0.val := by dsimp [r0]; omega
      have h1 : E.output ≠ r1.val := by dsimp [r1]; omega
      exact ⟨fun h => Or.inr (h.resolve_left h0), fun h => Or.inr (h.resolve_left h1)⟩
  · by_contra hge
    have ho : n + m + E.size ≤ E.output := Nat.le_of_not_lt hge
    let r0 : Fin n := ⟨0, by omega⟩
    obtain ⟨j, hj⟩ := (hrow r0).1
    have he := (hrep r0 j).trans hj
    have hge0 := circuit_eval_ge E (oneEach r0 j) (by rw [oneEach_len]; exact ho)
    rw [hge0] at he
    exact Bool.false_ne_true he

theorem reaches_root_iff_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (hL : closed N C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i))
    {w : ℕ} (hw : w < N) :
    reaches N C L w (N + r) ↔ w ∈ used N C L := by
  constructor
  · intro h
    rcases h.cases_head with h_eq | ⟨b, heb, _⟩
    · omega
    · obtain ⟨j, hj, rfl, hbef⟩ := heb
      exact mem_used.mpr ⟨j, hj, hbef⟩
  · exact used_reaches_root hL huse

theorem activeReach_none_iff {N : ℕ} {C : Circuit} {L : Finset ℕ} {u v : ℕ} :
    activeReach N C L none u v ↔ reaches N C L u v := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ he ih => exact .tail ih he.2
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ he ih => exact .tail ih ⟨by simp, he⟩

theorem activeNot_pos {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hFan : FanInTwo E) (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hrep : Represents A E) (hsz : E.size ≤ n + m - 1) (hhas : ∃ g ∈ E.gates, g.op = .not)
    {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i)) :
    0 < (activeNot E L).card := by
  by_contra hzero
  have hzero_eq : (activeNot E L).card = 0 := by omega
  have hno : ∀ j ∈ L, (gateAt E j).op ≠ .not := by
    intro j hj heq
    have hmem : j ∈ activeNot E L := mem_activeNot.mpr ⟨hj, heq⟩
    have hpos : 0 < (activeNot E L).card := Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  have hnoRow : missingRows n m E L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i₀ hi₀
    have hnotused : i₀.val ∉ used (n + m) E L := (Finset.mem_filter.mp hi₀).2
    have haway : ¬ activeReach (n + m) E L none i₀.val (n + m + r) := by
      rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := i₀.isLt; omega)]
      exact hnotused
    obtain ⟨k, hk⟩ := hg.2.2.1 i₀
    apply hk; left; intro j hij
    let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
    have h1 := oneEach_eval E hL hr hout hrep i₀ j
    have h2 := oneEach_eval E hL hr hout hrep k j
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := i₀.val)
      (x := oneEachRaw n m i₀ j) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hmono := eval_monotone_of_no_not hL hno hFan
      (x := z0) (y := oneEachRaw n m k j) (fix := fun _ => none)
      (fun w _ hw => by simp only [z0, oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
      (fun _ => rfl) (Or.inr ⟨r, hr, rfl⟩)
    rw [← h2]; apply hmono; rw [← hagree, h1]; exact hij
  have hnoCol : missingCols n m E L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j₀ hj₀
    have hnotused : n + j₀.val ∉ used (n + m) E L := (Finset.mem_filter.mp hj₀).2
    have haway : ¬ activeReach (n + m) E L none (n + j₀.val) (n + m + r) := by
      rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := j₀.isLt; omega)]
      exact hnotused
    obtain ⟨l, hl⟩ := hg.2.2.2.1 j₀
    apply hl; left; intro i hij
    let z0 : ℕ → Bool := fun w => decide (w = i.val)
    have h1 := oneEach_eval E hL hr hout hrep i j₀
    have h2 := oneEach_eval E hL hr hout hrep i l
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := n + j₀.val)
      (x := oneEachRaw n m i j₀) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hmono := eval_monotone_of_no_not hL hno hFan
      (x := z0) (y := oneEachRaw n m i l) (fix := fun _ => none)
      (fun w _ hw => by simp only [z0, oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
      (fun _ => rfl) (Or.inr ⟨r, hr, rfl⟩)
    rw [← h2]; apply hmono; rw [← hagree, h1]; exact hij
  have hpart := input_partition n m E L
  rw [hnoRow, hnoCol, Finset.card_empty, Finset.card_empty] at hpart
  have hlow := slots_count_low hr huse
  have hcap : (used (n + m) E L).card ≤ (slots (n + m) E L).card := Finset.card_image_le
  have hhigh := slots_count_high hL hFan hNotLen
  have hL_ge : n + m - 1 ≤ L.card := by
    have hp : 0 < L.card := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  obtain ⟨g₀, hg₀_mem, hg₀_not⟩ := hhas
  obtain ⟨j₀, hj₀_lt, hj₀_eq⟩ := List.mem_iff_getElem.mp hg₀_mem
  have hj₀_notL : j₀ ∉ L := fun hj₀L =>
    hno j₀ hj₀L (by rw [gateAt, List.getD_eq_getElem _ _ hj₀_lt, hj₀_eq]; exact hg₀_not)
  have hsub : L ⊆ (Finset.range E.gates.length).erase j₀ := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun e => hj₀_notL (e ▸ hk), Finset.mem_range.mpr (hL.1 k hk)⟩
  have hL_le := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj₀_lt), Finset.card_range] at hL_le
  change E.gates.length ≤ n + m - 1 at hsz
  omega

theorem huniq_of_inj {N : ℕ} {E : Circuit} {L : Finset ℕ}
    (hinj : Set.InjOn Prod.snd (slots N E L : Set (ℕ × ℕ)))
    (a b c : ℕ) (hb : edgeTo N E L a b) (hc : edgeTo N E L a c) : b = c := by
  obtain ⟨j₁, hj₁, rfl, hbef₁⟩ := hb
  obtain ⟨j₂, hj₂, rfl, hbef₂⟩ := hc
  exact congrArg (N + ·) (unique_reader_of_inj hinj hj₁ hj₂ hbef₁ hbef₂)

theorem missingRows_empty_of_inj {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hFan : FanInTwo E) (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hrep : Represents A E) {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i))
    (hinj : Set.InjOn Prod.snd (slots (n + m) E L : Set (ℕ × ℕ))) :
    missingRows n m E L = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i₀ hi₀
  have hnotused : i₀.val ∉ used (n + m) E L := (Finset.mem_filter.mp hi₀).2
  have haway : ¬ activeReach (n + m) E L none i₀.val (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := i₀.isLt; omega)]
    exact hnotused
  obtain ⟨k, hk⟩ := hg.2.2.1 i₀
  obtain ⟨s, hs⟩ := single_path_unate hL hFan hNotLen (skip := none) (fix := fun _ => none)
    (fun _ => by simp) (fun _ h => by cases h) (i := k.val) (by have := k.isLt; omega)
    (fun a b c _ _ hb hc => huniq_of_inj hinj a b c hb hc)
    (Or.inr ⟨r, hr, rfl⟩)
  apply hk
  cases hs_val : s
  · right; intro j hkj
    let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
    have h1 := oneEach_eval E hL hr hout hrep i₀ j
    have h2 := oneEach_eval E hL hr hout hrep k j
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := i₀.val)
      (x := oneEachRaw n m i₀ j) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hsp := (hs z0 (oneEachRaw n m k j)
      (fun w _ hwne => by
        simp only [z0, oneEachRaw, decide_eq_decide]
        exact ⟨Or.inr, fun h => h.resolve_left hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inr h)).2 hs_val
    rw [← h1, hagree]; apply hsp; rw [h2]; exact hkj
  · left; intro j hij
    let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
    have h1 := oneEach_eval E hL hr hout hrep i₀ j
    have h2 := oneEach_eval E hL hr hout hrep k j
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := i₀.val)
      (x := oneEachRaw n m i₀ j) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hsp := (hs z0 (oneEachRaw n m k j)
      (fun w _ hwne => by
        simp only [z0, oneEachRaw, decide_eq_decide]
        exact ⟨Or.inr, fun h => h.resolve_left hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inr h)).1 hs_val
    rw [← h2]; apply hsp; rw [← hagree, h1]; exact hij

theorem missingCols_empty_of_inj {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hFan : FanInTwo E) (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hrep : Represents A E) {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i))
    (hinj : Set.InjOn Prod.snd (slots (n + m) E L : Set (ℕ × ℕ))) :
    missingCols n m E L = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j₀ hj₀
  have hnotused : n + j₀.val ∉ used (n + m) E L := (Finset.mem_filter.mp hj₀).2
  have haway : ¬ activeReach (n + m) E L none (n + j₀.val) (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := j₀.isLt; omega)]
    exact hnotused
  obtain ⟨l, hl⟩ := hg.2.2.2.1 j₀
  obtain ⟨s, hs⟩ := single_path_unate hL hFan hNotLen (skip := none) (fix := fun _ => none)
    (fun _ => by simp) (fun _ h => by cases h) (i := n + l.val) (by have := l.isLt; omega)
    (fun a b c _ _ hb hc => huniq_of_inj hinj a b c hb hc)
    (Or.inr ⟨r, hr, rfl⟩)
  apply hl
  cases hs_val : s
  · right; intro i hil
    let z0 : ℕ → Bool := fun w => decide (w = i.val)
    have h1 := oneEach_eval E hL hr hout hrep i j₀
    have h2 := oneEach_eval E hL hr hout hrep i l
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := n + j₀.val)
      (x := oneEachRaw n m i j₀) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hsp := (hs z0 (oneEachRaw n m i l)
      (fun w _ hwne => by
        simp only [z0, oneEachRaw, decide_eq_decide]
        exact ⟨Or.inl, fun h => h.resolve_right hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inl h)).2 hs_val
    rw [← h1, hagree]; apply hsp; rw [h2]; exact hil
  · left; intro i hij
    let z0 : ℕ → Bool := fun w => decide (w = i.val)
    have h1 := oneEach_eval E hL hr hout hrep i j₀
    have h2 := oneEach_eval E hL hr hout hrep i l
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) hL
      (fun _ => by simp) (fun _ h => by cases h) (i := n + j₀.val)
      (x := oneEachRaw n m i j₀) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
      (Or.inr ⟨r, hr, rfl⟩) haway
    have hsp := (hs z0 (oneEachRaw n m i l)
      (fun w _ hwne => by
        simp only [z0, oneEachRaw, decide_eq_decide]
        exact ⟨Or.inl, fun h => h.resolve_right hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inl h)).1 hs_val
    rw [← h2]; apply hsp; rw [← hagree, h1]; exact hij

theorem not_injOn_slots {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hFan : FanInTwo E) (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hrep : Represents A E) (hsz : E.size ≤ n + m - 1) (hhas : ∃ g ∈ E.gates, g.op = .not)
    {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i)) :
    ¬ Set.InjOn Prod.snd (slots (n + m) E L : Set (ℕ × ℕ)) := by
  intro hinj
  have hnoRow := missingRows_empty_of_inj hg hFan hNotLen hrep hr hL hout huse hinj
  have hnoCol := missingCols_empty_of_inj hg hFan hNotLen hrep hr hL hout huse hinj
  have hpart := input_partition n m E L
  rw [hnoRow, hnoCol, Finset.card_empty, Finset.card_empty] at hpart
  have hlow := slots_count_low hr huse
  have hcard_eq : (used (n + m) E L).card = (slots (n + m) E L).card := by
    unfold used; exact Finset.card_image_of_injOn hinj
  have hhigh := slots_count_high hL hFan hNotLen
  have hpos := activeNot_pos hg hFan hNotLen hrep hsz hhas hr hL hout huse
  have hL_le : L.card ≤ n + m - 1 := by
    have hsub : L ⊆ Finset.range E.gates.length := fun k hk => Finset.mem_range.mpr (hL.1 k hk)
    exact (Finset.card_le_card hsub).trans ((Finset.card_range _).le.trans hsz)
  have hLp : 0 < L.card := Finset.card_pos.mpr ⟨r, hr⟩
  omega

theorem missingRows_le_one {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hrep : Represents A E)
    {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i)) :
    (missingRows n m E L).card ≤ 1 := by
  by_contra hlt
  have hgt : 1 < (missingRows n m E L).card := Nat.lt_of_not_le hlt
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp hgt
  have h1 : ¬ activeReach (n + m) E L none r₁.val (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := r₁.isLt; omega)]
    exact (Finset.mem_filter.mp hr₁).2
  have h2 : ¬ activeReach (n + m) E L none r₂.val (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := r₂.isLt; omega)]
    exact (Finset.mem_filter.mp hr₂).2
  apply hne; apply hg.1; funext j
  let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
  rw [← oneEach_eval E hL hr hout hrep r₁ j, ← oneEach_eval E hL hr hout hrep r₂ j]
  have a1 := unate_unchanged (skip := none) (fix := fun _ => none) hL
    (fun _ => by simp) (fun _ h => by cases h) (i := r₁.val)
    (x := oneEachRaw n m r₁ j) (y := z0)
    (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
    (Or.inr ⟨r, hr, rfl⟩) h1
  have a2 := unate_unchanged (skip := none) (fix := fun _ => none) hL
    (fun _ => by simp) (fun _ h => by cases h) (i := r₂.val)
    (x := oneEachRaw n m r₂ j) (y := z0)
    (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
    (Or.inr ⟨r, hr, rfl⟩) h2
  exact a1.trans a2.symm

theorem missingCols_le_one {n m : ℕ} {A : Fin n → Fin m → Bool} (hg : Good n m A)
    {E : Circuit} (hrep : Represents A E)
    {L : Finset ℕ} {r : ℕ} (hr : r ∈ L) (hL : closed (n + m) E L)
    (hout : E.output = n + m + r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i)) :
    (missingCols n m E L).card ≤ 1 := by
  by_contra hlt
  have hgt : 1 < (missingCols n m E L).card := Nat.lt_of_not_le hlt
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp hgt
  have h1 : ¬ activeReach (n + m) E L none (n + c₁.val) (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := c₁.isLt; omega)]
    exact (Finset.mem_filter.mp hc₁).2
  have h2 : ¬ activeReach (n + m) E L none (n + c₂.val) (n + m + r) := by
    rw [activeReach_none_iff, reaches_root_iff_used hr hL huse (by have := c₂.isLt; omega)]
    exact (Finset.mem_filter.mp hc₂).2
  apply hne; apply hg.2.1; funext i; dsimp only
  let z0 : ℕ → Bool := fun w => decide (w = i.val)
  rw [← oneEach_eval E hL hr hout hrep i c₁, ← oneEach_eval E hL hr hout hrep i c₂]
  have a1 := unate_unchanged (skip := none) (fix := fun _ => none) hL
    (fun _ => by simp) (fun _ h => by cases h) (i := n + c₁.val)
    (x := oneEachRaw n m i c₁) (y := z0)
    (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
    (Or.inr ⟨r, hr, rfl⟩) h1
  have a2 := unate_unchanged (skip := none) (fix := fun _ => none) hL
    (fun _ => by simp) (fun _ h => by cases h) (i := n + c₂.val)
    (x := oneEachRaw n m i c₂) (y := z0)
    (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
    (Or.inr ⟨r, hr, rfl⟩) h2
  exact a1.trans a2.symm

structure CollisionData (n m : ℕ) (A : Fin n → Fin m → Bool) where
  E : Circuit
  r : ℕ
  L : Finset ℕ
  r₀ : Fin n
  c₀ : Fin m
  j_not : ℕ
  f : ℕ
  j₁ : ℕ
  j₂ : ℕ
  hFan : FanInTwo E
  hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1
  hL : closed (n + m) E L
  hrL : r ∈ L
  hout : E.output = n + m + r
  huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before E (n + m) j (n + m + i)
  hRep : ∀ i j, value (n + m) E (oneEachRaw n m i j) (fun _ => none) (n + m + r) = A i j
  hFull : L = Finset.range (n + m - 1)
  hSize : E.gates.length = n + m - 1
  hr0 : ∀ i : Fin n, i.val ∉ used (n + m) E L ↔ i = r₀
  hc0 : ∀ j : Fin m, n + j.val ∉ used (n + m) E L ↔ j = c₀
  hjnot : ∀ j ∈ L, (gateAt E j).op = .not ↔ j = j_not
  hjnotL : j_not ∈ L
  hjnot_in : ∃ u_not, (gateAt E j_not).inputs = [u_not] ∧ u_not < n + m + j_not
  hother_two : ∀ j ∈ L, j ≠ j_not →
    ((gateAt E j).op = .and ∨ (gateAt E j).op = .or) ∧
    ∃ a b, a ≠ b ∧ (gateAt E j).inputs = [a, b] ∧ a < n + m + j ∧ b < n + m + j
  hf_used : f ∈ used (n + m) E L
  hj1L : j₁ ∈ L
  hj2L : j₂ ∈ L
  hj12 : j₁ ≠ j₂
  hf_j1 : before E (n + m) j₁ f
  hf_j2 : before E (n + m) j₂ f
  hsingle : ∀ a, a ≠ f → ∀ b c, edgeTo (n + m) E L a b → edgeTo (n + m) E L a c → b = c
  hf_two : ∀ j ∈ L, before E (n + m) j f → j = j₁ ∨ j = j₂

def slotPts (N : ℕ) (E : Circuit) (k : ℕ) : ℕ :=
  (inputSlots N E k).card + cond (isNotGate E k) 1 0

theorem slotPts_le {N : ℕ} {E : Circuit} {L : Finset ℕ}
    (hL : closed N E L) (hFan : FanInTwo E)
    (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    {k : ℕ} (hk : k ∈ L) : slotPts N E k ≤ 2 := by
  have hmem : gateAt E k ∈ E.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ (hL.1 k hk)]
    exact List.getElem_mem _
  have hw : (inputSlots N E k).card ≤ (gateAt E k).inputs.length := by
    rw [inputSlots_card]
    exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
  unfold slotPts
  cases hn' : isNotGate E k
  · dsimp [cond]
    exact (hw.trans (hFan _ hmem).2).trans (le_refl 2)
  · dsimp [cond]
    exact Nat.add_le_add_right (hw.trans (hNotLen _ hmem (isNotGate_eq_true.mp hn'))) 1

theorem slotPts_sum_ge (N : ℕ) (E : Circuit) (L : Finset ℕ) :
    (slots N E L).card + (activeNot E L).card ≤ ∑ k ∈ L, slotPts N E k := by
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N E)
  have han : (activeNot E L).card = ∑ k ∈ L, cond (isNotGate E k) 1 0 := by
    unfold activeNot; rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases isNotGate E k <;> rfl
  have hslots' : (slots N E L).card ≤ ∑ k ∈ L, (inputSlots N E k).card := hslots
  have hdist : ∑ k ∈ L, slotPts N E k =
      (∑ k ∈ L, (inputSlots N E k).card) + ∑ k ∈ L, cond (isNotGate E k) 1 0 := by
    simp only [slotPts, Finset.sum_add_distrib]
  rw [hdist, ← han]
  exact Nat.add_le_add_right hslots' _

theorem slotPts_eq_two {N : ℕ} {E : Circuit} {L : Finset ℕ}
    (hL : closed N E L) (hFan : FanInTwo E)
    (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hpts_sum : 2 * L.card ≤ ∑ m ∈ L, slotPts N E m)
    {k : ℕ} (hk : k ∈ L) : slotPts N E k = 2 := by
  have h1 := Finset.sum_erase_add L (slotPts N E) hk
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨k, hk⟩
  have h2 : ∑ m ∈ L.erase k, slotPts N E m ≤ 2 * (L.card - 1) := by
    calc ∑ m ∈ L.erase k, slotPts N E m ≤ ∑ _ ∈ L.erase k, (2 : ℕ) :=
          Finset.sum_le_sum fun m hm => slotPts_le hL hFan hNotLen (Finset.mem_of_mem_erase hm)
      _ = 2 * (L.card - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hk, Nat.mul_comm]
  rw [← h1] at hpts_sum
  have hk_le := slotPts_le hL hFan hNotLen hk
  omega

theorem unary_inputs_eq_singleton {N : ℕ} {E : Circuit} {L : Finset ℕ}
    (hL : closed N E L) (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    {j : ℕ} (hj : j ∈ L) (ho : (gateAt E j).op = .not)
    (hcard1 : (inputSlots N E j).card = 1) :
    ∃ u, (gateAt E j).inputs = [u] ∧ u < N + j := by
  rw [inputSlots_card] at hcard1
  have hmem : gateAt E j ∈ E.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
    exact List.getElem_mem _
  have hlen1 := hNotLen _ hmem ho
  obtain ⟨u, hu⟩ := Finset.card_pos.mp
    (by omega : 0 < ((gateAt E j).inputs.toFinset.filter (· < N + j)).card)
  rw [Finset.mem_filter, List.mem_toFinset] at hu
  rcases h : (gateAt E j).inputs with _ | ⟨x, tl⟩
  · rw [h] at hu; exact False.elim (List.not_mem_nil hu.1)
  · have htl : tl = [] := by
      rw [h] at hlen1
      exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hlen1))
    subst htl
    rw [h] at hu
    have hux : u = x := by simpa using hu.1
    subst hux
    exact ⟨u, rfl, hu.2⟩

theorem finset_not_injOn_witness (s : Finset (ℕ × ℕ))
    (hNotInj : ¬ Set.InjOn Prod.snd (s : Set (ℕ × ℕ))) :
    ∃ p₁ ∈ s, ∃ p₂ ∈ s, p₁.2 = p₂.2 ∧ p₁ ≠ p₂ := by
  by_contra hno
  apply hNotInj
  intro p₁ hp₁ p₂ hp₂ heq
  by_contra hpne
  exact hno ⟨p₁, hp₁, p₂, hp₂, heq, hpne⟩

theorem finset_erase_injOn (s : Finset (ℕ × ℕ)) (p₁ p₂ : ℕ × ℕ)
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (hf : p₁.2 = p₂.2) (hne : p₁ ≠ p₂)
    (hcard : (s.image Prod.snd).card + 1 = s.card) :
    Set.InjOn Prod.snd ((s.erase p₁ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  have himg : (s.erase p₁).image Prod.snd = s.image Prod.snd := by
    ext w
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      by_cases e : p = p₁
      · rw [e]; exact ⟨p₂, ⟨hne.symm, h₂⟩, hf.symm⟩
      · exact ⟨p, ⟨e, hp⟩, rfl⟩
  have hc : ((s.erase p₁).image Prod.snd).card = (s.erase p₁).card := by
    rw [himg, Finset.card_erase_of_mem h₁, ← hcard]
    exact (Nat.add_sub_cancel _ 1).symm
  exact Finset.injOn_of_card_image_eq hc

theorem single_reader_of_not_inj {N : ℕ} {E : Circuit} {L : Finset ℕ}
    (hS_lt : (used N E L).card + 1 = (slots N E L).card)
    (hNotInj : ¬ Set.InjOn Prod.snd (slots N E L : Set (ℕ × ℕ))) :
    ∃ f j₁ j₂, j₁ ∈ L ∧ j₂ ∈ L ∧ j₁ ≠ j₂ ∧ before E N j₁ f ∧ before E N j₂ f ∧
      f ∈ used N E L ∧ (∀ a, a ≠ f → ∀ b c, edgeTo N E L a b → edgeTo N E L a c → b = c) ∧
      (∀ j ∈ L, before E N j f → j = j₁ ∨ j = j₂) := by
  obtain ⟨⟨j₁, f₁⟩, h₁, ⟨j₂, f₂⟩, h₂, hf_eq, hne_p⟩ :=
    finset_not_injOn_witness (slots N E L) hNotInj
  dsimp only at hf_eq
  have hS'_inj := finset_erase_injOn (slots N E L) (j₁, f₁) (j₂, f₂) h₁ h₂ hf_eq hne_p hS_lt
  rw [← hf_eq] at h₂ hne_p
  have hj12 : j₁ ≠ j₂ := fun e => hne_p (by rw [e])
  obtain ⟨hj1L, hbef1⟩ := mem_slot.mp h₁
  obtain ⟨hj2L, hbef2⟩ := mem_slot.mp h₂
  have hsingle : ∀ a, a ≠ f₁ → ∀ b c, edgeTo N E L a b → edgeTo N E L a c → b = c := by
    intro a haf b c ⟨kb, hkbL, hb, hkb⟩ ⟨kc, hkcL, hc, hkc⟩
    subst hb hc
    have hb_mem : (kb, a) ∈ (slots N E L).erase (j₁, f₁) :=
      Finset.mem_erase.mpr ⟨fun h => haf (congrArg Prod.snd h), mem_slot.mpr ⟨hkbL, hkb⟩⟩
    have hc_mem : (kc, a) ∈ (slots N E L).erase (j₁, f₁) :=
      Finset.mem_erase.mpr ⟨fun h => haf (congrArg Prod.snd h), mem_slot.mpr ⟨hkcL, hkc⟩⟩
    exact congrArg (N + ·) (congrArg Prod.fst (hS'_inj hb_mem hc_mem rfl))
  have htwo : ∀ j ∈ L, before E N j f₁ → j = j₁ ∨ j = j₂ := by
    intro j hj hbef
    by_cases e : j = j₁
    · exact Or.inl e
    · have hp_mem : (j, f₁) ∈ (slots N E L).erase (j₁, f₁) :=
        Finset.mem_erase.mpr ⟨fun h => e (congrArg Prod.fst h), mem_slot.mpr ⟨hj, hbef⟩⟩
      have hp2_mem : (j₂, f₁) ∈ (slots N E L).erase (j₁, f₁) :=
        Finset.mem_erase.mpr ⟨fun h => hj12.symm (congrArg Prod.fst h), h₂⟩
      exact Or.inr (congrArg Prod.fst (hS'_inj hp_mem hp2_mem rfl))
  exact ⟨f₁, j₁, j₂, hj1L, hj2L, hj12, hbef1, hbef2, mem_used.mpr ⟨j₁, hj1L, hbef1⟩, hsingle, htwo⟩

theorem extract_collision_of {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    {A : Fin n → Fin m → Bool} (hg : Good n m A)
    (E : Circuit) (hFan : FanInTwo E)
    (hNotLen : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1)
    (hRep_trim : Represents A E) (hSz : E.size ≤ n + m - 1)
    (hHas : ∃ g ∈ E.gates, g.op = .not) :
    Nonempty (CollisionData n m A) := by
  classical
  obtain ⟨hlo, hhi⟩ := root_bounds_good hn hm hg hRep_trim
  obtain ⟨r, hout⟩ : ∃ r, E.output = n + m + r := ⟨E.output - (n + m), by omega⟩
  have hr_lt : r < E.gates.length := by
    have : E.output < n + m + E.gates.length := hhi
    omega
  obtain ⟨L, hrL, hL, huse⟩ := minimal_closed (n + m) E r hr_lt
  have hPos := activeNot_pos hg hFan hNotLen hRep_trim hSz hHas hrL hL hout huse
  have hNotInj := not_injOn_slots hg hFan hNotLen hRep_trim hSz hHas hrL hL hout huse
  have hMR := missingRows_le_one hg hRep_trim hrL hL hout huse
  have hMC := missingCols_le_one hg hRep_trim hrL hL hout huse
  have hpart := input_partition n m E L
  have hlow := slots_count_low hrL huse
  have hhigh := slots_count_high hL hFan hNotLen
  have hlt_slots : (used (n + m) E L).card < (slots (n + m) E L).card := by
    by_contra hle
    unfold used at hle
    exact hNotInj (Finset.injOn_of_card_image_eq (Nat.le_antisymm Finset.card_image_le (Nat.le_of_not_lt hle)))
  have hL_sub : L ⊆ Finset.range E.gates.length := fun k hk => Finset.mem_range.mpr (hL.1 k hk)
  have hL_le : L.card ≤ E.gates.length := (Finset.card_le_card hL_sub).trans (by rw [Finset.card_range])
  have hE_le : E.gates.length ≤ n + m - 1 := hSz
  have hLp : 0 < L.card := Finset.card_pos.mpr ⟨r, hrL⟩
  have hMR1 : (missingRows n m E L).card = 1 := by omega
  have hMC1 : (missingCols n m E L).card = 1 := by omega
  have hAN1 : (activeNot E L).card = 1 := by omega
  have hL_eq : L.card = n + m - 1 := by omega
  have hE_eq : E.gates.length = n + m - 1 := by omega
  have hFull : L = Finset.range (n + m - 1) := by
    have := Finset.eq_of_subset_of_card_le hL_sub (by rw [Finset.card_range]; omega)
    rw [this, hE_eq]
  have hS_lt : (used (n + m) E L).card + 1 = (slots (n + m) E L).card := by omega
  have hSum_eq : (slots (n + m) E L).card + (activeNot E L).card = 2 * L.card := by omega
  obtain ⟨r₀, hr₀_eq⟩ := Finset.card_eq_one.mp hMR1
  obtain ⟨c₀, hc₀_eq⟩ := Finset.card_eq_one.mp hMC1
  obtain ⟨j_not, hjnot_eq⟩ := Finset.card_eq_one.mp hAN1
  have hr₀_iff (i : Fin n) : i.val ∉ used (n + m) E L ↔ i = r₀ := by
    have : i ∈ missingRows n m E L ↔ i = r₀ := by rw [hr₀_eq, Finset.mem_singleton]
    simpa [missingRows] using this
  have hc₀_iff (j : Fin m) : n + j.val ∉ used (n + m) E L ↔ j = c₀ := by
    have : j ∈ missingCols n m E L ↔ j = c₀ := by rw [hc₀_eq, Finset.mem_singleton]
    simpa [missingCols] using this
  have hjnotL : j_not ∈ L := (mem_activeNot.mp (by rw [hjnot_eq]; exact Finset.mem_singleton_self _)).1
  have hjnot_iff (j : ℕ) (hj : j ∈ L) : (gateAt E j).op = .not ↔ j = j_not := by
    constructor
    · intro ho
      have hmem : j ∈ activeNot E L := mem_activeNot.mpr ⟨hj, ho⟩
      rw [hjnot_eq, Finset.mem_singleton] at hmem; exact hmem
    · rintro rfl
      exact (mem_activeNot.mp (by rw [hjnot_eq]; exact Finset.mem_singleton_self _)).2
  have hpts_exact (k : ℕ) (hk : k ∈ L) : slotPts (n + m) E k = 2 :=
    slotPts_eq_two hL hFan hNotLen (hSum_eq ▸ slotPts_sum_ge (n + m) E L) hk
  have hjnot_in : ∃ u_not, (gateAt E j_not).inputs = [u_not] ∧ u_not < n + m + j_not := by
    have hp := hpts_exact j_not hjnotL
    have ho : (gateAt E j_not).op = .not := (hjnot_iff j_not hjnotL).mpr rfl
    have hnt : isNotGate E j_not = true := isNotGate_eq_true.mpr ho
    dsimp [slotPts] at hp; rw [hnt] at hp; dsimp [cond] at hp
    have hcard1 : (inputSlots (n + m) E j_not).card = 1 := by omega
    exact unary_inputs_eq_singleton hL hNotLen hjnotL ho hcard1
  have hother_two : ∀ j ∈ L, j ≠ j_not →
      ((gateAt E j).op = .and ∨ (gateAt E j).op = .or) ∧
      ∃ a b, a ≠ b ∧ (gateAt E j).inputs = [a, b] ∧ a < n + m + j ∧ b < n + m + j := by
    intro j hj hjne
    have hp := hpts_exact j hj
    have hmem : gateAt E j ∈ E.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
      exact List.getElem_mem _
    have hno : (gateAt E j).op ≠ .not := fun ho => hjne ((hjnot_iff j hj).mp ho)
    have h_or_and : (gateAt E j).op = .and ∨ (gateAt E j).op = .or := by
      rcases (hFan _ hmem).1 with ho | ho | ho
      · exact Or.inl ho
      · exact Or.inr ho
      · exact False.elim (hno ho)
    have hnt : isNotGate E j = false :=
      Bool.eq_false_iff.mpr fun h => hno (isNotGate_eq_true.mp h)
    dsimp [slotPts] at hp; rw [hnt] at hp; dsimp [cond] at hp
    rw [inputSlots_card] at hp
    have hlen2 := (hFan _ hmem).2
    have hle1 := List.toFinset_card_le (gateAt E j).inputs
    have hle2 := Finset.card_filter_le (gateAt E j).inputs.toFinset (· < n + m + j)
    have hlen_eq : (gateAt E j).inputs.length = 2 := by omega
    obtain ⟨a, b, hin⟩ := List.length_eq_two.mp hlen_eq
    have heq_set : (gateAt E j).inputs.toFinset.filter (· < n + m + j) = (gateAt E j).inputs.toFinset := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      omega
    have hne : a ≠ b := by
      rintro rfl
      rw [heq_set, hin] at hp
      have hcard1 : [a, a].toFinset = ({a} : Finset ℕ) := by ext x; simp
      rw [hcard1, Finset.card_singleton] at hp
      omega
    have ha_lt : a < n + m + j := by
      have ha_in : a ∈ (gateAt E j).inputs.toFinset := by simp [hin]
      rw [← heq_set] at ha_in
      exact (Finset.mem_filter.mp ha_in).2
    have hb_lt : b < n + m + j := by
      have hb_in : b ∈ (gateAt E j).inputs.toFinset := by simp [hin]
      rw [← heq_set] at hb_in
      exact (Finset.mem_filter.mp hb_in).2
    exact ⟨h_or_and, a, b, hne, hin, ha_lt, hb_lt⟩
  obtain ⟨f₁, j₁, j₂, hj1L, hj2L, hj12, hbef1, hbef2, hf_used, hsingle, hf_two⟩ :=
    single_reader_of_not_inj hS_lt hNotInj
  exact ⟨⟨E, r, L, r₀, c₀, j_not, f₁, j₁, j₂, hFan, hNotLen, hL, hrL, hout, huse,
    fun i j => oneEach_eval E hL hrL hout hRep_trim i j,
    hFull, hE_eq, hr₀_iff, hc₀_iff, hjnot_iff, hjnotL, hjnot_in, hother_two,
    hf_used, hj1L, hj2L, hj12, hbef1, hbef2, hsingle, hf_two⟩⟩

theorem extract_collision {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    {A : Fin n → Fin m → Bool} (hg : Good n m A) :
    Nonempty (CollisionData n m A) := by
  obtain ⟨C, hCfan, hCrep, hCsz, hChas⟩ := hg.2.2.2.2
  exact extract_collision_of hn hm hg (trim C) (trim_fan C hCfan) (trim_unary C)
    (fun i j => (trim_eval C (oneEach i j)).trans (hCrep i j))
    (by rw [trim_size]; exact hCsz) (trim_has_not C hChas)

-- Block C.2: Collision Geometry, Polarity, u_not = f, Singletons

theorem reaches_lt_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {u w : ℕ}
    (hw : w < N) (h : reaches N C L u w) : u = w := by
  rcases h.cases_tail with rfl | ⟨a, _, _, hj, rfl, _⟩
  · rfl
  · omega

theorem reaches_total_of_gt {N : ℕ} {C : Circuit} {L : Finset ℕ} {f : ℕ}
    (hsingle : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {u v₁ v₂ : ℕ} (hgt : f < u) (h₁ : reaches N C L u v₁) (h₂ : reaches N C L u v₂) :
    reaches N C L v₁ v₂ ∨ reaches N C L v₂ v₁ := by
  have hmain : ∀ d u, v₁ - u = d → f < u → reaches N C L u v₁ → reaches N C L u v₂ →
      reaches N C L v₁ v₂ ∨ reaches N C L v₂ v₁ := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro u hd hgt h₁ h₂
      rcases h₁.cases_head with rfl | ⟨a, ea, ha₁⟩
      · exact Or.inl h₂
      · rcases h₂.cases_head with rfl | ⟨b, eb, hb₂⟩
        · exact Or.inr (Relation.ReflTransGen.head ea ha₁)
        · have hab := hsingle u (by omega) a b ea eb
          rw [← hab] at hb₂
          have hlt1 := edgeTo_lt ea
          have hle1 := reaches_le ha₁
          exact ih (v₁ - a) (by omega) a rfl (hgt.trans hlt1) ha₁ hb₂
  exact hmain (v₁ - u) u rfl hgt h₁ h₂

theorem reaches_total_of_no_f {N : ℕ} {C : Circuit} {L : Finset ℕ} {f : ℕ}
    (hsingle : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {u v₁ v₂ : ℕ} (hnf : ¬ reaches N C L u f)
    (h₁ : reaches N C L u v₁) (h₂ : reaches N C L u v₂) :
    reaches N C L v₁ v₂ ∨ reaches N C L v₂ v₁ := by
  have hmain : ∀ d u, v₁ - u = d → ¬ reaches N C L u f → reaches N C L u v₁ → reaches N C L u v₂ →
      reaches N C L v₁ v₂ ∨ reaches N C L v₂ v₁ := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro u hd hnf h₁ h₂
      rcases h₁.cases_head with rfl | ⟨a, ea, ha₁⟩
      · exact Or.inl h₂
      · rcases h₂.cases_head with rfl | ⟨b, eb, hb₂⟩
        · exact Or.inr (Relation.ReflTransGen.head ea ha₁)
        · have huf : u ≠ f := fun heq => hnf (heq ▸ Relation.ReflTransGen.refl)
          have hab := hsingle u huf a b ea eb
          rw [← hab] at hb₂
          have hlt1 := edgeTo_lt ea
          have hle1 := reaches_le ha₁
          exact ih (v₁ - a) (by omega) a rfl (fun h => hnf (Relation.ReflTransGen.head ea h)) ha₁ hb₂
  exact hmain (v₁ - u) u rfl hnf h₁ h₂

theorem value_agree_of_fix_away {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {x : ℕ → Bool} {fix₁ fix₂ : ℕ → Option Bool}
    {w : ℕ} (hw : live N L w)
    (hdiff : ∀ v, N ≤ v → fix₁ v ≠ fix₂ v → ¬ reaches N C L v w) :
    value N C x fix₁ w = value N C x fix₂ w := by
  revert hw hdiff
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdiff
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
    · have hfeq : fix₁ (N + j) = fix₂ (N + j) := by
        by_contra hne
        exact hdiff (N + j) (by omega) hne Relation.ReflTransGen.refl
      cases hfx : fix₂ (N + j) with
      | some b =>
        have h1 : fix₁ (N + j) = some b := hfeq.trans hfx
        rw [val_fixed (by omega) h1, val_fixed (by omega) hfx]
      | none =>
        have h1 : fix₁ (N + j) = none := hfeq.trans hfx
        rw [val_gate h1, val_gate hfx]
        congr 1; apply List.map_congr_left; intro u hu
        split_ifs with hlt
        · have he : edgeTo N C L u (N + j) := ⟨j, hj, rfl, hu, hlt⟩
          exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩)
            (fun v hvN hne hr => hdiff v hvN hne (Relation.ReflTransGen.tail hr he))
        · rfl

theorem eval_mono_inputs_of_fix {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C)
    {x y : ℕ → Bool} {fix : ℕ → Option Bool}
    (hNoNot : ∀ j ∈ L, fix (N + j) = none → (gateAt C j).op ≠ .not)
    (hraw : ∀ w < N, x w = true → y w = true)
    {w : ℕ} (hw : live N L w) :
    value N C x fix w = true → value N C y fix w = true := by
  revert hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low] at hx ⊢
      exact hraw w low hx
    · by_cases hf_none : fix (N + j) = none
      · rw [val_gate hf_none] at hx ⊢
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
          exact List.getElem_mem _
        have hne := hNoNot j hj hf_none
        have h_and_or : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          rcases (hFan _ hmem).1 with ho | ho | ho
          · exact Or.inl ho
          · exact Or.inr ho
          · exact False.elim (hne ho)
        have hchild : ∀ u ∈ (gateAt C j).inputs,
            (if u < N + j then value N C x fix u else false) = true →
            (if u < N + j then value N C y fix u else false) = true := by
          intro u hu hxu
          by_cases hlt : u < N + j
          · rw [if_pos hlt] at hxu ⊢
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) hxu
          · rw [if_neg hlt] at hxu
            exact False.elim (Bool.false_ne_true hxu)
        rcases h_and_or with ha | ho
        · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
          exact fun u hu => hchild u hu (hx u hu)
        · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
          obtain ⟨u, hu, hxu⟩ := hx
          exact ⟨u, hu, hchild u hu hxu⟩
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hf_none
        rw [val_fixed (by omega) hb] at hx ⊢
        exact hx

theorem eval_mono_fix_of_no_not {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C)
    {x : ℕ → Bool} {fix₁ fix₂ : ℕ → Option Bool}
    (hNoNot₁ : ∀ j ∈ L, fix₁ (N + j) = none → (gateAt C j).op ≠ .not)
    (hfix : ∀ j ∈ L,
      (fix₁ (N + j) = none ∧ fix₂ (N + j) = none) ∨
      (∃ b₁ b₂ : Bool, fix₁ (N + j) = some b₁ ∧ fix₂ (N + j) = some b₂ ∧ (b₁ = true → b₂ = true)))
    {w : ℕ} (hw : live N L w) :
    value N C x fix₁ w = true → value N C x fix₂ w = true := by
  revert hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low] at hx ⊢; exact hx
    · rcases hfix j hj with ⟨h1, h2⟩ | ⟨b₁, b₂, h1, h2, hb⟩
      · rw [val_gate h1] at hx; rw [val_gate h2]
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
          exact List.getElem_mem _
        have hne := hNoNot₁ j hj h1
        have h_and_or : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          rcases (hFan _ hmem).1 with ho | ho | ho
          · exact Or.inl ho
          · exact Or.inr ho
          · exact False.elim (hne ho)
        have hchild : ∀ u ∈ (gateAt C j).inputs,
            (if u < N + j then value N C x fix₁ u else false) = true →
            (if u < N + j then value N C x fix₂ u else false) = true := by
          intro u hu hxu
          by_cases hlt : u < N + j
          · rw [if_pos hlt] at hxu ⊢
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) hxu
          · rw [if_neg hlt] at hxu
            exact False.elim (Bool.false_ne_true hxu)
        rcases h_and_or with ha | ho
        · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
          exact fun u hu => hchild u hu (hx u hu)
        · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
          obtain ⟨u, hu, hxu⟩ := hx
          exact ⟨u, hu, hchild u hu hxu⟩
      · rw [val_fixed (by omega) h1] at hx
        rw [val_fixed (by omega) h2]
        exact hb hx

theorem contradict_IncR_of_unate {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A)
    {k : Fin n} (hk : ¬ ((∀ j, A d.r₀ j = true → A k j = true) ∨ (∀ j, A k j = true → A d.r₀ j = true)))
    (hs : ∃ s : Bool, ∀ x y : ℕ → Bool,
      (∀ v < n + m, v ≠ k.val → x v = y v) → (x k.val = true → y k.val = true) →
      ((s = true → value (n + m) d.E x (fun _ => none) (n + m + d.r) = true →
          value (n + m) d.E y (fun _ => none) (n + m + d.r) = true) ∧
       (s = false → value (n + m) d.E y (fun _ => none) (n + m + d.r) = true →
          value (n + m) d.E x (fun _ => none) (n + m + d.r) = true))) :
    False := by
  obtain ⟨s, hs⟩ := hs
  have hr0_away : ¬ activeReach (n + m) d.E d.L none d.r₀.val (n + m + d.r) := by
    rw [activeReach_none_iff, reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  apply hk
  cases hs_val : s
  · right; intro j hkj
    let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) d.hL
      (fun _ => by simp) (fun _ h => by cases h) (i := d.r₀.val)
      (x := oneEachRaw n m d.r₀ j) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
      (Or.inr ⟨d.r, d.hrL, rfl⟩) hr0_away
    have hsp := (hs z0 (oneEachRaw n m k j)
      (fun w _ hwne => by simp only [z0, oneEachRaw, decide_eq_decide]; exact ⟨Or.inr, fun h => h.resolve_left hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inr h)).2 hs_val
    rw [← d.hRep d.r₀ j, hagree]; apply hsp; rw [d.hRep k j]; exact hkj
  · left; intro j hij
    let z0 : ℕ → Bool := fun w => decide (w = n + j.val)
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) d.hL
      (fun _ => by simp) (fun _ h => by cases h) (i := d.r₀.val)
      (x := oneEachRaw n m d.r₀ j) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwne, Or.inr⟩)
      (Or.inr ⟨d.r, d.hrL, rfl⟩) hr0_away
    have hsp := (hs z0 (oneEachRaw n m k j)
      (fun w _ hwne => by simp only [z0, oneEachRaw, decide_eq_decide]; exact ⟨Or.inr, fun h => h.resolve_left hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inr h)).1 hs_val
    rw [← d.hRep k j]; apply hsp; rw [← hagree, d.hRep d.r₀ j]; exact hij

theorem contradict_IncC_of_unate {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A)
    {l : Fin m} (hl : ¬ ((∀ i, A i d.c₀ = true → A i l = true) ∨ (∀ i, A i l = true → A i d.c₀ = true)))
    (hs : ∃ s : Bool, ∀ x y : ℕ → Bool,
      (∀ v < n + m, v ≠ n + l.val → x v = y v) → (x (n + l.val) = true → y (n + l.val) = true) →
      ((s = true → value (n + m) d.E x (fun _ => none) (n + m + d.r) = true →
          value (n + m) d.E y (fun _ => none) (n + m + d.r) = true) ∧
       (s = false → value (n + m) d.E y (fun _ => none) (n + m + d.r) = true →
          value (n + m) d.E x (fun _ => none) (n + m + d.r) = true))) :
    False := by
  obtain ⟨s, hs⟩ := hs
  have hc0_away : ¬ activeReach (n + m) d.E d.L none (n + d.c₀.val) (n + m + d.r) := by
    rw [activeReach_none_iff, reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
    exact (d.hc0 d.c₀).mpr rfl
  apply hl
  cases hs_val : s
  · right; intro i hil
    let z0 : ℕ → Bool := fun w => decide (w = i.val)
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) d.hL
      (fun _ => by simp) (fun _ h => by cases h) (i := n + d.c₀.val)
      (x := oneEachRaw n m i d.c₀) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
      (Or.inr ⟨d.r, d.hrL, rfl⟩) hc0_away
    have hsp := (hs z0 (oneEachRaw n m i l)
      (fun w _ hwne => by simp only [z0, oneEachRaw, decide_eq_decide]; exact ⟨Or.inl, fun h => h.resolve_right hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inl h)).2 hs_val
    rw [← d.hRep i d.c₀, hagree]; apply hsp; rw [d.hRep i l]; exact hil
  · left; intro i hij
    let z0 : ℕ → Bool := fun w => decide (w = i.val)
    have hagree := unate_unchanged (skip := none) (fix := fun _ => none) d.hL
      (fun _ => by simp) (fun _ h => by cases h) (i := n + d.c₀.val)
      (x := oneEachRaw n m i d.c₀) (y := z0)
      (fun w _ hwne => by simp only [oneEachRaw, z0, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwne, Or.inl⟩)
      (Or.inr ⟨d.r, d.hrL, rfl⟩) hc0_away
    have hsp := (hs z0 (oneEachRaw n m i l)
      (fun w _ hwne => by simp only [z0, oneEachRaw, decide_eq_decide]; exact ⟨Or.inl, fun h => h.resolve_right hwne⟩)
      (fun h => by simp only [z0, oneEachRaw, decide_eq_true_eq] at h ⊢; exact Or.inl h)).1 hs_val
    rw [← d.hRep i l]; apply hsp; rw [← hagree, d.hRep i d.c₀]; exact hij

theorem f_ge_input_dim {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) : n + m ≤ d.f := by
  by_contra hlt
  have hf_lt : d.f < n + m := Nat.lt_of_not_le hlt
  have huniq_of_ne (i : ℕ) (hne : i ≠ d.f) :
      ∀ a b c, activeReach (n + m) d.E d.L none i a → (none : Option ℕ) ≠ some a →
        edgeTo (n + m) d.E d.L a b → edgeTo (n + m) d.E d.L a c → b = c := by
    intro a b c hr _ e1 e2
    rw [activeReach_none_iff] at hr
    have haf : a ≠ d.f := by
      intro rfl
      exact hne (reaches_lt_eq hf_lt hr)
    exact d.hsingle a haf b c e1 e2
  by_cases hfn : d.f < n
  · obtain ⟨l, hl⟩ := hg.2.2.2.1 d.c₀
    have hs := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := n + l.val) (by have := l.isLt; omega)
      (huniq_of_ne (n + l.val) (by omega)) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    exact contradict_IncC_of_unate hg d hl hs
  · obtain ⟨k, hk⟩ := hg.2.2.1 d.r₀
    have hs := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := k.val) (by have := k.isLt; omega)
      (huniq_of_ne k.val (by have := k.isLt; omega)) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    exact contradict_IncR_of_unate hg d hk hs

theorem f_unate_in_input {n m : ℕ} {A : Fin n → Fin m → Bool}
    (d : CollisionData n m A) (hN : n + m ≤ d.f) {i : ℕ} (hi : i < n + m) :
    ∃ s : Bool, ∀ x y : ℕ → Bool,
      (∀ v < n + m, v ≠ i → x v = y v) → (x i = true → y i = true) →
      ((s = true → value (n + m) d.E x (fun _ => none) d.f = true →
          value (n + m) d.E y (fun _ => none) d.f = true) ∧
       (s = false → value (n + m) d.E y (fun _ => none) d.f = true →
          value (n + m) d.E x (fun _ => none) d.f = true)) := by
  classical
  have hf_live : live (n + m) d.L d.f :=
    parent_live d.hL d.hj1L d.hf_j1
  obtain ⟨jf, hjfL, hf_eq⟩ : ∃ jf ∈ d.L, d.f = n + m + jf := by
    rcases hf_live with low | ⟨j, hj, heq⟩
    · omega
    · exact ⟨j, hj, heq⟩
  have huniq : ∀ a b c, activeReach (n + m) d.E d.L (some d.f) i a → some d.f ≠ some a →
      edgeTo (n + m) d.E d.L a b → edgeTo (n + m) d.E d.L a c → b = c := by
    intro a b c _ hne e1 e2
    exact d.hsingle a (fun h => hne (congrArg some h.symm)) b c e1 e2
  have hfix : ∀ v, (some d.f : Option ℕ) = some v ↔ relay d.f false v ≠ none := by
    intro v; simp [relay, eq_comm]
  have hskipN : ∀ v, (some d.f : Option ℕ) = some v → n + m ≤ v := by
    intro v hv; cases hv; exact hN
  have hval_lt : ∀ x u, u < d.f → live (n + m) d.L u →
      value (n + m) d.E x (relay d.f false) u = value (n + m) d.E x (fun _ => none) u := by
    intro x u hu hw
    exact value_agree_of_fix_away d.hL hw fun v _ hdiff hr => by
      simp only [relay] at hdiff
      split_ifs at hdiff with hvf
      · have := reaches_le hr; omega
      · exact False.elim (hdiff rfl)
  by_cases hjnot : jf = d.j_not
  · subst jf
    obtain ⟨u_not, hun_in, hun_lt⟩ := d.hjnot_in
    have ho : (gateAt d.E d.j_not).op = .not := (d.hjnot d.j_not hjfL).mpr rfl
    have hun_f : u_not < d.f := by rw [hf_eq]; exact hun_lt
    have hun_mem : u_not ∈ (gateAt d.E d.j_not).inputs := by simp [hun_in]
    have hu_live : live (n + m) d.L u_not := parent_live d.hL hjfL ⟨hun_mem, hun_lt⟩
    obtain ⟨su, hsu⟩ := single_path_unate d.hL d.hFan d.hNotLen hfix hskipN hi huniq hu_live
    refine ⟨!su, fun x y hraw hxy => ?_⟩
    have hfx : value (n + m) d.E x (fun _ => none) d.f =
        !(value (n + m) d.E x (relay d.f false) u_not) := by
      have h := congrArg (value (n + m) d.E x (fun _ => none)) hf_eq
      rw [h, val_gate rfl, ho, hun_in]
      simp only [GateOp.eval, List.map, hun_lt, ↓reduceIte, List.headD]
      exact congrArg Bool.not (hval_lt x u_not hun_f hu_live).symm
    have hfy : value (n + m) d.E y (fun _ => none) d.f =
        !(value (n + m) d.E y (relay d.f false) u_not) := by
      have h := congrArg (value (n + m) d.E y (fun _ => none)) hf_eq
      rw [h, val_gate rfl, ho, hun_in]
      simp only [GateOp.eval, List.map, hun_lt, ↓reduceIte, List.headD]
      exact congrArg Bool.not (hval_lt y u_not hun_f hu_live).symm
    rw [hfx, hfy]
    have hsp := hsu x y hraw hxy
    cases su with
    | false =>
      simp only [Bool.not_false]
      refine ⟨fun _ h => ?_, fun h => Bool.noConfusion h⟩
      simp only [Bool.not_eq_true'] at h ⊢
      by_contra hne
      have ht := hsp.2 rfl (Bool.eq_true_of_not_eq_false hne)
      rw [h] at ht; exact Bool.noConfusion ht
    | true =>
      simp only [Bool.not_true]
      refine ⟨fun h => Bool.noConfusion h, fun _ h => ?_⟩
      simp only [Bool.not_eq_true'] at h ⊢
      by_contra hne
      have ht := hsp.1 rfl (Bool.eq_true_of_not_eq_false hne)
      rw [h] at ht; exact Bool.noConfusion ht
  · obtain ⟨h_and_or, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two jf hjfL hjnot
    have ha_mem : a ∈ (gateAt d.E jf).inputs := by simp [hin]
    have hb_mem : b ∈ (gateAt d.E jf).inputs := by simp [hin]
    have ha_f : a < d.f := by rw [hf_eq]; exact ha_lt
    have hb_f : b < d.f := by rw [hf_eq]; exact hb_lt
    have ha_live := parent_live d.hL hjfL ⟨ha_mem, ha_lt⟩
    have hb_live := parent_live d.hL hjfL ⟨hb_mem, hb_lt⟩
    have hnot_both : ¬ (activeReach (n + m) d.E d.L (some d.f) i a ∧
                        activeReach (n + m) d.E d.L (some d.f) i b) := by
      rintro ⟨hra, hrb⟩
      have ea : edgeTo (n + m) d.E d.L a d.f := ⟨jf, hjfL, hf_eq, ha_mem, ha_lt⟩
      have eb : edgeTo (n + m) d.E d.L b d.f := ⟨jf, hjfL, hf_eq, hb_mem, hb_lt⟩
      have hne_a : (some d.f : Option ℕ) ≠ some a := fun h => by cases h; exact Nat.lt_irrefl _ ha_f
      have hne_b : (some d.f : Option ℕ) ≠ some b := fun h => by cases h; exact Nat.lt_irrefl _ hb_f
      exact hab (activeReach_last_eq huniq hra hrb hne_a hne_b ea eb)
    have unate_of_one {u v : ℕ} (hu_lt : u < n + m + jf) (hv_lt : v < n + m + jf)
        (hu_f : u < d.f) (hv_f : v < d.f) (hu_live : live (n + m) d.L u) (hv_live : live (n + m) d.L v)
        (h_uv : (gateAt d.E jf).inputs = [u, v] ∨ (gateAt d.E jf).inputs = [v, u])
        (hv_away : ¬ activeReach (n + m) d.E d.L (some d.f) i v) :
        ∃ s : Bool, ∀ x y : ℕ → Bool,
          (∀ w < n + m, w ≠ i → x w = y w) → (x i = true → y i = true) →
          ((s = true → value (n + m) d.E x (fun _ => none) d.f = true →
              value (n + m) d.E y (fun _ => none) d.f = true) ∧
           (s = false → value (n + m) d.E y (fun _ => none) d.f = true →
              value (n + m) d.E x (fun _ => none) d.f = true)) := by
      obtain ⟨s, hs⟩ := single_path_unate d.hL d.hFan d.hNotLen hfix hskipN hi huniq hu_live
      refine ⟨s, fun x y hraw hxy => ?_⟩
      have hv_eq : value (n + m) d.E x (relay d.f false) v = value (n + m) d.E y (relay d.f false) v :=
        unate_unchanged d.hL hfix hskipN (fun w _ hwi => hraw w (by omega) hwi) hv_live hv_away
      have hval_u : ∀ z, value (n + m) d.E z (fun _ => none) d.f =
          (gateAt d.E jf).op.eval [value (n + m) d.E z (relay d.f false) u,
                                     value (n + m) d.E z (relay d.f false) v] := by
        intro z
        have hlhs : value (n + m) d.E z (fun _ => none) d.f =
            value (n + m) d.E z (fun _ => none) (n + m + jf) := congrArg _ hf_eq
        rw [hlhs, val_gate rfl]
        rcases h_uv with h1 | h2
        · rw [h1]; simp only [List.map, hu_lt, hv_lt, ↓reduceIte,
            ← hval_lt z u hu_f hu_live, ← hval_lt z v hv_f hv_live]
        · rw [h2]; simp only [List.map, hu_lt, hv_lt, ↓reduceIte,
            ← hval_lt z u hu_f hu_live, ← hval_lt z v hv_f hv_live]
          rcases h_and_or with ha | ho
          · simp only [ha, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, Function.comp_apply, id_eq]
            exact Bool.and_comm _ _
          · simp only [ho, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Function.comp_apply, id_eq]
            exact Bool.or_comm _ _
      rw [hval_u x, hval_u y, ← hv_eq]
      have hsp := hs x y hraw hxy
      set vx := value (n + m) d.E x (relay d.f false) v
      set ux := value (n + m) d.E x (relay d.f false) u
      set uy := value (n + m) d.E y (relay d.f false) u
      rcases h_and_or with ha | ho
      · simp only [ha, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨fun h1 ⟨hux, hv⟩ => ⟨hsp.1 h1 hux, hv⟩, fun h2 ⟨huy, hv⟩ => ⟨hsp.2 h2 huy, hv⟩⟩
      · simp only [ho, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        refine ⟨fun h1 h => ?_, fun h2 h => ?_⟩
        · rcases h with hux | hv
          · exact Or.inl (hsp.1 h1 hux)
          · exact Or.inr hv
        · rcases h with huy | hv
          · exact Or.inl (hsp.2 h2 huy)
          · exact Or.inr hv
    by_cases hb : activeReach (n + m) d.E d.L (some d.f) i b
    · exact unate_of_one hb_lt ha_lt hb_f ha_f hb_live ha_live (Or.inr hin) (fun h => hnot_both ⟨h, hb⟩)
    · exact unate_of_one ha_lt hb_lt ha_f hb_f ha_live hb_live (Or.inl hin) hb

section JoinSetClassical
open Classical

noncomputable def joinSet {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) : Finset ℕ :=
  d.L.filter fun k => reaches (n + m) d.E d.L (n + m + d.j₁) (n + m + k) ∧
                      reaches (n + m) d.E d.L (n + m + d.j₂) (n + m + k)

theorem root_mem_joinSet {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) :
    d.r ∈ joinSet d := by
  rw [joinSet, Finset.mem_filter]
  exact ⟨d.hrL,
    reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L,
    reaches_root_of_closed d.hL d.huse d.j₂ d.hj2L⟩

noncomputable def joinGate {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) : ℕ :=
  (joinSet d).min' ⟨d.r, root_mem_joinSet d⟩

theorem joinGate_spec {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) :
    joinGate d ∈ d.L ∧
    reaches (n + m) d.E d.L (n + m + d.j₁) (n + m + joinGate d) ∧
    reaches (n + m) d.E d.L (n + m + d.j₂) (n + m + joinGate d) := by
  dsimp only [joinGate]
  have hmem := Finset.min'_mem (joinSet d) ⟨d.r, root_mem_joinSet d⟩
  dsimp only [joinSet] at hmem
  exact Finset.mem_filter.mp hmem

theorem joinGate_le {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {k : ℕ} (hk : k ∈ d.L) (h1 : reaches (n + m) d.E d.L (n + m + d.j₁) (n + m + k))
    (h2 : reaches (n + m) d.E d.L (n + m + d.j₂) (n + m + k)) :
    joinGate d ≤ k := by
  dsimp only [joinGate]
  apply Finset.min'_le
  rw [joinSet, Finset.mem_filter]
  exact ⟨hk, h1, h2⟩

end JoinSetClassical

theorem joinGate_reaches_root {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) :
    reaches (n + m) d.E d.L (n + m + joinGate d) (n + m + d.r) := by
  have hlt : d.f < n + m + d.j₁ := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
  have h1 := (joinGate_spec d).2.1
  have hr := reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L
  rcases reaches_total_of_gt d.hsingle hlt h1 hr with h | h
  · exact h
  · have hle1 := reaches_le h
    have hle2 := joinGate_le d d.hrL hr (reaches_root_of_closed d.hL d.huse d.j₂ d.hj2L)
    have : joinGate d = d.r := by omega
    rw [this]
    exact Relation.ReflTransGen.refl

theorem reaches_of_f_ne {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {w : ℕ} (hr : reaches (n + m) d.E d.L d.f w) (hne : w ≠ d.f) :
    reaches (n + m) d.E d.L (n + m + d.j₁) w ∨ reaches (n + m) d.E d.L (n + m + d.j₂) w := by
  rcases hr.cases_head with rfl | ⟨b, ⟨j, hjL, rfl, hbef⟩, hbw⟩
  · exact False.elim (hne rfl)
  · rcases d.hf_two j hjL hbef with rfl | rfl
    · exact Or.inl hbw
    · exact Or.inr hbw

theorem f_reaches_root {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A) :
    reaches (n + m) d.E d.L d.f (n + m + d.r) :=
  Relation.ReflTransGen.head ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
    (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)

theorem top_unate_in_f {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (hN : n + m ≤ d.f)
    (hcond : ¬ (reaches (n + m) d.E d.L d.f (n + m + d.j_not) ∧ d.f ≠ n + m + d.j_not) ∨
             reaches (n + m) d.E d.L (n + m + joinGate d) (n + m + d.j_not)) :
    ∃ s_top : Bool, ∀ x : ℕ → Bool, ∀ b₀ b₁ : Bool, (b₀ = true → b₁ = true) →
      ((s_top = true → value (n + m) d.E x (relay d.f b₀) (n + m + d.r) = true →
          value (n + m) d.E x (relay d.f b₁) (n + m + d.r) = true) ∧
       (s_top = false → value (n + m) d.E x (relay d.f b₁) (n + m + d.r) = true →
          value (n + m) d.E x (relay d.f b₀) (n + m + d.r) = true)) := by
  classical
  have hf_lt1 : d.f < n + m + d.j₁ := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
  have hf_lt2 : d.f < n + m + d.j₂ := edgeTo_lt ⟨d.j₂, d.hj2L, rfl, d.hf_j2⟩
  have mono_below (q : ℕ) (hq_lt : d.f < q)
      (hmono_gate : ∀ j ∈ d.L, reaches (n + m) d.E d.L d.f (n + m + j) →
        n + m + j ≠ d.f → n + m + j < q → (gateAt d.E j).op ≠ .not) :
      ∀ (x : ℕ → Bool) (b₀ b₁ : Bool), (b₀ = true → b₁ = true) →
        ∀ w, live (n + m) d.L w → w < q →
          value (n + m) d.E x (relay d.f b₀) w = true →
          value (n + m) d.E x (relay d.f b₁) w = true := by
    intro x b₀ b₁ hb w hw hwq hval
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hrf : reaches (n + m) d.E d.L d.f w
      · by_cases hweq : w = d.f
        · subst hweq
          rw [val_relay_at hN] at hval ⊢
          exact hb hval
        · rcases hw with low | ⟨j, hj, rfl⟩
          · have := reaches_le hrf; omega
          · have hno := hmono_gate j hj hrf hweq hwq
            have hmem : gateAt d.E j ∈ d.E.gates := by
              rw [gateAt, List.getD_eq_getElem _ _ (d.hL.1 j hj)]
              exact List.getElem_mem _
            have hf0 : relay d.f b₀ (n + m + j) = none := by simp [relay, hweq]
            have hf1 : relay d.f b₁ (n + m + j) = none := by simp [relay, hweq]
            rw [val_gate hf0] at hval; rw [val_gate hf1]
            have h_and_or : (gateAt d.E j).op = .and ∨ (gateAt d.E j).op = .or := by
              rcases (d.hFan _ hmem).1 with ho | ho | ho
              · exact Or.inl ho
              · exact Or.inr ho
              · exact False.elim (hno ho)
            rcases h_and_or with ha | ho
            · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hval ⊢
              intro u hu
              have hxu := hval u hu
              split_ifs with hlt
              · rw [if_pos hlt] at hxu
                exact ih u hlt (parent_live d.hL hj ⟨hu, hlt⟩) (by omega) hxu
              · rw [if_neg hlt] at hxu; cases hxu
            · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval ⊢
              obtain ⟨u, hu, hxu⟩ := hval
              refine ⟨u, hu, ?_⟩
              split_ifs with hlt
              · rw [if_pos hlt] at hxu
                exact ih u hlt (parent_live d.hL hj ⟨hu, hlt⟩) (by omega) hxu
              · rw [if_neg hlt] at hxu; cases hxu
      · have heq : value (n + m) d.E x (relay d.f b₀) w =
            value (n + m) d.E x (relay d.f b₁) w :=
          value_agree_of_fix_away d.hL hw fun v _ hdiff hr => by
            by_cases hvf : v = d.f
            · subst hvf; exact hrf hr
            · exfalso; apply hdiff; simp [relay, hvf]
        rw [← heq]; exact hval
  rcases hcond with hnot | hJ_q
  · refine ⟨true, fun x b₀ b₁ hb => ?_⟩
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    exact mono_below (n + m + d.r + 1) (by have := reaches_le (f_reaches_root d); omega)
      (fun j hj hrf hne _ ho => hnot ⟨(d.hjnot j hj).mp ho ▸ hrf, fun e => hne (by rw [(d.hjnot j hj).mp ho, e])⟩)
      x b₀ b₁ hb (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) (by omega)
  · have hq_lt : d.f < n + m + d.j_not := by
      have hle := reaches_le hJ_q
      have hle1 := reaches_le (joinGate_spec d).2.1
      omega
    have hq_root : reaches (n + m) d.E d.L (n + m + d.j_not) (n + m + d.r) :=
      reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL
    have anti_above : ∀ (x : ℕ → Bool) (b₀ b₁ : Bool), (b₀ = true → b₁ = true) →
        ∀ w, live (n + m) d.L w → reaches (n + m) d.E d.L (n + m + d.j_not) w →
          value (n + m) d.E x (relay d.f b₁) w = true →
          value (n + m) d.E x (relay d.f b₀) w = true := by
      intro x b₀ b₁ hb w hw hqw hval
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hweq : w = n + m + d.j_not
        · subst hweq
          obtain ⟨u_not, hun_in, hun_lt⟩ := d.hjnot_in
          have ho : (gateAt d.E d.j_not).op = .not := (d.hjnot d.j_not d.hjnotL).mpr rfl
          have hne_f : n + m + d.j_not ≠ d.f := by omega
          have hf0 : relay d.f b₀ (n + m + d.j_not) = none := by simp [relay, hne_f]
          have hf1 : relay d.f b₁ (n + m + d.j_not) = none := by simp [relay, hne_f]
          rw [val_gate hf1, ho, hun_in] at hval
          rw [val_gate hf0, ho, hun_in]
          simp only [GateOp.eval, List.map, hun_lt, ↓reduceIte, List.headD] at hval ⊢
          have hu_live := parent_live d.hL d.hjnotL ⟨by simp [hun_in], hun_lt⟩
          by_cases hxu : value (n + m) d.E x (relay d.f b₀) u_not = true
          · have hm := mono_below (n + m + d.j_not) hq_lt
              (fun j hj _ _ hlt ho' => by have := (d.hjnot j hj).mp ho'; omega)
              x b₀ b₁ hb u_not hu_live hun_lt hxu
            rw [hm] at hval; exact False.elim (Bool.noConfusion hval)
          · have hxf : value (n + m) d.E x (relay d.f b₀) u_not = false := Bool.eq_false_iff.mpr hxu
            simp only [hxf, Bool.not_false]
        · rcases hw with low | ⟨j, hj, rfl⟩
          · have := reaches_le hqw; omega
          · have hne_q : j ≠ d.j_not := fun e => hweq (by rw [e])
            have hne_f : n + m + j ≠ d.f := by have := reaches_le hqw; omega
            have hf0 : relay d.f b₀ (n + m + j) = none := by simp [relay, hne_f]
            have hf1 : relay d.f b₁ (n + m + j) = none := by simp [relay, hne_f]
            rw [val_gate hf1] at hval; rw [val_gate hf0]
            obtain ⟨h_and_or, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two j hj hne_q
            have handle_child {u : ℕ} (hu_mem : u ∈ (gateAt d.E j).inputs) (hu_lt : u < n + m + j) :
                value (n + m) d.E x (relay d.f b₁) u = true →
                value (n + m) d.E x (relay d.f b₀) u = true := by
              intro huval
              by_cases hqu : reaches (n + m) d.E d.L (n + m + d.j_not) u
              · exact ih u hu_lt (parent_live d.hL hj ⟨hu_mem, hu_lt⟩) hqu huval
              · by_cases hfu : reaches (n + m) d.E d.L d.f u
                · exfalso
                  have heuw : edgeTo (n + m) d.E d.L u (n + m + j) := ⟨j, hj, rfl, hu_mem, hu_lt⟩
                  by_cases hud : u = d.f
                  · subst hud
                    rcases d.hf_two j hj (by exact ⟨hu_mem, hu_lt⟩) with rfl | rfl
                    · have := reaches_le (joinGate_spec d).2.1
                      have := reaches_le hJ_q
                      have := reaches_le hqw
                      omega
                    · have := reaches_le (joinGate_spec d).2.2
                      have := reaches_le hJ_q
                      have := reaches_le hqw
                      omega
                  · have step_q : reaches (n + m) d.E d.L u (n + m + d.j_not) := by
                      rcases reaches_of_f_ne d hfu hud with h1 | h2
                      · rcases reaches_total_of_gt d.hsingle hf_lt1 h1 ((joinGate_spec d).2.1.trans hJ_q) with h | h
                        · exact h
                        · exact False.elim (hqu h)
                      · rcases reaches_total_of_gt d.hsingle hf_lt2 h2 ((joinGate_spec d).2.2.trans hJ_q) with h | h
                        · exact h
                        · exact False.elim (hqu h)
                    rcases step_q.cases_head with rfl | ⟨c, hc, hcq⟩
                    · exact hqu Relation.ReflTransGen.refl
                    · have hcw := d.hsingle u hud c (n + m + j) hc heuw
                      rw [hcw] at hcq
                      have := reaches_le hcq
                      have := reaches_le hqw
                      omega
                · have heq : value (n + m) d.E x (relay d.f b₁) u =
                      value (n + m) d.E x (relay d.f b₀) u :=
                    value_agree_of_fix_away d.hL (parent_live d.hL hj ⟨hu_mem, hu_lt⟩)
                      fun v _ hdiff hr => by
                        by_cases hvf : v = d.f
                        · subst hvf; exact hfu hr
                        · exfalso; apply hdiff; simp [relay, hvf]
                  rw [← heq]; exact huval
            rcases h_and_or with ha | ho
            · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hval ⊢
              intro u hu
              have hxu := hval u hu
              split_ifs with hlt
              · rw [if_pos hlt] at hxu
                exact handle_child hu hlt hxu
              · rw [if_neg hlt] at hxu; cases hxu
            · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval ⊢
              obtain ⟨u, hu, hxu⟩ := hval
              refine ⟨u, hu, ?_⟩
              split_ifs with hlt
              · rw [if_pos hlt] at hxu
                exact handle_child hu hlt hxu
              · rw [if_neg hlt] at hxu; cases hxu
    exact ⟨false, fun x b₀ b₁ hb => ⟨fun h => Bool.noConfusion h,
      fun _ => anti_above x b₀ b₁ hb (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) hq_root⟩⟩

structure SplitData (n m : ℕ) (A : Fin n → Fin m → Bool) (d : CollisionData n m A) where
  d_N_le_f : n + m ≤ d.f
  J : ℕ
  hJL : J ∈ d.L
  j_hit : ℕ
  j_miss : ℕ
  hbranches : (j_hit = d.j₁ ∧ j_miss = d.j₂) ∨ (j_hit = d.j₂ ∧ j_miss = d.j₁)
  h_hit_L : j_hit ∈ d.L
  h_miss_L : j_miss ∈ d.L
  h_hit_ne_miss : j_hit ≠ j_miss
  h_hit_f : before d.E (n + m) j_hit d.f
  h_miss_f : before d.E (n + m) j_miss d.f
  h_hit_not : reaches (n + m) d.E d.L (n + m + j_hit) (n + m + d.j_not)
  h_miss_not : ¬ reaches (n + m) d.E d.L (n + m + j_miss) (n + m + d.j_not)
  h_not_J : reaches (n + m) d.E d.L (n + m + d.j_not) (n + m + J)
  h_not_ne_J : d.j_not ≠ J
  h_miss_J : reaches (n + m) d.E d.L (n + m + j_miss) (n + m + J)
  h_J_root : reaches (n + m) d.E d.L (n + m + J) (n + m + d.r)

theorem split_data_of_collision {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) : Nonempty (SplitData n m A d) := by
  have hN : n + m ≤ d.f := f_ge_input_dim hg d
  have h_between : (reaches (n + m) d.E d.L d.f (n + m + d.j_not) ∧ d.f ≠ n + m + d.j_not) ∧
      ¬ reaches (n + m) d.E d.L (n + m + joinGate d) (n + m + d.j_not) := by
    by_contra hbad
    have hcond : ¬ (reaches (n + m) d.E d.L d.f (n + m + d.j_not) ∧ d.f ≠ n + m + d.j_not) ∨
        reaches (n + m) d.E d.L (n + m + joinGate d) (n + m + d.j_not) := by
      tauto
    obtain ⟨s_top, htop⟩ := top_unate_in_f d hN hcond
    obtain ⟨k, hk⟩ := hg.2.2.1 d.r₀
    by_cases hreach : reaches (n + m) d.E d.L k.val d.f
    · obtain ⟨s_f, hf_u⟩ := f_unate_in_input d hN (i := k.val) (by have := k.isLt; omega)
      have hcomb : ∃ s : Bool, ∀ x y : ℕ → Bool,
          (∀ v < n + m, v ≠ k.val → x v = y v) → (x k.val = true → y k.val = true) →
          ((s = true → value (n + m) d.E x (fun _ => none) (n + m + d.r) = true →
              value (n + m) d.E y (fun _ => none) (n + m + d.r) = true) ∧
           (s = false → value (n + m) d.E y (fun _ => none) (n + m + d.r) = true →
              value (n + m) d.E x (fun _ => none) (n + m + d.r) = true)) := by
        refine ⟨decide (s_f = s_top), fun x y hraw hxy => ?_⟩
        have hfx_eq : value (n + m) d.E x (fun _ => none) d.f =
            value (n + m) d.E x (relay d.f (value (n + m) d.E x (fun _ => none) d.f)) d.f := by
          rw [val_relay_at hN]
        have hfy_eq : value (n + m) d.E y (fun _ => none) d.f =
            value (n + m) d.E y (relay d.f (value (n + m) d.E y (fun _ => none) d.f)) d.f := by
          rw [val_relay_at hN]
        have hf_lt_R : d.f < n + m + d.r := by
          have := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
          have := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
          omega
        have hc1 := cut_agree d.hL d.f d.hsingle x x (fun _ => none)
          (relay d.f (value (n + m) d.E x (fun _ => none) d.f))
          (fun _ _ _ => rfl) (fun v _ hvf => by simp [relay, hvf]) hfx_eq
          (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (Or.inr fun hr => by have := reaches_le hr; omega)
        have hc2 := cut_agree d.hL d.f d.hsingle x y
          (relay d.f (value (n + m) d.E x (fun _ => none) d.f))
          (relay d.f (value (n + m) d.E x (fun _ => none) d.f))
          (fun v hvN hvnf => hraw v hvN (fun e => hvnf (e ▸ hreach)))
          (fun _ _ _ => rfl)
          (by rw [val_relay_at hN, val_relay_at hN])
          (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (Or.inr fun hr => by have := reaches_le hr; omega)
        have hc3 := cut_agree d.hL d.f d.hsingle y y (fun _ => none)
          (relay d.f (value (n + m) d.E y (fun _ => none) d.f))
          (fun _ _ _ => rfl) (fun v _ hvf => by simp [relay, hvf]) hfy_eq
          (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (Or.inr fun hr => by have := reaches_le hr; omega)
        have hsp := hf_u x y hraw hxy
        set fx := value (n + m) d.E x (fun _ => none) d.f
        set fy := value (n + m) d.E y (fun _ => none) d.f
        have ht := htop y false true (fun _ => rfl)
        have hrel_x : value (n + m) d.E x (fun _ => none) (n + m + d.r) =
            value (n + m) d.E y (relay d.f fx) (n + m + d.r) := hc1.trans hc2
        have hrel_y : value (n + m) d.E y (fun _ => none) (n + m + d.r) =
            value (n + m) d.E y (relay d.f fy) (n + m + d.r) := hc3
        cases hs1 : s_f <;> cases hs2 : s_top <;>
          simp only [Bool.true_eq_false, Bool.false_eq_true, decide_false, decide_true]
        · refine ⟨fun _ hx => ?_, fun h => False.elim h⟩
          rw [hrel_y]; rw [hrel_x] at hx
          by_cases hfx : fx = fy
          · rw [← hfx]; exact hx
          · have hfy0 : fy = false := by
              by_contra hfy1
              have hfx1 : fx = true := hsp.2 hs1 (Bool.eq_true_of_not_eq_false hfy1)
              exact hfx (hfx1.trans (Bool.eq_true_of_not_eq_false hfy1).symm)
            have hfx1 : fx = true := by
              by_contra hfx0
              exact hfx ((Bool.eq_false_iff.mpr hfx0).trans hfy0.symm)
            rw [hfy0]; rw [hfx1] at hx
            exact ht.2 hs2 hx
        · refine ⟨fun h => False.elim h, fun _ hy => ?_⟩
          rw [hrel_x]; rw [hrel_y] at hy
          by_cases hfx : fx = fy
          · rw [hfx]; exact hy
          · have hfy0 : fy = false := by
              by_contra hfy1
              have hfx1 : fx = true := hsp.2 hs1 (Bool.eq_true_of_not_eq_false hfy1)
              exact hfx (hfx1.trans (Bool.eq_true_of_not_eq_false hfy1).symm)
            have hfx1 : fx = true := by
              by_contra hfx0
              exact hfx ((Bool.eq_false_iff.mpr hfx0).trans hfy0.symm)
            rw [hfx1]; rw [hfy0] at hy
            exact ht.1 hs2 hy
        · refine ⟨fun h => False.elim h, fun _ hy => ?_⟩
          rw [hrel_x]; rw [hrel_y] at hy
          by_cases hfx : fx = fy
          · rw [hfx]; exact hy
          · have hfx0 : fx = false := by
              by_contra hfx1
              have hfy1 : fy = true := hsp.1 hs1 (Bool.eq_true_of_not_eq_false hfx1)
              exact hfx ((Bool.eq_true_of_not_eq_false hfx1).trans hfy1.symm)
            have hfy1 : fy = true := by
              by_contra hfy0
              exact hfx (hfx0.trans (Bool.eq_false_iff.mpr hfy0).symm)
            rw [hfx0]; rw [hfy1] at hy
            exact ht.2 hs2 hy
        · refine ⟨fun _ hx => ?_, fun h => False.elim h⟩
          rw [hrel_y]; rw [hrel_x] at hx
          by_cases hfx : fx = fy
          · rw [← hfx]; exact hx
          · have hfx0 : fx = false := by
              by_contra hfx1
              have hfy1 : fy = true := hsp.1 hs1 (Bool.eq_true_of_not_eq_false hfx1)
              exact hfx ((Bool.eq_true_of_not_eq_false hfx1).trans hfy1.symm)
            have hfy1 : fy = true := by
              by_contra hfy0
              exact hfx (hfx0.trans (Bool.eq_false_iff.mpr hfy0).symm)
            rw [hfy1]; rw [hfx0] at hx
            exact ht.1 hs2 hx
      exact contradict_IncR_of_unate hg d hk hcomb
    · have huniq : ∀ a b c, activeReach (n + m) d.E d.L none k.val a → (none : Option ℕ) ≠ some a →
          edgeTo (n + m) d.E d.L a b → edgeTo (n + m) d.E d.L a c → b = c := by
        intro a b c hr _ e1 e2
        rw [activeReach_none_iff] at hr
        exact d.hsingle a (fun heq => hreach (heq ▸ hr)) b c e1 e2
      have hsp := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
        (fun _ => by simp) (fun _ h => by cases h) (i := k.val) (by have := k.isLt; omega)
        huniq (Or.inr ⟨d.r, d.hrL, rfl⟩)
      exact contradict_IncR_of_unate hg d hk hsp
  rcases h_between with ⟨⟨hf_q, hf_neq⟩, hJ_nq⟩
  have hf_lt1 : d.f < n + m + d.j₁ := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
  have hf_lt2 : d.f < n + m + d.j₂ := edgeTo_lt ⟨d.j₂, d.hj2L, rfl, d.hf_j2⟩
  have hnot_both : ¬ (reaches (n + m) d.E d.L (n + m + d.j₁) (n + m + d.j_not) ∧
      reaches (n + m) d.E d.L (n + m + d.j₂) (n + m + d.j_not)) := by
    rintro ⟨h1, h2⟩
    have hle := joinGate_le d d.hjnotL h1 h2
    rcases reaches_total_of_gt d.hsingle hf_lt1 (joinGate_spec d).2.1 h1 with h | h
    · exact hJ_nq h
    · have := reaches_le h
      have heq : joinGate d = d.j_not := by omega
      exact hJ_nq (heq ▸ Relation.ReflTransGen.refl)
  rcases reaches_of_f_ne d hf_q hf_neq.symm with h1 | h2
  · have hn2 : ¬ reaches (n + m) d.E d.L (n + m + d.j₂) (n + m + d.j_not) := fun h => hnot_both ⟨h1, h⟩
    have h_not_J : reaches (n + m) d.E d.L (n + m + d.j_not) (n + m + joinGate d) :=
      (reaches_total_of_gt d.hsingle hf_lt1 h1 (joinGate_spec d).2.1).resolve_right hJ_nq
    have hne : d.j_not ≠ joinGate d := fun e => hn2 (e ▸ (joinGate_spec d).2.2)
    exact ⟨⟨hN, joinGate d, (joinGate_spec d).1, d.j₁, d.j₂, Or.inl ⟨rfl, rfl⟩,
      d.hj1L, d.hj2L, d.hj12, d.hf_j1, d.hf_j2, h1, hn2, h_not_J, hne,
      (joinGate_spec d).2.2, joinGate_reaches_root d⟩⟩
  · have hn1 : ¬ reaches (n + m) d.E d.L (n + m + d.j₁) (n + m + d.j_not) := fun h => hnot_both ⟨h, h2⟩
    have h_not_J : reaches (n + m) d.E d.L (n + m + d.j_not) (n + m + joinGate d) :=
      (reaches_total_of_gt d.hsingle hf_lt2 h2 (joinGate_spec d).2.2).resolve_right hJ_nq
    have hne : d.j_not ≠ joinGate d := fun e => hn1 (e ▸ (joinGate_spec d).2.1)
    exact ⟨⟨hN, joinGate d, (joinGate_spec d).1, d.j₂, d.j₁, Or.inr ⟨rfl, rfl⟩,
      d.hj2L, d.hj1L, d.hj12.symm, d.hf_j2, d.hf_j1, h2, hn1, h_not_J, hne,
      (joinGate_spec d).2.1, joinGate_reaches_root d⟩⟩

theorem false_of_no_not_reach {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {w : ℕ} (hw : live (n + m) d.L w)
    (hnq : ¬ reaches (n + m) d.E d.L (n + m + d.j_not) w) :
    value (n + m) d.E (fun _ => false) (fun _ => none) w = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · exact val_raw low
    · have hne : j ≠ d.j_not := fun e => hnq (e ▸ Relation.ReflTransGen.refl)
      obtain ⟨h_and_or, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j hj hne
      have ha_mem : a ∈ (gateAt d.E j).inputs := by simp [hin]
      have hb_mem : b ∈ (gateAt d.E j).inputs := by simp [hin]
      have hna : ¬ reaches (n + m) d.E d.L (n + m + d.j_not) a :=
        fun h => hnq (Relation.ReflTransGen.tail h ⟨j, hj, rfl, ha_mem, ha_lt⟩)
      have hnb : ¬ reaches (n + m) d.E d.L (n + m + d.j_not) b :=
        fun h => hnq (Relation.ReflTransGen.tail h ⟨j, hj, rfl, hb_mem, hb_lt⟩)
      have hfa := ih a ha_lt (parent_live d.hL hj ⟨ha_mem, ha_lt⟩) hna
      have hfb := ih b hb_lt (parent_live d.hL hj ⟨hb_mem, hb_lt⟩) hnb
      rw [val_gate rfl, hin]
      simp only [List.map, ha_lt, hb_lt, ↓reduceIte, hfa, hfb]
      rcases h_and_or with h' | h' <;> simp [h', GateOp.eval]

theorem activeReach_skip_contra {N : ℕ} {C : Circuit} {L : Finset ℕ} {f q w : ℕ}
    (hsingle : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {u : ℕ} (hnf : ¬ reaches N C L u f) (huq : reaches N C L u q) (hqw : q < w)
    (ha : activeReach N C L (some q) u w) : False := by
  have hmain : ∀ d u, w - u = d → ¬ reaches N C L u f → reaches N C L u q →
      activeReach N C L (some q) u w → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro u hd hnf huq ha
      rcases ha.cases_head with rfl | ⟨a, hua, haw⟩
      · have := reaches_le huq; omega
      · rcases huq.cases_head with rfl | ⟨b, hb, hbq⟩
        · exact hua.1 rfl
        · have huf : u ≠ f := fun e => hnf (e ▸ Relation.ReflTransGen.refl)
          have hab := hsingle u huf a b hua.2 hb
          rw [← hab] at hbq
          have hlt := edgeTo_lt hua.2
          have hle := activeReach_le haw
          exact ih (w - a) (by omega) a rfl (fun h => hnf (Relation.ReflTransGen.head hua.2 h)) hbq haw
  exact hmain (w - u) u rfl hnf huq ha

theorem A_r0_c0_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d) :
    A d.r₀ d.c₀ = false := by
  classical
  by_contra htrue
  have hA0 : A d.r₀ d.c₀ = true := Bool.eq_true_of_not_eq_false htrue
  have h0_agree : value (n + m) d.E (oneEachRaw n m d.r₀ d.c₀) (fun _ => none) (n + m + d.r) =
      value (n + m) d.E (fun _ => false) (fun _ => none) (n + m + d.r) := by
    apply value_agree_of_reaches d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) Relation.ReflTransGen.refl
    intro w hw hwr
    have hw_used : w ∈ used (n + m) d.E d.L :=
      (reaches_root_iff_used d.hrL d.hL d.huse hw).mp hwr
    simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
    refine ⟨?_, ?_⟩
    · intro he; subst he; exact (d.hr0 d.r₀).mpr rfl hw_used
    · intro he; subst he; exact (d.hc0 d.c₀).mpr rfl hw_used
  have hzero_R : value (n + m) d.E (fun _ => false) (fun _ => none) (n + m + d.r) = true := by
    rw [← h0_agree, d.hRep]; exact hA0
  let q := n + m + d.j_not
  have hf_ltq : d.f < q := by
    have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
    have := reaches_le sd.h_hit_not
    omega
  have hq_root : reaches (n + m) d.E d.L q (n + m + d.r) :=
    sd.h_not_J.trans sd.h_J_root
  have h_or_path : ∀ w, reaches (n + m) d.E d.L q w → reaches (n + m) d.E d.L w (n + m + d.r) →
      value (n + m) d.E (fun _ => false) (fun _ => none) w = true ∧
      (w ≠ q → ∃ k ∈ d.L, w = n + m + k ∧ (gateAt d.E k).op = .or) := by
    have hmain : ∀ dist w, (n + m + d.r) - w = dist →
        reaches (n + m) d.E d.L q w → reaches (n + m) d.E d.L w (n + m + d.r) →
        value (n + m) d.E (fun _ => false) (fun _ => none) w = true ∧
        (w ≠ q → ∃ k ∈ d.L, w = n + m + k ∧ (gateAt d.E k).op = .or) := by
      intro dist
      induction dist using Nat.strong_induction_on with
      | ind dist ih =>
        intro w hdist hqw hwR
        rcases hwR.cases_head with rfl | ⟨b, e, hwR_tail⟩
        · refine ⟨hzero_R, fun hne => ⟨d.r, d.hrL, rfl, ?_⟩⟩
          have hne_r : d.r ≠ d.j_not := fun eq => hne (by simp [q, eq])
          obtain ⟨h_ao, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two d.r d.hrL hne_r
          rcases h_ao with ha | ho
          · exfalso
            rcases hqw.cases_tail with heq | ⟨u, hqu, ⟨k, hkL, hk_eq, hu_mem, hu_lt⟩⟩
            · exact hne heq
            · have hkr : k = d.r := by omega
              subst k
              have hv : ∃ v ∈ (gateAt d.E d.r).inputs, v ≠ u ∧ v < n + m + d.r := by
                rw [hin] at hu_mem ⊢
                rcases List.mem_pair.mp hu_mem with rfl | rfl
                · exact ⟨b, by simp, hab.symm, hb_lt⟩
                · exact ⟨a, by simp, hab, ha_lt⟩
              obtain ⟨v, hv_mem, hvu, hv_lt⟩ := hv
              have hnqv : ¬ reaches (n + m) d.E d.L q v := by
                intro hqv
                have heu : edgeTo (n + m) d.E d.L u (n + m + d.r) := ⟨d.r, d.hrL, rfl, hu_mem, hu_lt⟩
                have hev : edgeTo (n + m) d.E d.L v (n + m + d.r) := ⟨d.r, d.hrL, rfl, hv_mem, hv_lt⟩
                have huv := activeReach_last_eq
                  (fun x y z hr _ e1 e2 => d.hsingle x (fun hx => by
                    have := reaches_le (activeReach_none_iff.mp hr); omega) y z e1 e2)
                  (activeReach_none_iff.mpr hqu) (activeReach_none_iff.mpr hqv)
                  (by simp) (by simp) heu hev
                exact hvu huv.symm
              have hfv := false_of_no_not_reach d (parent_live d.hL d.hrL ⟨hv_mem, hv_lt⟩) hnqv
              rw [val_gate rfl, ha] at hzero_R
              simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hzero_R
              have hvt := hzero_R v hv_mem
              rw [if_pos hv_lt, hfv] at hvt
              exact Bool.noConfusion hvt
          · exact ho
        · have hqb : reaches (n + m) d.E d.L q b := hqw.tail e
          have hlt_wb := edgeTo_lt e
          have hle_bR := reaches_le hwR_tail
          obtain ⟨hvb, hb_spec⟩ := ih ((n + m + d.r) - b) (by omega) b rfl hqb hwR_tail
          have hqb_ne : b ≠ q := fun eq => by have := reaches_le hqw; omega
          obtain ⟨k, hkL, rfl, hok⟩ := hb_spec hqb_ne
          obtain ⟨j_w, hjwL, hbw, hw_mem, hw_lt⟩ := e
          have hjw_eq : j_w = k := by omega
          subst j_w
          have hk_ne : k ≠ d.j_not := fun eq => hqb_ne (by simp [q, eq])
          obtain ⟨_, a, b', hab, hin, ha_lt, hb_lt⟩ := d.hother_two k hkL hk_ne
          have hv : ∃ v ∈ (gateAt d.E k).inputs, v ≠ w ∧ v < n + m + k := by
            rw [hin] at hw_mem ⊢
            rcases List.mem_pair.mp hw_mem with rfl | rfl
            · exact ⟨b', by simp, hab.symm, hb_lt⟩
            · exact ⟨a, by simp, hab, ha_lt⟩
          obtain ⟨v, hv_mem, hvw, hv_lt⟩ := hv
          have hnqv : ¬ reaches (n + m) d.E d.L q v := by
            intro hqv
            have hew : edgeTo (n + m) d.E d.L w (n + m + k) := ⟨k, hkL, rfl, hw_mem, hw_lt⟩
            have hev : edgeTo (n + m) d.E d.L v (n + m + k) := ⟨k, hkL, rfl, hv_mem, hv_lt⟩
            have huv := activeReach_last_eq
              (fun x y z hr _ e1 e2 => d.hsingle x (fun hx => by
                have := reaches_le (activeReach_none_iff.mp hr); omega) y z e1 e2)
              (activeReach_none_iff.mpr hqw) (activeReach_none_iff.mpr hqv)
              (by simp) (by simp) hew hev
            exact hvw huv.symm
          have hfv := false_of_no_not_reach d (parent_live d.hL hkL ⟨hv_mem, hv_lt⟩) hnqv
          rw [val_gate rfl, hok, hin] at hvb
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hvb
          obtain ⟨z, hz_mem, hzv⟩ := hvb
          have hvw_val : value (n + m) d.E (fun _ => false) (fun _ => none) w = true := by
            rw [hin] at hw_mem hv_mem
            have hzwv : z = w ∨ z = v := by
              rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hw_mem with ew | ew <;>
                rcases List.mem_pair.mp hv_mem with ev | ev
              all_goals first
                | exact Or.inl ew.symm
                | exact Or.inr ev.symm
                | exact False.elim (hvw (ev.trans ew.symm))
            rcases hzwv with rfl | rfl
            · rw [if_pos hw_lt] at hzv; exact hzv
            · rw [if_pos hv_lt, hfv] at hzv; cases hzv
          refine ⟨hvw_val, fun hne => ?_⟩
          rcases hqw.cases_tail with heq | ⟨u, _, ⟨jw, hjwL, hweq, _⟩⟩
          · exact False.elim (hne heq)
          · refine ⟨jw, hjwL, hweq, ?_⟩
            by_contra hnot_or
            have hjw_ne : jw ≠ d.j_not := fun eq => hne (by rw [hweq, eq])
            obtain ⟨hao, _, _, _, _, _, _⟩ := d.hother_two jw hjwL hjw_ne
            have ha : (gateAt d.E jw).op = .and := hao.resolve_right hnot_or
            rcases hqw.cases_tail with heq' | ⟨u', hqu', ⟨jw', hjw'L, hweq', hu'_mem, hu'_lt⟩⟩
            · exact hne heq'
            · have hjw_eq : jw' = jw := by omega
              subst jw'
              obtain ⟨_, a', b', hab', hin', ha'_lt, hb'_lt⟩ := d.hother_two jw hjwL hjw_ne
              have hv' : ∃ v' ∈ (gateAt d.E jw).inputs, v' ≠ u' ∧ v' < n + m + jw := by
                rw [hin'] at hu'_mem ⊢
                rcases List.mem_pair.mp hu'_mem with rfl | rfl
                · exact ⟨b', by simp, hab'.symm, hb'_lt⟩
                · exact ⟨a', by simp, hab', ha'_lt⟩
              obtain ⟨v', hv'_mem, hvu', hv'_lt⟩ := hv'
              have hnqv' : ¬ reaches (n + m) d.E d.L q v' := by
                intro hqv'
                have heu' : edgeTo (n + m) d.E d.L u' (n + m + jw) := ⟨jw, hjwL, rfl, hu'_mem, hu'_lt⟩
                have hev' : edgeTo (n + m) d.E d.L v' (n + m + jw) := ⟨jw, hjwL, rfl, hv'_mem, hv'_lt⟩
                have huv' := activeReach_last_eq
                  (fun x y z hr _ e1 e2 => d.hsingle x (fun hx => by
                    have := reaches_le (activeReach_none_iff.mp hr); omega) y z e1 e2)
                  (activeReach_none_iff.mpr hqu') (activeReach_none_iff.mpr hqv')
                  (by simp) (by simp) heu' hev'
                exact hvu' huv'.symm
              have hfv' := false_of_no_not_reach d (parent_live d.hL hjwL ⟨hv'_mem, hv'_lt⟩) hnqv'
              rw [hweq, val_gate rfl, ha] at hvw_val
              simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hvw_val
              have hvt := hvw_val v' hv'_mem
              rw [if_pos hv'_lt, hfv'] at hvt
              exact Bool.noConfusion hvt
    exact fun w hqw hwR => hmain ((n + m + d.r) - w) w rfl hqw hwR
  obtain ⟨u_not, hun_in, hun_lt⟩ := d.hjnot_in
  have hun_live : live (n + m) d.L u_not := parent_live d.hL d.hjnotL ⟨by simp [hun_in], hun_lt⟩
  let U (x : ℕ → Bool) : Bool := value (n + m) d.E x (fun _ => none) u_not
  let B (x : ℕ → Bool) : Bool := value (n + m) d.E x (relay q false) (n + m + d.r)
  have h_decomp : ∀ x w, live (n + m) d.L w →
      reaches (n + m) d.E d.L q w → reaches (n + m) d.E d.L w (n + m + d.r) →
      value (n + m) d.E x (fun _ => none) w = ((!(U x)) || value (n + m) d.E x (relay q false) w) := by
    intro x w hw hqw hwR
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hweq : w = q
      · subst hweq
        rw [val_relay_at (by omega), Bool.or_false]
        rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun_in]
        simp only [GateOp.eval, List.map, hun_lt, ↓reduceIte, List.headD, U]
      · obtain ⟨k, hkL, rfl, hok⟩ := (h_or_path w hqw hwR).2 hweq
        have hk_ne : k ≠ d.j_not := fun eq => hweq (by simp [q, eq])
        obtain ⟨_, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two k hkL hk_ne
        rcases hqw.cases_tail with heq | ⟨u, hqu, ⟨jw, hjwL, hweq', hu_mem, hu_lt⟩⟩
        · exact False.elim (hweq heq)
        · have hjw_eq : jw = k := by omega
          subst jw
          have hv : ∃ v ∈ (gateAt d.E k).inputs, v ≠ u ∧ v < n + m + k := by
            rw [hin] at hu_mem ⊢
            rcases List.mem_pair.mp hu_mem with rfl | rfl
            · exact ⟨b, by simp, hab.symm, hb_lt⟩
            · exact ⟨a, by simp, hab, ha_lt⟩
          obtain ⟨v, hv_mem, hvu, hv_lt⟩ := hv
          have hnqv : ¬ reaches (n + m) d.E d.L q v := by
            intro hqv
            have heu : edgeTo (n + m) d.E d.L u (n + m + k) := ⟨k, hkL, rfl, hu_mem, hu_lt⟩
            have hev : edgeTo (n + m) d.E d.L v (n + m + k) := ⟨k, hkL, rfl, hv_mem, hv_lt⟩
            have huv := activeReach_last_eq
              (fun x' y z hr _ e1 e2 => d.hsingle x' (fun hx => by
                have := reaches_le (activeReach_none_iff.mp hr); omega) y z e1 e2)
              (activeReach_none_iff.mpr hqu) (activeReach_none_iff.mpr hqv)
              (by simp) (by simp) heu hev
            exact hvu huv.symm
          have hu_R : reaches (n + m) d.E d.L u (n + m + d.r) :=
            Relation.ReflTransGen.head ⟨k, hkL, rfl, hu_mem, hu_lt⟩ hwR
          have ihu := ih u hu_lt (parent_live d.hL hkL ⟨hu_mem, hu_lt⟩) hqu hu_R
          have hveq : value (n + m) d.E x (relay q false) v = value (n + m) d.E x (fun _ => none) v :=
            value_agree_of_fix_away d.hL (parent_live d.hL hkL ⟨hv_mem, hv_lt⟩)
              fun z _ hdiff hr => by
                simp only [relay] at hdiff; split_ifs at hdiff with hzq
                · subst hzq; exact hnqv hr
                · exact False.elim (hdiff rfl)
          have hq_ne_k : relay q false (n + m + k) = none := by simp [relay, hweq]
          rw [val_gate rfl, val_gate hq_ne_k, hok]
          simp only [GateOp.eval]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          constructor
          · rintro ⟨z, hz_mem, hzv⟩
            have hmem_z := hz_mem
            rw [hin] at hu_mem hv_mem hz_mem
            have hz_or : z = u ∨ z = v := by
              rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hu_mem with eu | eu <;>
                rcases List.mem_pair.mp hv_mem with ev | ev
              all_goals first
                | exact Or.inl eu.symm
                | exact Or.inr ev.symm
                | exact False.elim (hvu (ev.trans eu.symm))
            rcases hz_or with hzu | hzv_eq
            · rw [hzu] at hzv
              rw [if_pos hu_lt, ihu, Bool.or_eq_true] at hzv
              rcases hzv with hU | hBu
              · exact Or.inl hU
              · right; refine ⟨u, by rw [← hzu]; exact hmem_z, by rw [if_pos hu_lt]; exact hBu⟩
            · rw [hzv_eq] at hzv
              right; refine ⟨v, by rw [← hzv_eq]; exact hmem_z, by rw [if_pos hv_lt, hveq]; rw [if_pos hv_lt] at hzv; exact hzv⟩
          · rintro (hU | ⟨z, hz_mem, hzv⟩)
            · refine ⟨u, hu_mem, ?_⟩
              rw [if_pos hu_lt, ihu, Bool.or_eq_true]; exact Or.inl hU
            · have hmem_z := hz_mem
              have hu_mem0 := hu_mem
              have hv_mem0 := hv_mem
              rw [hin] at hu_mem hv_mem hz_mem
              have hz_or : z = u ∨ z = v := by
                rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
                  rcases List.mem_pair.mp hu_mem with eu | eu <;>
                  rcases List.mem_pair.mp hv_mem with ev | ev
                all_goals first
                  | exact Or.inl eu.symm
                  | exact Or.inr ev.symm
                  | exact False.elim (hvu (ev.trans eu.symm))
              rcases hz_or with hzu | hzv_eq
              · refine ⟨u, hu_mem0, ?_⟩
                rw [if_pos hu_lt, ihu, Bool.or_eq_true]; right; rw [hzu, if_pos hu_lt] at hzv; exact hzv
              · refine ⟨v, hv_mem0, ?_⟩
                rw [if_pos hv_lt, ← hveq]; rw [hzv_eq, if_pos hv_lt] at hzv; exact hzv
  have hA_eq : ∀ i j, A i j = ((!(U (oneEachRaw n m i j))) || B (oneEachRaw n m i j)) := by
    intro i j
    rw [← d.hRep i j]
    exact h_decomp _ (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) hq_root Relation.ReflTransGen.refl
  have hU_eq_fix : ∀ x, U x = value (n + m) d.E x (relay q false) u_not := by
    intro x
    exact value_agree_of_fix_away d.hL hun_live fun v _ hdiff hr => by
      simp only [relay] at hdiff
      split_ifs at hdiff with hvq
      · subst hvq; have := reaches_le hr; omega
      · exact False.elim (hdiff rfl)
  have hNoNot_q : ∀ j ∈ d.L, relay q false (n + m + j) = none → (gateAt d.E j).op ≠ .not := by
    intro j hj hnone ho
    have hjq := (d.hjnot j hj).mp ho
    simp [relay, q, hjq] at hnone
  have hU_mono : ∀ x y : ℕ → Bool, (∀ v < n + m, x v = true → y v = true) →
      U x = true → U y = true := by
    intro x y hxy hux
    rw [hU_eq_fix x] at hux; rw [hU_eq_fix y]
    exact eval_mono_inputs_of_fix d.hL d.hFan hNoNot_q hxy hun_live hux
  have hB_mono : ∀ x y : ℕ → Bool, (∀ v < n + m, x v = true → y v = true) →
      B x = true → B y = true := by
    intro x y hxy
    exact eval_mono_inputs_of_fix d.hL d.hFan hNoNot_q hxy (Or.inr ⟨d.r, d.hrL, rfl⟩)
  have h_agree_fix : ∀ (fix : ℕ → Option Bool) (x y : ℕ → Bool) (w : ℕ),
      live (n + m) d.L w → (∀ v < n + m, reaches (n + m) d.E d.L v w → x v = y v) →
      value (n + m) d.E x fix w = value (n + m) d.E y fix w := by
    intro fix x y w hw hxy
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases hw with low | ⟨j, hj, rfl⟩
      · rw [val_raw low, val_raw low]; exact hxy w low Relation.ReflTransGen.refl
      · cases hf : fix (n + m + j) with
        | some b => rw [val_fixed (by omega) hf, val_fixed (by omega) hf]
        | none =>
          rw [val_gate hf, val_gate hf]
          congr 1; apply List.map_congr_left; intro u hu
          split_ifs with hlt
          · exact ih u hlt (parent_live d.hL hj ⟨hu, hlt⟩)
              (fun v hv hr => hxy v hv (Relation.ReflTransGen.tail hr ⟨j, hj, rfl, hu, hlt⟩))
          · rfl
  have hU_zero : U (fun _ => false) = false :=
    false_of_no_not_reach d hun_live fun hr => by have := reaches_le hr; omega
  have hc0_away_R : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
    exact (d.hc0 d.c₀).mpr rfl
  have hr0_away_R : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  have hc0_away_unot : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) u_not :=
    fun h => hc0_away_R (h.trans ((Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, by simp [hun_in], hun_lt⟩).trans hq_root))
  have hc0_away_f : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) d.f :=
    fun h => hc0_away_R (h.trans (f_reaches_root d))
  have hB_c0 : ∀ i : Fin n, B (oneEachRaw n m i d.c₀) = false := by
    intro i
    by_contra htrue
    have hbt : B (oneEachRaw n m i d.c₀) = true := Bool.eq_true_of_not_eq_false htrue
    have hag := h_agree_fix (relay q false) (oneEachRaw n m i d.c₀) (fun w => decide (w = i.val))
      (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v hv hvr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_right (fun e => hc0_away_R (e ▸ hvr)), Or.inl⟩
    dsimp only [B] at hbt
    rw [hag] at hbt
    have hall : ∀ j : Fin m, A i j = true := by
      intro j
      have hB := hB_mono _ (oneEachRaw n m i j)
        (fun v _ hv => by simp only [oneEachRaw, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) hbt
      rw [hA_eq i j, hB, Bool.or_true]
    obtain ⟨j, hj⟩ := (no_empty_or_full_row hg.2.2.1 i).2
    rw [hall j] at hj; cases hj
  have hB_r0 : ∀ j : Fin m, B (oneEachRaw n m d.r₀ j) = false := by
    intro j
    by_contra htrue
    have hbt : B (oneEachRaw n m d.r₀ j) = true := Bool.eq_true_of_not_eq_false htrue
    have hag := h_agree_fix (relay q false) (oneEachRaw n m d.r₀ j) (fun w => decide (w = n + j.val))
      (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v hv hvr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away_R (e ▸ hvr)), Or.inr⟩
    dsimp only [B] at hbt
    rw [hag] at hbt
    have hall : ∀ i : Fin n, A i j = true := by
      intro i
      have hB := hB_mono _ (oneEachRaw n m i j)
        (fun v _ hv => by simp only [oneEachRaw, decide_eq_true_eq] at hv ⊢; exact Or.inr hv) hbt
      rw [hA_eq i j, hB, Bool.or_true]
    obtain ⟨i, hi⟩ := (no_empty_or_full_col hg.2.2.2.1 j).2
    rw [hall i] at hi; cases hi
  obtain ⟨l₀, hl₀⟩ := hg.2.2.2.1 d.c₀
  have h_not_lc : ¬ ∀ i, A i l₀ = true → A i d.c₀ = true :=
    fun h => hl₀ (Or.inr h)
  have hex : ∃ i₂ : Fin n, A i₂ l₀ = true ∧ A i₂ d.c₀ = false := by
    by_contra hno
    apply h_not_lc; intro i hi
    by_contra hc
    exact hno ⟨i, hi, Bool.eq_false_iff.mpr hc⟩
  obtain ⟨i₂, hi2_l, hi2_c⟩ := hex
  have hU_c0 : U (oneEachRaw n m i₂ d.c₀) = true := by
    have ha := hA_eq i₂ d.c₀
    rw [hi2_c, hB_c0 i₂, Bool.or_false, eq_comm, Bool.not_eq_false'] at ha
    exact ha
  have hU_i2 : U (fun w => decide (w = i₂.val)) = true := by
    rw [← hU_c0]
    exact h_agree_fix (fun _ => none) (fun w => decide (w = i₂.val)) (oneEachRaw n m i₂ d.c₀)
      u_not hun_live fun v hv hvu => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨Or.inl, fun h => h.resolve_right (fun e => hc0_away_unot (e ▸ hvu))⟩
  have hU_l0 : U (oneEachRaw n m i₂ l₀) = true :=
    hU_mono _ _ (fun v _ hv => by simp only [oneEachRaw, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) hU_i2
  have hB_l0 : B (oneEachRaw n m i₂ l₀) = true := by
    have ha := hA_eq i₂ l₀
    rw [hi2_l, hU_l0, Bool.not_true, Bool.false_or] at ha
    exact ha.symm
  have hl0_f : reaches (n + m) d.E d.L (n + l₀.val) d.f := by
    by_contra hnf
    have huniq : ∀ a b c, activeReach (n + m) d.E d.L none (n + l₀.val) a → (none : Option ℕ) ≠ some a →
        edgeTo (n + m) d.E d.L a b → edgeTo (n + m) d.E d.L a c → b = c := by
      intro a b c hr _ e1 e2
      rw [activeReach_none_iff] at hr
      exact d.hsingle a (fun heq => hnf (heq ▸ hr)) b c e1 e2
    have hsp := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := n + l₀.val) (by have := l₀.isLt; omega)
      huniq (Or.inr ⟨d.r, d.hrL, rfl⟩)
    exact contradict_IncC_of_unate hg d hl₀ hsp
  have hf_i2 : value (n + m) d.E (fun w => decide (w = i₂.val)) (fun _ => none) d.f = false := by
    by_contra hf_t
    have hf_true : value (n + m) d.E (fun w => decide (w = i₂.val)) (fun _ => none) d.f = true :=
      Bool.eq_true_of_not_eq_false hf_t
    have hf_live := parent_live d.hL d.hj1L d.hf_j1
    have hf_mono : ∀ x y : ℕ → Bool, (∀ v < n + m, x v = true → y v = true) →
        value (n + m) d.E x (fun _ => none) d.f = true →
        value (n + m) d.E y (fun _ => none) d.f = true := by
      intro x y hxy hvx
      have hfeq : ∀ z, value (n + m) d.E z (fun _ => none) d.f =
          value (n + m) d.E z (relay q false) d.f := by
        intro z
        exact value_agree_of_fix_away d.hL hf_live fun v _ hdiff hr => by
          simp only [relay] at hdiff; split_ifs at hdiff with hvq
          · subst hvq; have := reaches_le hr; omega
          · exact False.elim (hdiff rfl)
      rw [hfeq x] at hvx; rw [hfeq y]
      exact eval_mono_inputs_of_fix d.hL d.hFan hNoNot_q hxy hf_live hvx
    have hf_l0 : value (n + m) d.E (oneEachRaw n m i₂ l₀) (fun _ => none) d.f = true :=
      hf_mono _ _ (fun v _ hv => by simp only [oneEachRaw, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) hf_true
    have hB_z2 : B (fun w => decide (w = i₂.val)) = false := by
      have hag := h_agree_fix (relay q false) (oneEachRaw n m i₂ d.c₀) (fun w => decide (w = i₂.val))
        (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v _ hvr => by
          simp only [oneEachRaw, decide_eq_decide]
          exact ⟨fun h => h.resolve_right (fun e => hc0_away_R (e ▸ hvr)), Or.inl⟩
      dsimp only [B]
      rw [← hag]; exact hB_c0 i₂
    have hf_eq_z : value (n + m) d.E (oneEachRaw n m i₂ l₀) (relay q false) d.f =
        value (n + m) d.E (fun w => decide (w = i₂.val)) (relay q false) d.f := by
      have h1 : value (n + m) d.E (oneEachRaw n m i₂ l₀) (relay q false) d.f =
          value (n + m) d.E (oneEachRaw n m i₂ l₀) (fun _ => none) d.f :=
        value_agree_of_fix_away d.hL hf_live fun v _ hdiff hr => by
          simp only [relay] at hdiff; split_ifs at hdiff with hvq
          · subst hvq; have := reaches_le hr; omega
          · exact False.elim (hdiff rfl)
      have h2 : value (n + m) d.E (fun w => decide (w = i₂.val)) (relay q false) d.f =
          value (n + m) d.E (fun w => decide (w = i₂.val)) (fun _ => none) d.f :=
        value_agree_of_fix_away d.hL hf_live fun v _ hdiff hr => by
          simp only [relay] at hdiff; split_ifs at hdiff with hvq
          · subst hvq; have := reaches_le hr; omega
          · exact False.elim (hdiff rfl)
      rw [h1, h2, hf_l0, hf_true]
    have hc_B := cut_agree d.hL d.f d.hsingle (oneEachRaw n m i₂ l₀) (fun w => decide (w = i₂.val))
      (relay q false) (relay q false)
      (fun v _ hvnf => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_right (fun e => hvnf (e ▸ hl0_f)), Or.inl⟩)
      (fun _ _ _ => rfl) hf_eq_z (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (Or.inr fun hr => by
        have hlt1 := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
        have hle1 := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
        have hle2 := reaches_le hr
        omega)
    change B (oneEachRaw n m i₂ l₀) = B (fun w => decide (w = i₂.val)) at hc_B
    rw [hB_l0, hB_z2] at hc_B
    exact Bool.noConfusion hc_B
  by_cases hi2_f : reaches (n + m) d.E d.L i₂.val d.f
  · by_cases hun_eq : u_not = d.f
    · have hU_val : U (fun w => decide (w = i₂.val)) = false := by
        dsimp only [U]
        rw [hun_eq]
        exact hf_i2
      rw [hU_i2] at hU_val
      exact Bool.noConfusion hU_val
    · have hun_not_f : ¬ reaches (n + m) d.E d.L u_not d.f := by
        intro huf
        rcases huf.cases_head with heq | ⟨c, ec, hcf⟩
        · exact hun_eq heq
        · have euq : edgeTo (n + m) d.E d.L u_not q :=
            ⟨d.j_not, d.hjnotL, rfl, by simp [hun_in], hun_lt⟩
          have hcq := d.hsingle u_not hun_eq c q ec euq
          rw [hcq] at hcf
          have h1 := reaches_le hcf
          have h2 := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
          have h3 := reaches_le sd.h_hit_not
          omega
      have h_f0 : value (n + m) d.E (fun _ => false) (fun _ => none) d.f = false :=
        false_of_no_not_reach d (parent_live d.hL d.hj1L d.hf_j1)
          fun hr => by
            have h1 := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
            have h2 := reaches_le sd.h_hit_not
            have h3 := reaches_le hr
            omega
      have hcu := cut_agree d.hL d.f d.hsingle (fun w => decide (w = i₂.val)) (fun _ => false)
        (fun _ => none) (fun _ => none)
        (fun v _ hvnf => by
          simp only [decide_eq_false_iff_not]
          intro e; subst e; exact hvnf hi2_f)
        (fun _ _ _ => rfl) (hf_i2.trans h_f0.symm) hun_live
        (Or.inr fun hr => hun_not_f hr)
      change U (fun w => decide (w = i₂.val)) = U (fun _ => false) at hcu
      rw [hU_i2, hU_zero] at hcu
      exact Bool.noConfusion hcu
  · have hi2_unot : reaches (n + m) d.E d.L i₂.val u_not := by
      by_contra hnu
      have heq := h_agree_fix (fun _ => none) (fun w => decide (w = i₂.val)) (fun _ => false)
        u_not hun_live fun v _ hv => by
          simp only [decide_eq_false_iff_not]
          intro e; subst e; exact hnu hv
      change U (fun w => decide (w = i₂.val)) = U (fun _ => false) at heq
      rw [hU_i2, hU_zero] at heq
      exact Bool.noConfusion heq
    have hi2_q : reaches (n + m) d.E d.L i₂.val q :=
      Relation.ReflTransGen.tail hi2_unot ⟨d.j_not, d.hjnotL, rfl, by simp [hun_in], hun_lt⟩
    have haway_q : ¬ activeReach (n + m) d.E d.L (some q) i₂.val (n + m + d.r) := by
      have hqr : q < n + m + d.r := by
        have := reaches_le sd.h_not_J
        have := reaches_le sd.h_J_root
        have := sd.h_not_ne_J
        omega
      exact activeReach_skip_contra d.hsingle hi2_f hi2_q hqr
    have hag_i2 := unate_unchanged d.hL (skip := some q) (fix := relay q false)
      (fun v => by simp [relay, eq_comm]) (fun v hv => by cases hv; simp [q])
      (i := i₂.val) (x := oneEachRaw n m i₂ l₀) (y := fun w => decide (w = n + l₀.val))
      (fun w _ hwi => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left hwi, Or.inr⟩)
      (Or.inr ⟨d.r, d.hrL, rfl⟩) haway_q
    have hag_r0 := h_agree_fix (relay q false) (oneEachRaw n m d.r₀ l₀) (fun w => decide (w = n + l₀.val))
      (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v _ hvr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away_R (e ▸ hvr)), Or.inr⟩
    change B (oneEachRaw n m i₂ l₀) = B (fun w => decide (w = n + l₀.val)) at hag_i2
    change B (oneEachRaw n m d.r₀ l₀) = B (fun w => decide (w = n + l₀.val)) at hag_r0
    rw [hB_l0, ← hag_r0, hB_r0 l₀] at hag_i2
    exact Bool.noConfusion hag_i2

-- Step 4 & Step 5: u_not = d.f, evalT, singletons S_r = {u₁}, S_c = {v₁}, and f = u₁ || v₁

theorem value_agree_inputs {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (fix : ℕ → Option Bool) {x y : ℕ → Bool} {w : ℕ} (hw : live N L w)
    (hxy : ∀ v < N, reaches N C L v w → x v = y v) :
    value N C x fix w = value N C y fix w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]; exact hxy w low Relation.ReflTransGen.refl
    · cases hf : fix (N + j) with
      | some b => rw [val_fixed (by omega) hf, val_fixed (by omega) hf]
      | none =>
        rw [val_gate hf, val_gate hf]
        congr 1; apply List.map_congr_left; intro u hu
        split_ifs with hlt
        · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩)
            (fun v hv hr => hxy v hv (Relation.ReflTransGen.tail hr ⟨j, hj, rfl, hu, hlt⟩))
        · rfl

theorem eval_mono_bound {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C) {fix₀ fix₁ : ℕ → Option Bool} {q : ℕ}
    (hfix_some : ∀ j ∈ L, N + j < q → ∀ b₀, fix₀ (N + j) = some b₀ →
      ∃ b₁, fix₁ (N + j) = some b₁ ∧ (b₀ = true → b₁ = true))
    (hfix_none : ∀ j ∈ L, N + j < q → fix₀ (N + j) = none →
      fix₁ (N + j) = none ∧ (gateAt C j).op ≠ .not)
    {x y : ℕ → Bool} (hxy : ∀ v < N, x v = true → y v = true)
    {w : ℕ} (hw : live N L w) (hwq : w < q) :
    value N C x fix₀ w = true → value N C y fix₁ w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hval
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low] at hval; rw [val_raw low]; exact hxy w low hval
    · cases hf0 : fix₀ (N + j) with
      | some b₀ =>
        obtain ⟨b₁, hf1, hb⟩ := hfix_some j hj hwq b₀ hf0
        rw [val_fixed (by omega) hf0] at hval; rw [val_fixed (by omega) hf1]
        exact hb hval
      | none =>
        obtain ⟨hf1, hno⟩ := hfix_none j hj hwq hf0
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
          exact List.getElem_mem _
        rw [val_gate hf0] at hval; rw [val_gate hf1]
        have h_ao : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          rcases (hFan _ hmem).1 with ho | ho | ho
          · exact Or.inl ho
          · exact Or.inr ho
          · exact False.elim (hno ho)
        rcases h_ao with ha | ho
        · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hval ⊢
          intro u hu
          have hxu := hval u hu
          split_ifs with hlt
          · rw [if_pos hlt] at hxu
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (by omega) hxu
          · rw [if_neg hlt] at hxu; cases hxu
        · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval ⊢
          obtain ⟨u, hu, hxu⟩ := hval
          refine ⟨u, hu, ?_⟩
          split_ifs with hlt
          · rw [if_pos hlt] at hxu
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) (by omega) hxu
          · rw [if_neg hlt] at hxu; cases hxu

theorem gate_has_input_path {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {w : ℕ} (hw : live (n + m) d.L w) :
    ∃ v < n + m, reaches (n + m) d.E d.L v w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · exact ⟨w, low, Relation.ReflTransGen.refl⟩
    · by_cases hjn : j = d.j_not
      · subst hjn
        obtain ⟨u, hun_in, hun_lt⟩ := d.hjnot_in
        obtain ⟨v, hvN, hvu⟩ := ih u hun_lt (parent_live d.hL hj ⟨by simp [hun_in], hun_lt⟩)
        exact ⟨v, hvN, Relation.ReflTransGen.tail hvu ⟨d.j_not, hj, rfl, by simp [hun_in], hun_lt⟩⟩
      · obtain ⟨_, a, _, _, hin, ha_lt, _⟩ := d.hother_two j hj hjn
        obtain ⟨v, hvN, hva⟩ := ih a ha_lt (parent_live d.hL hj ⟨by simp [hin], ha_lt⟩)
        exact ⟨v, hvN, Relation.ReflTransGen.tail hva ⟨j, hj, rfl, by simp [hin], ha_lt⟩⟩

theorem reaches_branch_at_f {N : ℕ} {C : Circuit} {L : Finset ℕ} {f : ℕ}
    (hsingle : ∀ a ≠ f, ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {u w : ℕ} (huf : reaches N C L u f) (huw : reaches N C L u w) :
    reaches N C L f w ∨ reaches N C L w f := by
  have aux : ∀ k u, f - u = k → reaches N C L u f → reaches N C L u w →
      reaches N C L f w ∨ reaches N C L w f := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro u hk huf huw
      by_cases huf_eq : u = f
      · subst huf_eq; exact Or.inl huw
      · by_cases huw_eq : u = w
        · subst huw_eq; exact Or.inr huf
        · rcases huf.cases_head with h | ⟨a, ea, haf⟩
          · exact False.elim (huf_eq h)
          · rcases huw.cases_head with h | ⟨b, eb, hbw⟩
            · exact False.elim (huw_eq h)
            · have hab := hsingle u huf_eq a b ea eb
              subst hab
              have hlt := edgeTo_lt ea
              have hle := reaches_le haf
              exact ih (f - a) (by omega) a rfl haf hbw
  exact aux (f - u) u rfl huf huw

theorem activeReach_to_reaches {N : ℕ} {C : Circuit} {L : Finset ℕ} {skip : Option ℕ}
    {u w : ℕ} (ha : activeReach N C L skip u w) : reaches N C L u w :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ ha

theorem reaches_live {N : ℕ} {C : Circuit} {L : Finset ℕ} {u w : ℕ}
    (hu : live N L u) (hr : reaches N C L u w) : live N L w := by
  rcases hr.cases_tail with rfl | ⟨_, _, ⟨j, hj, rfl, _⟩⟩
  · exact hu
  · exact Or.inr ⟨j, hj, rfl⟩

theorem jnot_input_lt {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {u : ℕ} (hun : (gateAt d.E d.j_not).inputs = [u]) : u < n + m + d.j_not := by
  obtain ⟨u', hun', hlt⟩ := d.hjnot_in
  rw [hun] at hun'
  cases hun'
  exact hlt

theorem activeReach_of_lt {N : ℕ} {C : Circuit} {L : Finset ℕ} {f u w : ℕ}
    (hfu : f < u) (hr : reaches N C L u w) : activeReach N C L (some f) u w := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hua eb ih =>
    have hle := reaches_le hua
    exact Relation.ReflTransGen.tail ih ⟨fun h => by cases h; omega, eb⟩

theorem reaches_active_or_f {N : ℕ} {C : Circuit} {L : Finset ℕ} {f u w : ℕ}
    (hr : reaches N C L u w) :
    activeReach N C L (some f) u w ∨ reaches N C L u f := by
  induction hr with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail a b hua eb ih =>
    rcases ih with ha | hf
    · by_cases haf : a = f
      · exact Or.inr (haf ▸ activeReach_to_reaches ha)
      · exact Or.inl (Relation.ReflTransGen.tail ha ⟨fun h => haf (Option.some.inj h.symm), eb⟩)
    · exact Or.inr hf

theorem activeReach_skip_f_lt {N : ℕ} {C : Circuit} {L : Finset ℕ} {f u w : ℕ}
    (hsingle : ∀ a ≠ f, ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (hfw : f < w) (huf : reaches N C L u f) (ha : activeReach N C L (some f) u w) : False := by
  have hmain : ∀ k u, f - u = k → reaches N C L u f → activeReach N C L (some f) u w → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro u hk huf ha
      rcases ha.cases_head with rfl | ⟨b, hb, hbw⟩
      · have := reaches_le huf; omega
      · rcases huf.cases_head with rfl | ⟨a, ea, haf⟩
        · exact hb.1 rfl
        · have huf_ne : u ≠ f := fun e => hb.1 (by rw [e])
          have hab := hsingle u huf_ne a b ea hb.2
          rw [← hab] at hbw
          have hlt := edgeTo_lt ea
          have hle := reaches_le haf
          exact ih (f - a) (by omega) a rfl haf hbw
  exact hmain (f - u) u rfl huf ha

theorem eval_unchanged_of_not_active {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (skip : ℕ) (hskip : N ≤ skip) (fix : ℕ → Option Bool) (hfix : ∃ b, fix skip = some b)
    {v : ℕ} {x y : ℕ → Bool} (hxy : ∀ w < N, w ≠ v → x w = y w)
    {w : ℕ} (hw : live N L w) (hna : ¬ activeReach N C L (some skip) v w) :
    value N C x fix w = value N C y fix w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
      exact hxy w low fun e => hna (e ▸ Relation.ReflTransGen.refl)
    · cases hf : fix (N + j) with
      | some b => rw [val_fixed (by omega) hf, val_fixed (by omega) hf]
      | none =>
        rw [val_gate hf, val_gate hf]
        congr 1; apply List.map_congr_left; intro u hu
        split_ifs with hlt
        · by_cases hus : u = skip
          · subst hus; obtain ⟨b, hb⟩ := hfix
            rw [val_fixed hskip hb, val_fixed hskip hb]
          · have hnau : ¬ activeReach N C L (some skip) v u := fun hau =>
              hna (Relation.ReflTransGen.tail hau ⟨fun h => hus (Option.some.inj h.symm), ⟨j, hj, rfl, hu, hlt⟩⟩)
            exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩) hnau
        · rfl

theorem value_subst_node {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (c : ℕ) (fix₁ fix₂ : ℕ → Option Bool) {x : ℕ → Bool}
    (hfix : ∀ u, u ≠ c → fix₁ u = fix₂ u)
    (hc : value N C x fix₁ c = value N C x fix₂ c)
    {w : ℕ} (hw : live N L w) :
    value N C x fix₁ w = value N C x fix₂ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwc : w = c
    · subst hwc; exact hc
    · rcases hw with low | ⟨j, hj, rfl⟩
      · rw [val_raw low, val_raw low]
      · have hfeq := hfix (N + j) hwc
        cases hf1 : fix₁ (N + j) with
        | some b =>
          have hf2 : fix₂ (N + j) = some b := hfeq.symm.trans hf1
          rw [val_fixed (by omega) hf1, val_fixed (by omega) hf2]
        | none =>
          have hf2 : fix₂ (N + j) = none := hfeq.symm.trans hf1
          rw [val_gate hf1, val_gate hf2]
          congr 1; apply List.map_congr_left; intro u hu
          split_ifs with hlt
          · exact ih u hlt (parent_live hL hj ⟨hu, hlt⟩)
          · rfl

theorem value_subst_relay {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (c : ℕ) (hcN : N ≤ c) (b : Bool) {x : ℕ → Bool}
    (hc : value N C x (fun _ => none) c = b)
    {w : ℕ} (hw : live N L w) :
    value N C x (fun _ => none) w = value N C x (relay c b) w :=
  value_subst_node hL c (fun _ => none) (relay c b)
    (fun u hu => by dsimp only [relay]; rw [if_neg hu])
    (by rw [val_relay_at hcN]; exact hc) hw

theorem evalT_q_mono {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {x : ℕ → Bool} {w : ℕ} (hw : live (n + m) d.L w) :
    value (n + m) d.E x (relay (n + m + d.j_not) false) w = true →
    value (n + m) d.E x (relay (n + m + d.j_not) true) w = true :=
  eval_mono_bound d.hL d.hFan
    (fun j _ _ b₀ hb₀ => by
      by_cases hjq : j = d.j_not
      · subst hjq; dsimp only [relay] at hb₀ ⊢; rw [if_pos rfl] at hb₀ ⊢; cases hb₀; exact ⟨true, rfl, fun _ => rfl⟩
      · have hne : n + m + j ≠ n + m + d.j_not := by omega
        dsimp only [relay] at hb₀; rw [if_neg hne] at hb₀; cases hb₀)
    (fun j hj _ hnone => by
      by_cases hjq : j = d.j_not
      · subst hjq; dsimp only [relay] at hnone; rw [if_pos rfl] at hnone; cases hnone
      · have hne : n + m + j ≠ n + m + d.j_not := by omega
        dsimp only [relay] at ⊢; rw [if_neg hne]
        exact ⟨rfl, fun ho => hjq ((d.hjnot j hj).mp ho)⟩)
    (fun _ _ => id) hw (Nat.lt_succ_self w)

theorem B_r0_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d) (j : Fin m) :
    value (n + m) d.E (oneEachRaw n m d.r₀ j) (relay (n + m + d.j_not) false) (n + m + d.r) = false := by
  let q := n + m + d.j_not
  have hq_lt_R : q < n + m + d.r := by
    have := reaches_le sd.h_not_J
    have := reaches_le sd.h_J_root
    have := sd.h_not_ne_J
    omega
  have hq_ne_f : q ≠ d.f := by
    have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
    have := reaches_le sd.h_hit_not
    omega
  by_contra htrue
  have hbt := Bool.eq_true_of_not_eq_false htrue
  have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  have hz : value (n + m) d.E (fun w => decide (w = n + j.val)) (relay q false) (n + m + d.r) = true := by
    rw [← value_agree_inputs d.hL (relay q false) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
      fun w _ hwr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩]
    exact hbt
  have hall : ∀ i : Fin n, A i j = true := by
    intro i
    have hb0 : value (n + m) d.E (oneEachRaw n m i j) (relay q false) (n + m + d.r) = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := relay q false) (fix₁ := relay q false)
        (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
        (fun k hk _ hnone => ⟨hnone, fun ho => by
          have := (d.hjnot k hk).mp ho
          simp [relay, q, this] at hnone⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
        (Or.inr ⟨d.r, d.hrL, rfl⟩) (Nat.lt_succ_self _) hz
    rw [← d.hRep i j]
    cases hqv : value (n + m) d.E (oneEachRaw n m i j) (fun _ => none) q with
    | false =>
      rw [value_subst_relay d.hL q (by omega) false hqv (Or.inr ⟨d.r, d.hrL, rfl⟩)]
      exact hb0
    | true =>
      rw [value_subst_relay d.hL q (by omega) true hqv (Or.inr ⟨d.r, d.hrL, rfl⟩)]
      exact evalT_q_mono d (Or.inr ⟨d.r, d.hrL, rfl⟩) hb0
  obtain ⟨i, hi⟩ := (no_empty_or_full_col hg.2.2.2.1 j).2
  rw [hall i] at hi; cases hi

theorem B_c0_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d) (i : Fin n) :
    value (n + m) d.E (oneEachRaw n m i d.c₀) (relay (n + m + d.j_not) false) (n + m + d.r) = false := by
  let q := n + m + d.j_not
  have hq_lt_R : q < n + m + d.r := by
    have := reaches_le sd.h_not_J
    have := reaches_le sd.h_J_root
    have := sd.h_not_ne_J
    omega
  have hq_ne_f : q ≠ d.f := by
    have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
    have := reaches_le sd.h_hit_not
    omega
  by_contra htrue
  have hbt := Bool.eq_true_of_not_eq_false htrue
  have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
    exact (d.hc0 d.c₀).mpr rfl
  have hz : value (n + m) d.E (fun w => decide (w = i.val)) (relay q false) (n + m + d.r) = true := by
    rw [← value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
      fun w _ hwr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hwr)), Or.inl⟩]
    exact hbt
  have hall : ∀ j : Fin m, A i j = true := by
    intro j
    have hb0 : value (n + m) d.E (oneEachRaw n m i j) (relay q false) (n + m + d.r) = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := relay q false) (fix₁ := relay q false)
        (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
        (fun k hk _ hnone => ⟨hnone, fun ho => by
          have := (d.hjnot k hk).mp ho
          simp [relay, q, this] at hnone⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
        (Or.inr ⟨d.r, d.hrL, rfl⟩) (Nat.lt_succ_self _) hz
    rw [← d.hRep i j]
    cases hqv : value (n + m) d.E (oneEachRaw n m i j) (fun _ => none) q with
    | false =>
      rw [value_subst_relay d.hL q (by omega) false hqv (Or.inr ⟨d.r, d.hrL, rfl⟩)]
      exact hb0
    | true =>
      rw [value_subst_relay d.hL q (by omega) true hqv (Or.inr ⟨d.r, d.hrL, rfl⟩)]
      exact evalT_q_mono d (Or.inr ⟨d.r, d.hrL, rfl⟩) hb0
  obtain ⟨j, hj⟩ := (no_empty_or_full_row hg.2.2.1 i).2
  rw [hall j] at hj; cases hj

theorem u_not_eq_f {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hA00 : A d.r₀ d.c₀ = false)
    {u_not : ℕ} (hun : (gateAt d.E d.j_not).inputs = [u_not]) :
    u_not = d.f := by
  classical
  let q := n + m + d.j_not
  have hq_live : live (n + m) d.L q := Or.inr ⟨d.j_not, d.hjnotL, rfl⟩
  have hun_lt : u_not < q := jnot_input_lt d hun
  have hun_lt' : u_not < n + m + d.j_not := hun_lt
  have hun_mem' : u_not ∈ (gateAt d.E d.j_not).inputs := by rw [hun]; simp
  have hun_live : live (n + m) d.L u_not := parent_live d.hL d.hjnotL ⟨hun_mem', hun_lt⟩
  have hq_lt_R : q < n + m + d.r := by
    have := reaches_le sd.h_not_J
    have := reaches_le sd.h_J_root
    have := sd.h_not_ne_J
    omega
  have hf_q : reaches (n + m) d.E d.L d.f q :=
    Relation.ReflTransGen.head ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩ sd.h_hit_not
  have hf_lt_q : d.f < q := by
    have h1 := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
    have h2 := reaches_le sd.h_hit_not
    omega
  have hf_unot : reaches (n + m) d.E d.L d.f u_not := by
    rcases hf_q.cases_tail with h | ⟨w, hfw, ⟨k, _, hkq, hw_mem, _⟩⟩
    · exact False.elim (by omega)
    · have hk : k = d.j_not := by omega
      subst hk
      rw [hun] at hw_mem
      have heq : w = u_not := by simpa using hw_mem
      exact heq ▸ hfw
  by_contra hun_ne
  have hf_lt_unot : d.f < u_not := by
    have := reaches_le hf_unot
    omega
  let H_r : Finset (Fin n) := Finset.univ.filter fun i =>
    ¬ reaches (n + m) d.E d.L i.val d.f ∧ reaches (n + m) d.E d.L i.val u_not
  let H_c : Finset (Fin m) := Finset.univ.filter fun j =>
    ¬ reaches (n + m) d.E d.L (n + j.val) d.f ∧ reaches (n + m) d.E d.L (n + j.val) u_not
  have hanti_through_q : ∀ v < n + m, ¬ reaches (n + m) d.E d.L v d.f → reaches (n + m) d.E d.L v u_not →
      ∀ x y : ℕ → Bool, (∀ w < n + m, w ≠ v → x w = y w) → (x v = true → y v = true) →
      value (n + m) d.E y (fun _ => none) (n + m + d.r) = true →
      value (n + m) d.E x (fun _ => none) (n + m + d.r) = true := by
    intro v hvN hnvf hnv_unot x y hraw hxy hyR
    let fv := value (n + m) d.E x (fun _ => none) d.f
    have hfx_eq : value (n + m) d.E y (fun _ => none) d.f = fv :=
      value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
        fun w hwN hwf => (hraw w hwN (fun e => hnvf (e ▸ hwf))).symm
    have hy_fix : value (n + m) d.E y (fun _ => none) (n + m + d.r) =
        value (n + m) d.E y (relay d.f fv) (n + m + d.r) := by
      apply cut_agree d.hL d.f d.hsingle y y (fun _ => none) (relay d.f fv)
        (fun _ _ _ => rfl) (fun w _ hwf => by simp [relay, hwf])
      · rw [val_relay_at sd.d_N_le_f]; exact hfx_eq
      · exact Or.inr ⟨d.r, d.hrL, rfl⟩
      · right; intro hr
        have h1 := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
        have h2 := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
        have h3 := reaches_le hr
        omega
    have hx_fix : value (n + m) d.E x (fun _ => none) (n + m + d.r) =
        value (n + m) d.E x (relay d.f fv) (n + m + d.r) := by
      apply cut_agree d.hL d.f d.hsingle x x (fun _ => none) (relay d.f fv)
        (fun _ _ _ => rfl) (fun w _ hwf => by simp [relay, hwf])
      · rw [val_relay_at sd.d_N_le_f]
      · exact Or.inr ⟨d.r, d.hrL, rfl⟩
      · right; intro hr
        have h1 := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
        have h2 := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
        have h3 := reaches_le hr
        omega
    have hmono_unot : value (n + m) d.E x (relay d.f fv) u_not = true →
        value (n + m) d.E y (relay d.f fv) u_not = true :=
      eval_mono_bound d.hL d.hFan
        (fun j _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
        (fun j hj hlt hnone => ⟨hnone, fun ho => by
          have := (d.hjnot j hj).mp ho
          change n + m + j < q at hlt
          omega⟩)
        (fun w hwN hwx => by
          by_cases hwv : w = v
          · exact hwv ▸ hxy (hwv ▸ hwx)
          · rw [← hraw w hwN hwv]; exact hwx)
        hun_live hun_lt
    have hq_anti : value (n + m) d.E y (relay d.f fv) q = true →
        value (n + m) d.E x (relay d.f fv) q = true := by
      have hqf : relay d.f fv q = none := by simp [relay, Nat.ne_of_gt hf_lt_q]
      rw [val_gate hqf, val_gate hqf, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
      simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
      intro hyq
      by_cases hxu : value (n + m) d.E x (relay d.f fv) u_not = true
      · rw [hmono_unot hxu, Bool.not_true] at hyq; cases hyq
      · simp only [Bool.eq_false_iff.mpr hxu, Bool.not_false]
    have hvq : reaches (n + m) d.E d.L v q :=
      Relation.ReflTransGen.tail hnv_unot ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
    have hvq_act : activeReach (n + m) d.E d.L (some d.f) v q :=
      (reaches_active_or_f hvq).resolve_right hnvf
    have hq_root : reaches (n + m) d.E d.L q (n + m + d.r) :=
      reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL
    have h_above_q : ∀ w, live (n + m) d.L w → reaches (n + m) d.E d.L q w →
        value (n + m) d.E y (relay d.f fv) w = true →
        value (n + m) d.E x (relay d.f fv) w = true := by
      intro w hw hqw hwy
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hwq : w = q
        · subst hwq; exact hq_anti hwy
        · rcases hw with low | ⟨j, hj, rfl⟩
          · have := reaches_le hqw; omega
          · have hjne : j ≠ d.j_not := fun e => hwq (by rw [e])
            have hlt_qw : q < n + m + j := by
              have := reaches_le hqw
              exact Nat.lt_of_le_of_ne this (Ne.symm hwq)
            have hjf : relay d.f fv (n + m + j) = none := by
              simp [relay]; omega
            rw [val_gate hjf] at hwy ⊢
            obtain ⟨hao, _, _, _, _, _, _⟩ := d.hother_two j hj hjne
            have handle_in {u : ℕ} (hu_mem : u ∈ (gateAt d.E j).inputs) (hu_lt : u < n + m + j) :
                value (n + m) d.E y (relay d.f fv) u = true →
                value (n + m) d.E x (relay d.f fv) u = true := by
              intro hyu
              by_cases hqu : reaches (n + m) d.E d.L q u
              · exact ih u hu_lt (parent_live d.hL hj ⟨hu_mem, hu_lt⟩) hqu hyu
              · have haway : ¬ reaches (n + m) d.E d.L v u := by
                  intro hvu
                  have ha_vu := (reaches_active_or_f hvu).resolve_right hnvf
                  rcases hqw.cases_tail with heq | ⟨u', hqu', ⟨k', _, hkeq, hu'_mem, hu'_lt⟩⟩
                  · exact hwq heq
                  · have hk' : k' = j := by omega
                    subst k'
                    have ha_qu' : activeReach (n + m) d.E d.L (some d.f) q u' :=
                      activeReach_of_lt hf_lt_q hqu'
                    have ha_vu' : activeReach (n + m) d.E d.L (some d.f) v u' := hvq_act.trans ha_qu'
                    have hne1 : (some d.f : Option ℕ) ≠ some u' := by
                      have := reaches_le hqu'; simp; omega
                    have hne2 : (some d.f : Option ℕ) ≠ some u := by
                      intro e; cases e; exact hnvf (activeReach_to_reaches ha_vu)
                    have heq := activeReach_last_eq
                      (fun a' b' c' hr' _ e1 e2 => d.hsingle a'
                        (fun ea => hnvf (ea ▸ activeReach_to_reaches hr')) b' c' e1 e2)
                      ha_vu' ha_vu hne1 hne2 ⟨j, hj, rfl, hu'_mem, hu'_lt⟩ ⟨j, hj, rfl, hu_mem, hu_lt⟩
                    exact hqu (heq ▸ hqu')
                have hxy_u := value_agree_inputs d.hL (relay d.f fv) (parent_live d.hL hj ⟨hu_mem, hu_lt⟩)
                  fun w' hw'N hw'u => (hraw w' hw'N (fun e => haway (e ▸ hw'u))).symm
                rw [← hxy_u]; exact hyu
            rcases hao with ha | ho
            · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hwy ⊢
              intro u hu
              have hyu := hwy u hu
              split_ifs with hlt
              · rw [if_pos hlt] at hyu; exact handle_in hu hlt hyu
              · rw [if_neg hlt] at hyu; cases hyu
            · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwy ⊢
              obtain ⟨u, hu, hyu⟩ := hwy
              refine ⟨u, hu, ?_⟩
              split_ifs with hlt
              · rw [if_pos hlt] at hyu; exact handle_in hu hlt hyu
              · rw [if_neg hlt] at hyu; cases hyu
    rw [hy_fix] at hyR; rw [hx_fix]
    exact h_above_q (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩) hq_root hyR
  have hr_sub : ∀ r_h ∈ H_r, ∀ j : Fin m, A r_h j = true → A d.r₀ j = true := by
    intro r_h hmem j hrj
    simp only [H_r, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [← d.hRep r_h j] at hrj
    rw [← d.hRep d.r₀ j]
    have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
      rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
      exact (d.hr0 d.r₀).mpr rfl
    have hz1 : value (n + m) d.E (oneEachRaw n m d.r₀ j) (fun _ => none) (n + m + d.r) =
        value (n + m) d.E (fun w => decide (w = n + j.val)) (fun _ => none) (n + m + d.r) :=
      value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hwr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
    rw [hz1]
    exact hanti_through_q r_h.val (by have := r_h.isLt; omega) hmem.1 hmem.2
      (fun w => decide (w = n + j.val)) (oneEachRaw n m r_h j)
      (fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨Or.inr, fun h => h.resolve_left hw⟩)
      (fun h => by simp at h; omega) hrj
  have hc_sub : ∀ c_h ∈ H_c, ∀ i : Fin n, A i c_h = true → A i d.c₀ = true := by
    intro c_h hmem i hic
    simp only [H_c, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [← d.hRep i c_h] at hic
    rw [← d.hRep i d.c₀]
    have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
      rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
      exact (d.hc0 d.c₀).mpr rfl
    have hz1 : value (n + m) d.E (oneEachRaw n m i d.c₀) (fun _ => none) (n + m + d.r) =
        value (n + m) d.E (fun w => decide (w = i.val)) (fun _ => none) (n + m + d.r) :=
      value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hwr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hwr)), Or.inl⟩
    rw [hz1]
    exact hanti_through_q (n + c_h.val) (by have := c_h.isLt; omega) hmem.1 hmem.2
      (fun w => decide (w = i.val)) (oneEachRaw n m i c_h)
      (fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨Or.inl, fun h => h.resolve_right hw⟩)
      (fun h => by simp at h; omega) hic
  obtain ⟨k₀, hk₀⟩ := hg.2.2.1 d.r₀
  have hk0_not_Hr : k₀ ∉ H_r := fun hm => hk₀ (Or.inr (hr_sub k₀ hm))
  have hk0_f : reaches (n + m) d.E d.L k₀.val d.f := by
    by_contra hnf
    have hk0_nu : ¬ reaches (n + m) d.E d.L k₀.val u_not :=
      fun hu => hk0_not_Hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnf, hu⟩)
    have hsp := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := k₀.val) (by have := k₀.isLt; omega)
      (fun a b c hr _ e1 e2 => d.hsingle a (fun ha => by
        rw [activeReach_none_iff] at hr; exact hnf (ha ▸ hr)) b c e1 e2)
      (Or.inr ⟨d.r, d.hrL, rfl⟩)
    exact contradict_IncR_of_unate hg d hk₀ hsp
  obtain ⟨j_star, hj_r0, hj_k0⟩ : ∃ j : Fin m, A d.r₀ j = true ∧ A k₀ j = false := by
    by_contra hnone
    apply hk₀; left; intro j hj
    by_contra hc
    exact hnone ⟨j, hj, Bool.eq_false_iff.mpr hc⟩
  have hj_not_Hc : j_star ∉ H_c := by
    intro hm
    have := hc_sub j_star hm d.r₀ hj_r0
    rw [hA00] at this; cases this
  have hf_val_k0_r0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f = true ∧
      value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f = false := by
    have hfr0_eq : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f =
        value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) d.f := by
      have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
        exact (d.hr0 d.r₀).mpr rfl
      exact value_agree_inputs d.hL _ (parent_live d.hL d.hj1L d.hf_j1) fun w _ hwf => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩
    have h_same_iff : ∀ h : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f =
        value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f, False := by
      intro h
      have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
        exact (d.hr0 d.r₀).mpr rfl
      have hr0_f_eq : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f =
          value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) d.f :=
        value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
          fun w _ hwf => by
            simp only [oneEachRaw, decide_eq_decide]
            exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩
      have hsame := cut_agree d.hL d.f d.hsingle
        (oneEachRaw n m k₀ j_star) (fun w => decide (w = n + j_star.val))
        (fun _ => none) (fun _ => none)
        (fun w _ hwf => by
          simp only [oneEachRaw, decide_eq_decide]
          constructor
          · intro h
            rcases h with rfl | hw
            · exact False.elim (hwf hk0_f)
            · exact hw
          · intro hw; exact Or.inr hw)
        (fun _ _ _ => rfl) (h.trans hr0_f_eq) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (Or.inr fun hr => by
          have h1 := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
          have h2 := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
          have h3 := reaches_le hr
          omega)
      have hr0_same := value_agree_inputs d.hL (fun _ => none) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (x := oneEachRaw n m d.r₀ j_star) (y := fun w => decide (w = n + j_star.val))
        fun w _ hwr => by
          simp only [oneEachRaw, decide_eq_decide]
          exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
      rw [← hr0_same, d.hRep k₀ j_star, d.hRep d.r₀ j_star, hj_k0, hj_r0] at hsame
      cases hsame
    have hf_0j_false : value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) d.f = false := by
      by_contra htrue
      have hft := Bool.eq_true_of_not_eq_false htrue
      have hfk : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f = true :=
        eval_mono_bound d.hL d.hFan
          (fun _ _ _ _ h => by simp at h)
          (fun j hj hlt _ => ⟨rfl, fun ho => by
            have := (d.hjnot j hj).mp ho; change n + m + j < q at hlt; omega⟩)
          (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
          (parent_live d.hL d.hj1L d.hf_j1) hf_lt_q hft
      exact h_same_iff (hfk.trans (hfr0_eq ▸ hft).symm)
    refine ⟨?_, hfr0_eq.trans hf_0j_false⟩
    by_contra hkf_f
    exact h_same_iff ((Bool.eq_false_iff.mpr hkf_f).trans (hfr0_eq.trans hf_0j_false).symm)
  have hU_k0_r0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) u_not = true ∧
      value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) u_not = false := by
    have hU_ne : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) u_not ≠
        value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) u_not := by
      intro heq
      let qv := !(value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) u_not)
      have hqr0 : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) q = qv := by
        rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
        simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
        rfl
      have hqk0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) q = qv := by
        rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
        simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD, heq]
        rfl
      have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
        exact (d.hr0 d.r₀).mpr rfl
      have hr0_R : value (n + m) d.E (fun w => decide (w = n + j_star.val)) (relay q qv) (n + m + d.r) = true := by
        rw [← value_agree_inputs d.hL (relay q qv) (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (x := oneEachRaw n m d.r₀ j_star) (y := fun w => decide (w = n + j_star.val))
          fun w _ hwr => by
            simp only [oneEachRaw, decide_eq_decide]
            exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩]
        rw [← value_subst_relay d.hL q (by omega) qv hqr0 (Or.inr ⟨d.r, d.hrL, rfl⟩)]
        rw [d.hRep d.r₀ j_star]; exact hj_r0
      have hk0_R : value (n + m) d.E (oneEachRaw n m k₀ j_star) (relay q qv) (n + m + d.r) = true :=
        eval_mono_bound d.hL d.hFan (fix₀ := relay q qv) (fix₁ := relay q qv)
          (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
          (fun k hk _ hnone => ⟨hnone, fun ho => by
            have := (d.hjnot k hk).mp ho
            simp [relay, q, this] at hnone⟩)
          (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
          (Or.inr ⟨d.r, d.hrL, rfl⟩) (Nat.lt_succ_self _) hr0_R
      rw [← value_subst_relay d.hL q (by omega) qv hqk0 (Or.inr ⟨d.r, d.hrL, rfl⟩)] at hk0_R
      rw [d.hRep k₀ j_star, hj_k0] at hk0_R; cases hk0_R
    have hmono : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) u_not = true →
        value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) u_not = true := by
      have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
        exact (d.hr0 d.r₀).mpr rfl
      intro hur
      have h0j : value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) u_not = true := by
        rw [← value_agree_inputs d.hL (fun _ => none) hun_live
          (x := oneEachRaw n m d.r₀ j_star) (y := fun w => decide (w = n + j_star.val))
          fun w _ hwu => by
            simp only [oneEachRaw, decide_eq_decide]
            have h1step : reaches (n + m) d.E d.L u_not q :=
              Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
            exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwu).trans
              (h1step.trans (reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL)))), Or.inr⟩]
        exact hur
      exact eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by simp at h)
        (fun j hj hlt _ => ⟨rfl, fun ho => by
          have := (d.hjnot j hj).mp ho; change n + m + j < q at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
        hun_live hun_lt h0j
    cases hu_r : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) u_not with
    | false =>
      refine ⟨?_, rfl⟩
      cases hu_k : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) u_not with
      | false => exact False.elim (hU_ne (hu_k.trans hu_r.symm))
      | true => rfl
    | true =>
      exact False.elim (hU_ne ((hmono hu_r).trans hu_r.symm))
  -- Child avoiding d.f on every gate strictly after d.f reaching u_not
  have hchild_away : ∀ w, reaches (n + m) d.E d.L d.f w → reaches (n + m) d.E d.L w u_not → w ≠ d.f →
      ∃ j ∈ d.L, w = n + m + j ∧
        ∃ u v, u ∈ (gateAt d.E j).inputs ∧ u < n + m + j ∧ reaches (n + m) d.E d.L d.f u ∧
               v ∈ (gateAt d.E j).inputs ∧ v < n + m + j ∧ v ≠ u ∧
               ¬ reaches (n + m) d.E d.L d.f v ∧ ¬ reaches (n + m) d.E d.L v d.f := by
    intro w hfw hwu hwnf
    have hlt_fw : d.f < w := Nat.lt_of_le_of_ne (reaches_le hfw) (Ne.symm hwnf)
    have hlt_wq : w < q := lt_of_le_of_lt (reaches_le hwu) hun_lt
    have hw_live : live (n + m) d.L w :=
      reaches_live (parent_live d.hL d.hj1L d.hf_j1) hfw
    rcases hw_live with low | ⟨j, hjL, rfl⟩
    · have := sd.d_N_le_f; omega
    · have hjne : j ≠ d.j_not := by omega
      obtain ⟨_, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two j hjL hjne
      rcases hfw.cases_tail with h | ⟨u, hfu, ⟨kw, _, hkw, hu_mem, hu_lt⟩⟩
      · exact False.elim (hwnf h)
      · have hkw_eq : kw = j := by omega
        rw [hkw_eq] at hkw hu_mem hu_lt
        have ha_mem : a ∈ (gateAt d.E j).inputs := by rw [hin]; simp
        have hb_mem : b ∈ (gateAt d.E j).inputs := by rw [hin]; simp
        have hv : ∃ v ∈ (gateAt d.E j).inputs, v ≠ u ∧ v < n + m + j := by
          rw [hin] at hu_mem
          rcases List.mem_pair.mp hu_mem with rfl | rfl
          · exact ⟨b, hb_mem, hab.symm, hb_lt⟩
          · exact ⟨a, ha_mem, hab, ha_lt⟩
        obtain ⟨v, hv_mem, hvu, hv_lt⟩ := hv
        have heuw : edgeTo (n + m) d.E d.L u (n + m + j) := ⟨j, hjL, rfl, hu_mem, hu_lt⟩
        have hevw : edgeTo (n + m) d.E d.L v (n + m + j) := ⟨j, hjL, rfl, hv_mem, hv_lt⟩
        have hnvf : ¬ reaches (n + m) d.E d.L v d.f := by
          intro hvf
          have hvnf : v ≠ d.f := by
            intro e; subst e
            rcases d.hf_two j hjL ⟨hv_mem, hv_lt⟩ with rfl | rfl <;>
              rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have hq := hwu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)
              rcases reaches_of_f_ne d hfu (fun eu => hvu eu.symm) with hu1 | hu2
              · have := reaches_le hu1; have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩; omega
              · exact sd.h_miss_not (h2 ▸ (hu2.trans (Relation.ReflTransGen.head heuw hq)))
            · exact sd.h_miss_not (h2 ▸ (hwu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)))
            · exact sd.h_miss_not (h2 ▸ (hwu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)))
            · have hq := hwu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)
              rcases reaches_of_f_ne d hfu (fun eu => hvu eu.symm) with hu1 | hu2
              · exact sd.h_miss_not (h2 ▸ (hu1.trans (Relation.ReflTransGen.head heuw hq)))
              · have := reaches_le hu2; have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩; omega
          rcases hvf.cases_head with rfl | ⟨c, ec, hcf⟩
          · exact hvnf rfl
          · have hcw := d.hsingle v hvnf c (n + m + j) ec hevw
            rw [hcw] at hcf
            have := reaches_le hcf; omega
        have hn_fv : ¬ reaches (n + m) d.E d.L d.f v := by
          intro hfv
          have h_hit_lt : d.f < n + m + sd.j_hit := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
          have hwq : reaches (n + m) d.E d.L (n + m + j) q :=
            hwu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)
          by_cases huv_f : u = d.f ∨ v = d.f
          · rcases huv_f with rfl | rfl
            · rcases d.hf_two j hjL ⟨hu_mem, hu_lt⟩ with rfl | rfl <;>
                rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have h_v_q : reaches (n + m) d.E d.L v q := Relation.ReflTransGen.head hevw hwq
                rcases reaches_of_f_ne d hfv (fun e => by subst e; exact hvu rfl) with hv1 | hv2
                · have : n + m + d.j₁ ≤ v := reaches_le hv1; omega
                · exact sd.h_miss_not (h2 ▸ (hv2.trans h_v_q))
              · exact sd.h_miss_not (h2 ▸ hwq)
              · exact sd.h_miss_not (h2 ▸ hwq)
              · rcases reaches_of_f_ne d hfv (fun e => by subst e; exact hvu rfl) with hv1 | hv2
                · exact sd.h_miss_not (h2 ▸ (hv1.trans (Relation.ReflTransGen.head hevw hwq)))
                · have : n + m + d.j₂ ≤ v := reaches_le hv2; omega
            · rcases d.hf_two j hjL ⟨hv_mem, hv_lt⟩ with rfl | rfl <;>
                rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rcases reaches_of_f_ne d hfu (fun e => by subst e; exact hvu.symm rfl) with hu1 | hu2
                · have : n + m + d.j₁ ≤ u := reaches_le hu1; omega
                · exact sd.h_miss_not (h2 ▸ (hu2.trans (Relation.ReflTransGen.head heuw hwq)))
              · exact sd.h_miss_not (h2 ▸ hwq)
              · exact sd.h_miss_not (h2 ▸ hwq)
              · rcases reaches_of_f_ne d hfu (fun e => by subst e; exact hvu.symm rfl) with hu1 | hu2
                · exact sd.h_miss_not (h2 ▸ (hu1.trans (Relation.ReflTransGen.head heuw hwq)))
                · have : n + m + d.j₂ ≤ u := reaches_le hu2; omega
          · push_neg at huv_f
            have h1_hit : reaches (n + m) d.E d.L (n + m + sd.j_hit) u := by
              rcases reaches_of_f_ne d hfu huv_f.1 with h | h <;>
                rcases sd.hbranches with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact e1 ▸ h
              · exact False.elim (sd.h_miss_not (e2 ▸ (h.trans (Relation.ReflTransGen.head heuw hwq))))
              · exact False.elim (sd.h_miss_not (e2 ▸ (h.trans (Relation.ReflTransGen.head heuw hwq))))
              · exact e1 ▸ h
            have h2_hit : reaches (n + m) d.E d.L (n + m + sd.j_hit) v := by
              rcases reaches_of_f_ne d hfv huv_f.2 with h | h <;>
                rcases sd.hbranches with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact e1 ▸ h
              · exact False.elim (sd.h_miss_not (e2 ▸ (h.trans (Relation.ReflTransGen.head hevw hwq))))
              · exact False.elim (sd.h_miss_not (e2 ▸ (h.trans (Relation.ReflTransGen.head hevw hwq))))
              · exact e1 ▸ h
            have huv := activeReach_last_eq
              (fun a' b' c' hr' _ e1 e2 => d.hsingle a' (fun ea => by
                have := reaches_le (activeReach_to_reaches hr'); omega) b' c' e1 e2)
              (activeReach_of_lt h_hit_lt h1_hit) (activeReach_of_lt h_hit_lt h2_hit)
              (by simp; have := reaches_le h1_hit; omega)
              (by simp; have := reaches_le h2_hit; omega) heuw hevw
            exact hvu huv.symm
        exact ⟨j, hjL, rfl, u, v, hu_mem, hu_lt, hfu, hv_mem, hv_lt, hvu, hn_fv, hnvf⟩
  have h_or_unot : ∀ w, reaches (n + m) d.E d.L d.f w → reaches (n + m) d.E d.L w u_not →
      value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) w = true ∧
      (w ≠ d.f → ∃ j ∈ d.L, w = n + m + j ∧ (gateAt d.E j).op = .or) := by
    have hmain : ∀ dist w, u_not - w = dist →
        reaches (n + m) d.E d.L d.f w → reaches (n + m) d.E d.L w u_not →
        value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) w = true ∧
        (w ≠ d.f → ∃ j ∈ d.L, w = n + m + j ∧ (gateAt d.E j).op = .or) := by
      intro dist
      induction dist using Nat.strong_induction_on with
      | ind dist ih =>
        intro w hdist hfw hwu
        rcases hwu.cases_head with hw_unot | ⟨b, eb, hbu⟩
        · rw [hw_unot] at hfw ⊢
          refine ⟨hU_k0_r0.1, fun hne => ?_⟩
          obtain ⟨j, hjL, hweq, u, v, _, _, _, hv_mem, hv_lt, _, hn_fv, hnvf⟩ :=
            hchild_away u_not hfw Relation.ReflTransGen.refl hne
          have hjne : j ≠ d.j_not := by omega
          obtain ⟨hao, _, _, _, _, _, _⟩ := d.hother_two j hjL hjne
          have hfv_0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) v = false := by
            have hkv : ¬ reaches (n + m) d.E d.L k₀.val v := by
              intro hkv
              rcases reaches_branch_at_f d.hsingle hk0_f hkv with h | h
              · exact hn_fv h
              · exact hnvf h
            have hjv : ¬ reaches (n + m) d.E d.L (n + j_star.val) v := by
              intro hjv
              have hju : reaches (n + m) d.E d.L (n + j_star.val) u_not :=
                hjv.trans (Relation.ReflTransGen.single ⟨j, hjL, hweq, hv_mem, hv_lt⟩)
              have hjf : reaches (n + m) d.E d.L (n + j_star.val) d.f := by
                by_contra hnjf
                exact hj_not_Hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnjf, hju⟩)
              rcases reaches_branch_at_f d.hsingle hjf hjv with h | h
              · exact hn_fv h
              · exact hnvf h
            have h0v := value_agree_inputs d.hL (fun _ => none) (parent_live d.hL hjL ⟨hv_mem, hv_lt⟩)
              (x := oneEachRaw n m k₀ j_star) (y := fun _ => false)
              fun z _ hzv => by
                simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
                exact ⟨fun e => hkv (e ▸ hzv), fun e => hjv (e ▸ hzv)⟩
            rw [h0v]
            exact false_of_no_not_reach d (parent_live d.hL hjL ⟨hv_mem, hv_lt⟩) fun hqv => by
              have := reaches_le hqv; omega
          rcases hao with ha | ho
          · exfalso
            have hv := hU_k0_r0.1
            rw [hweq, val_gate rfl, ha] at hv
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
            have hvt := hv v hv_mem
            rw [if_pos hv_lt, hfv_0] at hvt; cases hvt
          · exact ⟨j, hjL, hweq, ho⟩
        · have hfb := hfw.tail eb
          have hlt_wb := edgeTo_lt eb
          have hle_bu := reaches_le hbu
          obtain ⟨hvb, hb_spec⟩ := ih (u_not - b) (by omega) b rfl hfb hbu
          have hfb_ne : b ≠ d.f := fun eq => by have := reaches_le hfw; omega
          obtain ⟨kb, hkbL, hbeq, hok⟩ := hb_spec hfb_ne
          obtain ⟨jw, hjwL, hwb, hw_mem, hw_lt⟩ := eb
          have hjw_eq : jw = kb := by omega
          rw [hjw_eq] at hjwL hwb hw_mem hw_lt
          have hk_ne : kb ≠ d.j_not := by have := reaches_le hbu; omega
          obtain ⟨_, a, b', hab, hin, ha_lt, hb_lt⟩ := d.hother_two kb hkbL hk_ne
          have hwa : ∃ v' ∈ (gateAt d.E kb).inputs, v' ≠ w ∧ v' < n + m + kb := by
            rw [hin] at hw_mem
            rcases List.mem_pair.mp hw_mem with rfl | rfl
            · exact ⟨b', by rw [hin]; simp, hab.symm, hb_lt⟩
            · exact ⟨a, by rw [hin]; simp, hab, ha_lt⟩
          obtain ⟨v', hv'_mem, hv'w, hv'_lt⟩ := hwa
          have hn_fv' : ¬ reaches (n + m) d.E d.L d.f v' := by
            obtain ⟨kb', _, hkb'_eq, u', v'', hu'_mem, hu'_lt, hfu', hv''_mem, _, hv''u', hn_fv'', _⟩ :=
              hchild_away b hfb hbu hfb_ne
            have hkb_eq : kb' = kb := by omega
            rw [hkb_eq] at hu'_mem hu'_lt
            have heu' : edgeTo (n + m) d.E d.L u' (n + m + kb) := ⟨kb, hkbL, rfl, hu'_mem, hu'_lt⟩
            have hew : edgeTo (n + m) d.E d.L w (n + m + kb) := ⟨kb, hkbL, rfl, hw_mem, hw_lt⟩
            have hu'w : u' = w := by
              by_cases hw_f : w = d.f
              · subst hw_f
                by_contra hu'nf
                have b_q := hbu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)
                rw [hbeq] at b_q
                have hkb_hit : kb = sd.j_hit := by
                  rcases d.hf_two kb hkbL ⟨hw_mem, hw_lt⟩ with rfl | rfl <;>
                    rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact h1.symm
                  · exact False.elim (sd.h_miss_not (h2 ▸ b_q))
                  · exact False.elim (sd.h_miss_not (h2 ▸ b_q))
                  · exact h1.symm
                rcases reaches_of_f_ne d hfu' hu'nf with h | h <;>
                  rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have := reaches_le h; omega
                · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head heu' b_q))))
                · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head heu' b_q))))
                · have := reaches_le h; omega
              · have h_hit_lt := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
                have b_q := hbu.trans (Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩)
                rw [hbeq] at b_q
                have h_hit_w : reaches (n + m) d.E d.L (n + m + sd.j_hit) w := by
                  rcases reaches_of_f_ne d hfw hw_f with h | h <;>
                    rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact h1 ▸ h
                  · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head hew b_q))))
                  · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head hew b_q))))
                  · exact h1 ▸ h
                by_cases hu'f : u' = d.f
                · subst hu'f
                  rcases d.hf_two kb hkbL ⟨hu'_mem, hu'_lt⟩ with rfl | rfl <;>
                    rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · have := reaches_le h_hit_w; omega
                  · exact False.elim (sd.h_miss_not (h2 ▸ b_q))
                  · exact False.elim (sd.h_miss_not (h2 ▸ b_q))
                  · have := reaches_le h_hit_w; omega
                · have h_hit_u' : reaches (n + m) d.E d.L (n + m + sd.j_hit) u' := by
                    rcases reaches_of_f_ne d hfu' hu'f with h | h <;>
                      rcases sd.hbranches with ⟨h1, h2⟩ | ⟨h1, h2⟩
                    · exact h1 ▸ h
                    · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head heu' b_q))))
                    · exact False.elim (sd.h_miss_not (h2 ▸ (h.trans (Relation.ReflTransGen.head heu' b_q))))
                    · exact h1 ▸ h
                  exact activeReach_last_eq
                    (fun a' b' c' hr' _ e1 e2 => d.hsingle a' (fun ea => by
                      have := reaches_le (activeReach_to_reaches hr'); omega) b' c' e1 e2)
                    (activeReach_of_lt h_hit_lt h_hit_u') (activeReach_of_lt h_hit_lt h_hit_w)
                    (by simp; have := reaches_le h_hit_u'; omega)
                    (by simp; have := reaches_le h_hit_w; omega) heu' hew
            have hv'_eq : v' = v'' := by
              rw [hin] at hv'_mem hw_mem
              have hkb_eq' : kb' = kb := by omega
              rw [hkb_eq', hin] at hv''_mem
              rcases List.mem_pair.mp hv'_mem with ev' | ev' <;>
                rcases List.mem_pair.mp hv''_mem with ev'' | ev'' <;>
                rcases List.mem_pair.mp hw_mem with ew | ew
              all_goals first
                | exact ev'.trans ev''.symm
                | exact False.elim (hv'w (ev'.trans ew.symm))
                | exact False.elim (hv''u' (ev''.trans (ew.symm.trans hu'w.symm)))
            subst v'; exact hn_fv''
          have hnw_f : ¬ reaches (n + m) d.E d.L v' d.f := by
            intro hvf
            have hv'nf : v' ≠ d.f := fun e => hn_fv' (e ▸ Relation.ReflTransGen.refl)
            rcases hvf.cases_head with rfl | ⟨c, ec, hcf⟩
            · exact hv'nf rfl
            · rw [d.hsingle v' hv'nf c (n + m + kb) ec ⟨kb, hkbL, rfl, hv'_mem, hv'_lt⟩] at hcf
              have := reaches_le hcf; have := reaches_le hfw; omega
          have hfv'_0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) v' = false := by
            have hkv : ¬ reaches (n + m) d.E d.L k₀.val v' := by
              intro hkv
              rcases reaches_branch_at_f d.hsingle hk0_f hkv with h | h
              · exact hn_fv' h
              · exact hnw_f h
            have hjv : ¬ reaches (n + m) d.E d.L (n + j_star.val) v' := by
              intro hjv
              have hju : reaches (n + m) d.E d.L (n + j_star.val) u_not :=
                hjv.trans ((Relation.ReflTransGen.single ⟨kb, hkbL, rfl, hv'_mem, hv'_lt⟩).trans (hbeq ▸ hbu))
              have hjf : reaches (n + m) d.E d.L (n + j_star.val) d.f := by
                by_contra hnjf
                exact hj_not_Hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnjf, hju⟩)
              rcases reaches_branch_at_f d.hsingle hjf hjv with h | h
              · exact hn_fv' h
              · exact hnw_f h
            have h0v := value_agree_inputs d.hL (fun _ => none) (parent_live d.hL hkbL ⟨hv'_mem, hv'_lt⟩)
              (x := oneEachRaw n m k₀ j_star) (y := fun _ => false)
              fun z _ hzv => by
                simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
                exact ⟨fun e => hkv (e ▸ hzv), fun e => hjv (e ▸ hzv)⟩
            rw [h0v]
            exact false_of_no_not_reach d (parent_live d.hL hkbL ⟨hv'_mem, hv'_lt⟩) fun hqv => by
              have := reaches_le hqv; have := reaches_le hbu; omega
          have hw_val : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) w = true := by
            rw [hbeq, val_gate rfl, hok] at hvb
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hvb
            obtain ⟨z, hz_mem, hzv⟩ := hvb
            rw [hin] at hw_mem hv'_mem hz_mem
            have hzwv : z = w ∨ z = v' := by
              rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hw_mem with ew | ew <;>
                rcases List.mem_pair.mp hv'_mem with ev | ev
              all_goals first
                | exact Or.inl ew.symm
                | exact Or.inr ev.symm
                | exact False.elim (hv'w (ev.trans ew.symm))
            rcases hzwv with rfl | rfl
            · rw [if_pos hw_lt] at hzv; exact hzv
            · rw [if_pos hv'_lt, hfv'_0] at hzv; cases hzv
          refine ⟨hw_val, fun hne => ?_⟩
          obtain ⟨j, hjL, hweq, u, v, _, _, _, hv_mem, hv_lt, _, hn_fv, hnvf⟩ :=
            hchild_away w hfw hwu hne
          subst hweq
          have hjne : j ≠ d.j_not := by omega
          obtain ⟨hao, _, _, _, _, _, _⟩ := d.hother_two j hjL hjne
          have hfv_0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) v = false := by
            have hkv : ¬ reaches (n + m) d.E d.L k₀.val v := by
              intro hkv
              rcases reaches_branch_at_f d.hsingle hk0_f hkv with h | h
              · exact hn_fv h
              · exact hnvf h
            have hjv : ¬ reaches (n + m) d.E d.L (n + j_star.val) v := by
              intro hjv
              have hju : reaches (n + m) d.E d.L (n + j_star.val) u_not :=
                hjv.trans ((Relation.ReflTransGen.single ⟨j, hjL, rfl, hv_mem, hv_lt⟩).trans hwu)
              have hjf : reaches (n + m) d.E d.L (n + j_star.val) d.f := by
                by_contra hnjf
                exact hj_not_Hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnjf, hju⟩)
              rcases reaches_branch_at_f d.hsingle hjf hjv with h | h
              · exact hn_fv h
              · exact hnvf h
            have h0v := value_agree_inputs d.hL (fun _ => none) (parent_live d.hL hjL ⟨hv_mem, hv_lt⟩)
              (x := oneEachRaw n m k₀ j_star) (y := fun _ => false)
              fun z _ hzv => by
                simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
                exact ⟨fun e => hkv (e ▸ hzv), fun e => hjv (e ▸ hzv)⟩
            rw [h0v]
            exact false_of_no_not_reach d (parent_live d.hL hjL ⟨hv_mem, hv_lt⟩) fun hqv => by
              have := reaches_le hqv; have := reaches_le hwu; omega
          rcases hao with ha | ho
          · exfalso
            rw [val_gate rfl, ha] at hw_val
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hw_val
            have hvt := hw_val v hv_mem
            rw [if_pos hv_lt, hfv_0] at hvt; cases hvt
          · exact ⟨j, hjL, rfl, ho⟩
    exact fun w hfw hwu => hmain (u_not - w) w rfl hfw hwu
  let U (x : ℕ → Bool) := value (n + m) d.E x (fun _ => none) u_not
  let U_side (x : ℕ → Bool) := value (n + m) d.E x (relay d.f false) u_not
  have hU_decomp : ∀ x w, live (n + m) d.L w → reaches (n + m) d.E d.L d.f w → reaches (n + m) d.E d.L w u_not →
      value (n + m) d.E x (fun _ => none) w =
        (value (n + m) d.E x (fun _ => none) d.f || value (n + m) d.E x (relay d.f false) w) := by
    intro x w hw hfw hwu
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hwf : w = d.f
      · subst hwf
        rw [val_relay_at sd.d_N_le_f, Bool.or_false]
      · obtain ⟨j, hjL, hweq, ho⟩ := (h_or_unot w hfw hwu).2 hwf
        obtain ⟨j', _, hweq2, u, v, hu_mem, hu_lt, hfu, hv_mem, hv_lt, hvu, hn_fv, _⟩ :=
          hchild_away w hfw hwu hwf
        have hjj : j' = j := by rw [hweq] at hweq2; omega
        subst hjj
        subst hweq
        have hjq_lt : j' ≠ d.j_not := by have := reaches_le hwu; omega
        obtain ⟨_, a, b, hab, hin, ha_lt, hb_lt⟩ := d.hother_two j' hjL hjq_lt
        have hu_u : reaches (n + m) d.E d.L u u_not :=
          Relation.ReflTransGen.head ⟨j', hjL, rfl, hu_mem, hu_lt⟩ hwu
        have ihu := ih u hu_lt (parent_live d.hL hjL ⟨hu_mem, hu_lt⟩) hfu hu_u
        have hveq : value (n + m) d.E x (relay d.f false) v = value (n + m) d.E x (fun _ => none) v :=
          value_agree_of_fix_away d.hL (parent_live d.hL hjL ⟨hv_mem, hv_lt⟩) fun z _ hdiff hr => by
            by_cases hzf : z = d.f
            · subst hzf; exact hn_fv hr
            · exfalso; apply hdiff; simp [relay, hzf]
        have hf_ne_j : relay d.f false (n + m + j') = none := by simp [relay, hwf]
        rw [val_gate rfl, val_gate hf_ne_j, ho]
        simp only [GateOp.eval]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        have hu_mem0 := hu_mem
        have hv_mem0 := hv_mem
        constructor
        · rintro ⟨z, hz_mem, hzv⟩
          have hmem_z := hz_mem
          rw [hin] at hu_mem hv_mem hz_mem
          have hzwv : z = u ∨ z = v := by
            rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
              rcases List.mem_pair.mp hu_mem with eu | eu <;>
              rcases List.mem_pair.mp hv_mem with ev | ev
            all_goals first
              | exact Or.inl eu.symm
              | exact Or.inr ev.symm
              | exact False.elim (hvu (ev.trans eu.symm))
          rcases hzwv with hzu | hzv_eq
          · rw [hzu] at hzv
            rw [if_pos hu_lt, ihu, Bool.or_eq_true] at hzv
            rcases hzv with hf | hUs
            · exact Or.inl hf
            · right; refine ⟨u, hu_mem0, by rw [if_pos hu_lt]; exact hUs⟩
          · rw [hzv_eq] at hzv
            right; refine ⟨v, hv_mem0, by rw [if_pos hv_lt, hveq]; rw [if_pos hv_lt] at hzv; exact hzv⟩
        · rintro (hf | ⟨z, hz_mem, hzv⟩)
          · refine ⟨u, hu_mem0, ?_⟩
            rw [if_pos hu_lt, ihu, Bool.or_eq_true]; exact Or.inl hf
          · rw [hin] at hu_mem hv_mem hz_mem
            have hzwv : z = u ∨ z = v := by
              rcases List.mem_pair.mp hz_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hu_mem with eu | eu <;>
                rcases List.mem_pair.mp hv_mem with ev | ev
              all_goals first
                | exact Or.inl eu.symm
                | exact Or.inr ev.symm
                | exact False.elim (hvu (ev.trans eu.symm))
            rcases hzwv with hzu | hzv_eq
            · refine ⟨u, hu_mem0, ?_⟩
              rw [if_pos hu_lt, ihu, Bool.or_eq_true]; right; rw [hzu, if_pos hu_lt] at hzv; exact hzv
            · refine ⟨v, hv_mem0, ?_⟩
              rw [if_pos hv_lt, ← hveq]; rw [hzv_eq, if_pos hv_lt] at hzv; exact hzv
  have hU_eq (x : ℕ → Bool) : U x = (value (n + m) d.E x (fun _ => none) d.f || U_side x) :=
    hU_decomp x u_not hun_live hf_unot Relation.ReflTransGen.refl
  -- Show H_r.Nonempty ∨ H_c.Nonempty from the non-f child of u_not
  have hnonempty : H_r.Nonempty ∨ H_c.Nonempty := by
    obtain ⟨j, hjL, heq, _, v, _, _, _, hv_mem, hv_lt, _, hn_fv, hnvf⟩ :=
      hchild_away u_not hf_unot Relation.ReflTransGen.refl hun_ne
    have hv_live := parent_live d.hL hjL ⟨hv_mem, hv_lt⟩
    obtain ⟨v₀, hv₀N, hv₀v⟩ := gate_has_input_path d hv_live
    have hv₀_unot : reaches (n + m) d.E d.L v₀ u_not :=
      hv₀v.trans (Relation.ReflTransGen.single ⟨j, hjL, heq, hv_mem, hv_lt⟩)
    have hv₀_nf : ¬ reaches (n + m) d.E d.L v₀ d.f := by
      intro hv₀f
      rcases reaches_branch_at_f d.hsingle hv₀f hv₀v with h | h
      · exact hn_fv h
      · exact hnvf h
    by_cases hvn : v₀ < n
    · left; refine ⟨⟨v₀, hvn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀_nf, hv₀_unot⟩⟩
    · right; refine ⟨⟨v₀ - n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Nat.add_sub_cancel' (Nat.not_lt.mp hvn)] using hv₀_nf, by simpa [Nat.add_sub_cancel' (Nat.not_lt.mp hvn)] using hv₀_unot⟩⟩
  have hU_side_mono : ∀ x y : ℕ → Bool, (∀ v < n + m, x v = true → y v = true) →
      U_side x = true → U_side y = true :=
    fun x y hxy => eval_mono_bound d.hL d.hFan
      (fun j _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
      (fun j hj hlt hnone => ⟨hnone, fun ho => by
        have := (d.hjnot j hj).mp ho; change n + m + j < q at hlt; omega⟩)
      hxy hun_live hun_lt
  have h_not_Hr : ∀ r_h ∈ H_r, False := by
    intro r_h hmem_Hr
    have hmem := hmem_Hr
    simp only [H_r, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hrq : reaches (n + m) d.E d.L r_h.val q :=
      Relation.ReflTransGen.tail hmem.2 ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
    have haway_q : ¬ activeReach (n + m) d.E d.L (some q) r_h.val (n + m + d.r) :=
      activeReach_skip_contra d.hsingle hmem.1 hrq hq_lt_R
    have hB_eq : ∀ b j, value (n + m) d.E (oneEachRaw n m r_h j) (relay q b) (n + m + d.r) =
        value (n + m) d.E (oneEachRaw n m d.r₀ j) (relay q b) (n + m + d.r) := by
      intro b j
      have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
        exact (d.hr0 d.r₀).mpr rfl
      have h1 := eval_unchanged_of_not_active d.hL q (by omega) (relay q b) ⟨b, by dsimp only [relay]; rw [if_pos rfl]⟩
        (v := r_h.val) (x := oneEachRaw n m r_h j) (y := fun w => decide (w = n + j.val))
        (fun w _ hwr => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwr, Or.inr⟩)
        (Or.inr ⟨d.r, d.hrL, rfl⟩) haway_q
      have h2 := value_agree_inputs d.hL (relay q b) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
        fun w _ hwr => by
          simp only [oneEachRaw, decide_eq_decide]
          exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
      exact h1.trans h2.symm
    cases hsr : U_side (fun w => decide (w = r_h.val)) with
    | true =>
      have hall0 : ∀ j : Fin m, A r_h j = false := by
        intro j
        have hUs : U_side (oneEachRaw n m r_h j) = true :=
          hU_side_mono _ _ (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw) hsr
        have hU1 : U (oneEachRaw n m r_h j) = true := by rw [hU_eq, hUs, Bool.or_true]
        have hq0 : value (n + m) d.E (oneEachRaw n m r_h j) (fun _ => none) q = false := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU1
        rw [← d.hRep r_h j, value_subst_relay d.hL q (by omega) false hq0 (Or.inr ⟨d.r, d.hrL, rfl⟩),
          hB_eq false j, B_r0_false hg d sd j]
      obtain ⟨j, hj⟩ := (no_empty_or_full_row hg.2.2.1 r_h).1
      rw [hall0 j] at hj; cases hj
    | false =>
      have hr_eq : ∀ j : Fin m, A r_h j = A d.r₀ j := by
        intro j
        apply Bool.eq_iff_iff.mpr
        refine ⟨hr_sub r_h hmem_Hr j, fun hr0j => ?_⟩
        have hz_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
          rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
          exact (d.hr0 d.r₀).mpr rfl
        have hU_r0_false : U (oneEachRaw n m d.r₀ j) = false := by
          by_contra hU1
          have hUt := Bool.eq_true_of_not_eq_false hU1
          have hq0 : value (n + m) d.E (oneEachRaw n m d.r₀ j) (fun _ => none) q = false := by
            rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
            simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
            exact congrArg Bool.not hUt
          rw [← d.hRep d.r₀ j, value_subst_relay d.hL q (by omega) false hq0 (Or.inr ⟨d.r, d.hrL, rfl⟩),
            B_r0_false hg d sd j] at hr0j
          cases hr0j
        have hf_0j : value (n + m) d.E (fun w => decide (w = n + j.val)) (fun _ => none) d.f = false := by
          have := value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
            (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
            fun w _ hwf => by
              simp only [oneEachRaw, decide_eq_decide]
              exact ⟨fun h => h.resolve_left (fun e => hz_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩
          rw [← this]
          by_contra hft
          have := Bool.eq_true_of_not_eq_false hft
          rw [hU_eq, this, Bool.true_or] at hU_r0_false; cases hU_r0_false
        have hUs_0j : U_side (fun w => decide (w = n + j.val)) = false := by
          have := value_agree_inputs d.hL (fun _ => none) hun_live
            (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
            fun w _ hwu => by
              simp only [oneEachRaw, decide_eq_decide]
              have h1step : reaches (n + m) d.E d.L u_not q :=
                Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
              exact ⟨fun h => h.resolve_left (fun e => hz_away ((e ▸ hwu).trans
                (h1step.trans (reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL)))), Or.inr⟩
          change U (oneEachRaw n m d.r₀ j) = U (fun w => decide (w = n + j.val)) at this
          rw [hU_r0_false] at this
          by_contra hust
          have h1 := Bool.eq_true_of_not_eq_false hust
          rw [hU_eq, h1, Bool.or_true] at this; cases this
        have hf_rhj : value (n + m) d.E (oneEachRaw n m r_h j) (fun _ => none) d.f = false := by
          rw [← hf_0j]
          exact value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
            (x := oneEachRaw n m r_h j) (y := fun w => decide (w = n + j.val))
            fun w _ hwf => by
              simp only [oneEachRaw, decide_eq_decide]
              exact ⟨fun h => h.resolve_left (fun e => hmem.1 (e ▸ hwf)), Or.inr⟩
        have hUs_rhj : U_side (oneEachRaw n m r_h j) = false := by
          by_contra h1
          have hUs_t := Bool.eq_true_of_not_eq_false h1
          have h_act : activeReach (n + m) d.E d.L (some d.f) (n + j.val) u_not := by
            by_contra hna
            have heq := eval_unchanged_of_not_active d.hL d.f sd.d_N_le_f (relay d.f false)
              ⟨false, by dsimp only [relay]; rw [if_pos rfl]⟩
              (v := n + j.val) (x := oneEachRaw n m r_h j) (y := fun w => decide (w = r_h.val))
              (fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hw, Or.inl⟩)
              hun_live hna
            change U_side (oneEachRaw n m r_h j) = U_side (fun w => decide (w = r_h.val)) at heq
            rw [hUs_t, hsr] at heq; cases heq
          have hj_nf : ¬ reaches (n + m) d.E d.L (n + j.val) d.f :=
            fun hjf => activeReach_skip_f_lt (fun a ha => d.hsingle a ha) hf_lt_unot hjf h_act
          have hj_Hc : j ∈ H_c := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hj_nf, activeReach_to_reaches h_act⟩
          have hc := hc_sub j hj_Hc d.r₀ hr0j
          rw [hA00] at hc; cases hc
        have hU_rhj : U (oneEachRaw n m r_h j) = false := by
          rw [hU_eq, hf_rhj, hUs_rhj]; rfl
        have hq_rhj : value (n + m) d.E (oneEachRaw n m r_h j) (fun _ => none) q = true := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU_rhj
        have hq_r0j : value (n + m) d.E (oneEachRaw n m d.r₀ j) (fun _ => none) q = true := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU_r0_false
        rw [← d.hRep r_h j, value_subst_relay d.hL q (by omega) true hq_rhj (Or.inr ⟨d.r, d.hrL, rfl⟩), hB_eq true j]
        rw [← value_subst_relay d.hL q (by omega) true hq_r0j (Or.inr ⟨d.r, d.hrL, rfl⟩)]
        rw [d.hRep d.r₀ j]; exact hr0j
      have hr_ne : r_h ≠ d.r₀ := by
        intro e; subst e
        have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
          rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
          exact (d.hr0 d.r₀).mpr rfl
        exact hr0_away ((Relation.ReflTransGen.tail hmem.2 ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩).trans
          (reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL))
      exact hr_ne (hg.1 (funext hr_eq))
  have h_not_Hc : ∀ c_h ∈ H_c, False := by
    intro c_h hmem_Hc
    have hmem := hmem_Hc
    simp only [H_c, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hcq : reaches (n + m) d.E d.L (n + c_h.val) q :=
      Relation.ReflTransGen.tail hmem.2 ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
    have haway_q : ¬ activeReach (n + m) d.E d.L (some q) (n + c_h.val) (n + m + d.r) :=
      activeReach_skip_contra d.hsingle hmem.1 hcq hq_lt_R
    have hB_eq : ∀ b i, value (n + m) d.E (oneEachRaw n m i c_h) (relay q b) (n + m + d.r) =
        value (n + m) d.E (oneEachRaw n m i d.c₀) (relay q b) (n + m + d.r) := by
      intro b i
      have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
        rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
        exact (d.hc0 d.c₀).mpr rfl
      have h1 := eval_unchanged_of_not_active d.hL q (by omega) (relay q b) ⟨b, by dsimp only [relay]; rw [if_pos rfl]⟩
        (v := n + c_h.val) (x := oneEachRaw n m i c_h) (y := fun w => decide (w = i.val))
        (fun w _ hwc => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwc, Or.inl⟩)
        (Or.inr ⟨d.r, d.hrL, rfl⟩) haway_q
      have h2 := value_agree_inputs d.hL (relay q b) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
        fun w _ hwc => by
          simp only [oneEachRaw, decide_eq_decide]
          exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hwc)), Or.inl⟩
      exact h1.trans h2.symm
    cases hsc : U_side (fun w => decide (w = n + c_h.val)) with
    | true =>
      have hall0 : ∀ i : Fin n, A i c_h = false := by
        intro i
        have hUs : U_side (oneEachRaw n m i c_h) = true :=
          hU_side_mono _ _ (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw) hsc
        have hU1 : U (oneEachRaw n m i c_h) = true := by rw [hU_eq, hUs, Bool.or_true]
        have hq0 : value (n + m) d.E (oneEachRaw n m i c_h) (fun _ => none) q = false := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU1
        rw [← d.hRep i c_h, value_subst_relay d.hL q (by omega) false hq0 (Or.inr ⟨d.r, d.hrL, rfl⟩),
          hB_eq false i, B_c0_false hg d sd i]
      obtain ⟨i, hi⟩ := (no_empty_or_full_col hg.2.2.2.1 c_h).1
      rw [hall0 i] at hi; cases hi
    | false =>
      have hc_eq : ∀ i : Fin n, A i c_h = A i d.c₀ := by
        intro i
        apply Bool.eq_iff_iff.mpr
        refine ⟨hc_sub c_h hmem_Hc i, fun hic0 => ?_⟩
        have hz_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
          rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
          exact (d.hc0 d.c₀).mpr rfl
        have hU_ic0_false : U (oneEachRaw n m i d.c₀) = false := by
          by_contra hU1
          have hUt := Bool.eq_true_of_not_eq_false hU1
          have hq0 : value (n + m) d.E (oneEachRaw n m i d.c₀) (fun _ => none) q = false := by
            rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
            simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
            exact congrArg Bool.not hUt
          rw [← d.hRep i d.c₀, value_subst_relay d.hL q (by omega) false hq0 (Or.inr ⟨d.r, d.hrL, rfl⟩),
            B_c0_false hg d sd i] at hic0
          cases hic0
        have hf_i0 : value (n + m) d.E (fun w => decide (w = i.val)) (fun _ => none) d.f = false := by
          have := value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
            (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
            fun w _ hwf => by
              simp only [oneEachRaw, decide_eq_decide]
              exact ⟨fun h => h.resolve_right (fun e => hz_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inl⟩
          rw [← this]
          by_contra hft
          have := Bool.eq_true_of_not_eq_false hft
          rw [hU_eq, this, Bool.true_or] at hU_ic0_false; cases hU_ic0_false
        have hUs_i0 : U_side (fun w => decide (w = i.val)) = false := by
          have := value_agree_inputs d.hL (fun _ => none) hun_live
            (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
            fun w _ hwu => by
              simp only [oneEachRaw, decide_eq_decide]
              have h1step : reaches (n + m) d.E d.L u_not q :=
                Relation.ReflTransGen.single ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩
              exact ⟨fun h => h.resolve_right (fun e => hz_away ((e ▸ hwu).trans
                (h1step.trans (reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL)))), Or.inl⟩
          change U (oneEachRaw n m i d.c₀) = U (fun w => decide (w = i.val)) at this
          rw [hU_ic0_false] at this
          by_contra hust
          have h1 := Bool.eq_true_of_not_eq_false hust
          rw [hU_eq, h1, Bool.or_true] at this; cases this
        have hf_ich : value (n + m) d.E (oneEachRaw n m i c_h) (fun _ => none) d.f = false := by
          rw [← hf_i0]
          exact value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
            (x := oneEachRaw n m i c_h) (y := fun w => decide (w = i.val))
            fun w _ hwf => by
              simp only [oneEachRaw, decide_eq_decide]
              exact ⟨fun h => h.resolve_right (fun e => hmem.1 (e ▸ hwf)), Or.inl⟩
        have hUs_ich : U_side (oneEachRaw n m i c_h) = false := by
          by_contra h1
          have hUs_t := Bool.eq_true_of_not_eq_false h1
          have h_act : activeReach (n + m) d.E d.L (some d.f) i.val u_not := by
            by_contra hna
            have heq := eval_unchanged_of_not_active d.hL d.f sd.d_N_le_f (relay d.f false)
              ⟨false, by dsimp only [relay]; rw [if_pos rfl]⟩
              (v := i.val) (x := oneEachRaw n m i c_h) (y := fun w => decide (w = n + c_h.val))
              (fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hw, Or.inr⟩)
              hun_live hna
            change U_side (oneEachRaw n m i c_h) = U_side (fun w => decide (w = n + c_h.val)) at heq
            rw [hUs_t, hsc] at heq; cases heq
          have hi_nf : ¬ reaches (n + m) d.E d.L i.val d.f :=
            fun hif => activeReach_skip_f_lt (fun a ha => d.hsingle a ha) hf_lt_unot hif h_act
          have hi_Hr : i ∈ H_r := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hi_nf, activeReach_to_reaches h_act⟩
          exact h_not_Hr i hi_Hr
        have hU_ich : U (oneEachRaw n m i c_h) = false := by
          rw [hU_eq, hf_ich, hUs_ich]; rfl
        have hq_ich : value (n + m) d.E (oneEachRaw n m i c_h) (fun _ => none) q = true := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU_ich
        have hq_ic0 : value (n + m) d.E (oneEachRaw n m i d.c₀) (fun _ => none) q = true := by
          rw [val_gate rfl, (d.hjnot d.j_not d.hjnotL).mpr rfl, hun]
          simp only [GateOp.eval, List.map, hun_lt', ↓reduceIte, List.headD]
          exact congrArg Bool.not hU_ic0_false
        rw [← d.hRep i c_h, value_subst_relay d.hL q (by omega) true hq_ich (Or.inr ⟨d.r, d.hrL, rfl⟩), hB_eq true i]
        rw [← value_subst_relay d.hL q (by omega) true hq_ic0 (Or.inr ⟨d.r, d.hrL, rfl⟩)]
        rw [d.hRep i d.c₀]; exact hic0
      have hc_ne : c_h ≠ d.c₀ := by
        intro e; subst e
        have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
          rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
          exact (d.hc0 d.c₀).mpr rfl
        exact hc0_away ((Relation.ReflTransGen.tail hmem.2 ⟨d.j_not, d.hjnotL, rfl, hun_mem', hun_lt'⟩).trans
          (reaches_root_of_closed d.hL d.huse d.j_not d.hjnotL))
      exact hc_ne (hg.2.1 (funext hc_eq))
  rcases hnonempty with ⟨r_h, hr⟩ | ⟨c_h, hc⟩
  · exact h_not_Hr r_h hr
  · exact h_not_Hc c_h hc

def fixBranch {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (bf bn : Bool) (w : ℕ) : Option Bool :=
  if w = d.f then some bf else if w = n + m + d.j_not then some bn else none

def evalT {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (bf bn : Bool) (x : ℕ → Bool) : Bool :=
  value (n + m) d.E x (fixBranch d bf bn) (n + m + d.r)

theorem evalT_mono {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (sd : SplitData n m A d) {bf₀ bf₁ bn₀ bn₁ : Bool}
    (hbf : bf₀ = true → bf₁ = true) (hbn : bn₀ = true → bn₁ = true)
    {x y : ℕ → Bool} (hxy : ∀ v < n + m, x v = true → y v = true) :
    evalT d bf₀ bn₀ x = true → evalT d bf₁ bn₁ y = true := by
  have hne : n + m + d.j_not ≠ d.f := by
    have := edgeTo_lt ⟨sd.j_hit, sd.h_hit_L, rfl, sd.h_hit_f⟩
    have := reaches_le sd.h_hit_not
    omega
  exact eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d bf₀ bn₀) (fix₁ := fixBranch d bf₁ bn₁)
    (fun j _ _ b₀ hb₀ => by
      dsimp only [fixBranch] at hb₀ ⊢
      by_cases h1 : n + m + j = d.f
      · rw [if_pos h1] at hb₀ ⊢; cases hb₀; exact ⟨bf₁, rfl, hbf⟩
      · by_cases h2 : n + m + j = n + m + d.j_not
        · rw [if_neg h1, if_pos h2] at hb₀ ⊢; cases hb₀; exact ⟨bn₁, rfl, hbn⟩
        · rw [if_neg h1, if_neg h2] at hb₀; cases hb₀)
    (fun j hj _ hnone => by
      dsimp only [fixBranch] at hnone ⊢
      by_cases h1 : n + m + j = d.f
      · rw [if_pos h1] at hnone; cases hnone
      · by_cases h2 : n + m + j = n + m + d.j_not
        · rw [if_neg h1, if_pos h2] at hnone; cases hnone
        · rw [if_neg h1, if_neg h2] at hnone ⊢
          exact ⟨rfl, fun ho => h2 (by rw [(d.hjnot j hj).mp ho])⟩)
    hxy (Or.inr ⟨d.r, d.hrL, rfl⟩) (Nat.lt_succ_self _)

theorem evalT_eq_eval {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (sd : SplitData n m A d) (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) (x : ℕ → Bool) :
    evalT d (value (n + m) d.E x (fun _ => none) d.f)
      (!(value (n + m) d.E x (fun _ => none) d.f)) x =
      value (n + m) d.E x (fun _ => none) (n + m + d.r) := by
  let q := n + m + d.j_not
  let fv := value (n + m) d.E x (fun _ => none) d.f
  have hfq : d.f < q := jnot_input_lt d hf_not
  have hfq' : d.f < n + m + d.j_not := hfq
  have hqR : q < n + m + d.r := by
    have := reaches_le sd.h_not_J
    have := reaches_le sd.h_J_root
    have := sd.h_not_ne_J
    omega
  have hc1 := cut_agree d.hL d.f d.hsingle x x (fun _ => none) (relay d.f fv)
    (fun _ _ _ => rfl) (fun w _ hwf => by dsimp only [relay]; rw [if_neg hwf])
    (by rw [val_relay_at sd.d_N_le_f]) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    (Or.inr fun hr => by
      have := reaches_le (f_reaches_root d)
      have := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
      have := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
      have := reaches_le hr
      omega)
  have hq_val : value (n + m) d.E x (relay d.f fv) q = !fv := by
    have hqf : relay d.f fv q = none := by dsimp only [relay]; rw [if_neg (Nat.ne_of_gt hfq)]
    rw [val_gate hqf, (d.hjnot d.j_not d.hjnotL).mpr rfl, hf_not]
    simp only [GateOp.eval, List.map, hfq', ↓reduceIte, List.headD]
    rw [val_relay_at sd.d_N_le_f]
  have hc2 := value_subst_node d.hL q (x := x) (fix₁ := relay d.f fv) (fix₂ := fixBranch d fv (!fv))
    (fun w hwq => by
      dsimp only [relay, fixBranch]
      by_cases hwf : w = d.f
      · rw [if_pos hwf, if_pos hwf]
      · rw [if_neg hwf, if_neg hwf, if_neg hwq])
    (by
      have hfq_ne : q ≠ d.f := Nat.ne_of_gt hfq
      have hfbq : fixBranch d fv (!fv) q = some (!fv) := by
        dsimp only [fixBranch]; rw [if_neg hfq_ne, if_pos rfl]
      rw [hq_val, val_fixed (by omega) hfbq])
    (Or.inr ⟨d.r, d.hrL, rfl⟩)
  exact (hc1.trans hc2).symm

theorem T_000_false {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (sd : SplitData n m A d) :
    evalT d false false (fun _ => false) = false := by
  have hmain : ∀ w, live (n + m) d.L w → value (n + m) d.E (fun _ => false) (fixBranch d false false) w = false := by
    intro w hw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases hw with low | ⟨j, hj, rfl⟩
      · exact val_raw low
      · cases hfx : fixBranch d false false (n + m + j) with
        | some b =>
          have : b = false := by simp only [fixBranch] at hfx; split_ifs at hfx <;> cases hfx <;> rfl
          subst this; exact val_fixed (by omega) hfx
        | none =>
          have hjne : j ≠ d.j_not := by
            intro e; subst e; simp only [fixBranch] at hfx; split_ifs at hfx <;> cases hfx
          obtain ⟨hao, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j hj hjne
          have ha_f := ih a ha_lt (parent_live d.hL hj ⟨by rw [hin]; simp, ha_lt⟩)
          have hb_f := ih b hb_lt (parent_live d.hL hj ⟨by rw [hin]; simp, hb_lt⟩)
          rw [val_gate hfx, hin]
          simp only [List.map, ha_lt, hb_lt, ↓reduceIte, ha_f, hb_f]
          rcases hao with h' | h' <;> simp [h', GateOp.eval]
  exact hmain (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩)

theorem T_010_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hA00 : A d.r₀ d.c₀ = false) (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) :
    evalT d false true (fun _ => false) = false := by
  have hfq := jnot_input_lt d hf_not
  have hf0 : value (n + m) d.E (fun _ => false) (fun _ => none) d.f = false :=
    false_of_no_not_reach d (parent_live d.hL d.hj1L d.hf_j1) fun hr => by
      have := reaches_le hr; omega
  have hev := evalT_eq_eval d sd hf_not (fun _ => false)
  rw [hf0, Bool.not_false] at hev
  rw [hev]
  have h0_agree : value (n + m) d.E (oneEachRaw n m d.r₀ d.c₀) (fun _ => none) (n + m + d.r) =
      value (n + m) d.E (fun _ => false) (fun _ => none) (n + m + d.r) := by
    apply value_agree_of_reaches d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) Relation.ReflTransGen.refl
    intro w hw hwr
    have hw_used := (reaches_root_iff_used d.hrL d.hL d.huse hw).mp hwr
    simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
    exact ⟨fun e => (d.hr0 d.r₀).mpr rfl (e ▸ hw_used), fun e => (d.hc0 d.c₀).mpr rfl (e ▸ hw_used)⟩
  rw [← h0_agree, d.hRep]; exact hA00

theorem T_100_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) :
    evalT d true false (fun _ => false) = false := by
  have hfq : d.f < n + m + d.j_not := jnot_input_lt d hf_not
  obtain ⟨k₀, hk₀⟩ := hg.2.2.1 d.r₀
  have hk0_f : reaches (n + m) d.E d.L k₀.val d.f := by
    by_contra hnf
    have hsp := single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := k₀.val) (by have := k₀.isLt; omega)
      (fun a b c hr _ e1 e2 => d.hsingle a (fun ha => by
        rw [activeReach_none_iff] at hr; exact hnf (ha ▸ hr)) b c e1 e2)
      (Or.inr ⟨d.r, d.hrL, rfl⟩)
    exact contradict_IncR_of_unate hg d hk₀ hsp
  obtain ⟨j_star, hj_r0, hj_k0⟩ : ∃ j : Fin m, A d.r₀ j = true ∧ A k₀ j = false := by
    by_contra hnone
    apply hk₀; left; intro j hj; by_contra hc; exact hnone ⟨j, hj, Bool.eq_false_iff.mpr hc⟩
  have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  have hf_k0 : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f = true := by
    by_contra hkf
    have hfk_eq : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f =
        value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f := by
      have hkf0 := Bool.eq_false_iff.mpr hkf
      rw [hkf0]; symm
      by_contra hft
      have hr0_f := Bool.eq_true_of_not_eq_false hft
      have h0j_f : value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) d.f = true := by
        rw [← value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
          (x := oneEachRaw n m d.r₀ j_star) (y := fun w => decide (w = n + j_star.val))
          fun w _ hwf => by
            simp only [oneEachRaw, decide_eq_decide]
            exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩]
        exact hr0_f
      have hkj_f : value (n + m) d.E (oneEachRaw n m k₀ j_star) (fun _ => none) d.f = true :=
        eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
          (fun _ _ _ _ h => by cases h)
          (fun j hj hlt _ => ⟨rfl, fun ho => by
            have := (d.hjnot j hj).mp ho; change n + m + j < n + m + d.j_not at hlt; omega⟩)
          (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
          (parent_live d.hL d.hj1L d.hf_j1) hfq h0j_f
      rw [hkj_f] at hkf0; cases hkf0
    have hr0_f_eq : value (n + m) d.E (oneEachRaw n m d.r₀ j_star) (fun _ => none) d.f =
        value (n + m) d.E (fun w => decide (w = n + j_star.val)) (fun _ => none) d.f :=
      value_agree_inputs d.hL (fun _ => none) (parent_live d.hL d.hj1L d.hf_j1)
        fun w _ hwf => by
          simp only [oneEachRaw, decide_eq_decide]
          exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩
    have hsame := cut_agree d.hL d.f d.hsingle
      (oneEachRaw n m k₀ j_star) (fun w => decide (w = n + j_star.val))
      (fun _ => none) (fun _ => none)
      (fun w _ hwf => by
        simp only [oneEachRaw, decide_eq_decide]
        constructor
        · intro h
          rcases h with rfl | hw
          · exact False.elim (hwf hk0_f)
          · exact hw
        · intro hw; exact Or.inr hw)
      (fun _ _ _ => rfl) (hfk_eq.trans hr0_f_eq) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (Or.inr fun hr => by
        have := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
        have := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
        have := reaches_le hr; omega)
    have hr0_same := value_agree_inputs d.hL (fun _ => none) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (x := oneEachRaw n m d.r₀ j_star) (y := fun w => decide (w = n + j_star.val))
      fun w _ hwr => by
        simp only [oneEachRaw, decide_eq_decide]
        exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
    rw [← hr0_same, d.hRep k₀ j_star, d.hRep d.r₀ j_star, hj_k0, hj_r0] at hsame; cases hsame
  by_contra htrue
  have ht1 := Bool.eq_true_of_not_eq_false htrue
  have htk := evalT_mono d sd id id (fun _ _ h => by cases h) ht1 (y := oneEachRaw n m k₀ j_star)
  have hev := evalT_eq_eval d sd hf_not (oneEachRaw n m k₀ j_star)
  rw [hf_k0, Bool.not_true, d.hRep k₀ j_star, hj_k0] at hev
  rw [htk] at hev; cases hev

theorem evalT_indep_of_reaches_f {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (sd : SplitData n m A d) (bf bn : Bool) {v : ℕ} (hvf : reaches (n + m) d.E d.L v d.f)
    {x y : ℕ → Bool} (hxy : ∀ w < n + m, w ≠ v → x w = y w) :
    evalT d bf bn x = evalT d bf bn y := by
  have hfR : d.f < n + m + d.r := by
    have := edgeTo_lt ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩
    have := reaches_le (reaches_root_of_closed d.hL d.huse d.j₁ d.hj1L)
    omega
  have hna : ¬ activeReach (n + m) d.E d.L (some d.f) v (n + m + d.r) :=
    fun ha => activeReach_skip_f_lt (fun a ha' => d.hsingle a ha') hfR hvf ha
  exact eval_unchanged_of_not_active d.hL d.f sd.d_N_le_f (fixBranch d bf bn)
    ⟨bf, by dsimp only [fixBranch]; rw [if_pos rfl]⟩
    hxy (Or.inr ⟨d.r, d.hrL, rfl⟩) hna

theorem f_singleton_row_col {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hA00 : A d.r₀ d.c₀ = false) (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) :
    ∃ (u₁ : Fin n) (v₁ : Fin m),
      (∀ i : Fin n, reaches (n + m) d.E d.L i.val d.f ↔ i = u₁) ∧
      (∀ j : Fin m, reaches (n + m) d.E d.L (n + j.val) d.f ↔ j = v₁) ∧
      (∀ i j, value (n + m) d.E (oneEachRaw n m i j) (fun _ => none) d.f = decide (i = u₁ ∨ j = v₁)) := by
  have hfq : d.f < n + m + d.j_not := jnot_input_lt d hf_not
  have hf_live := parent_live d.hL d.hj1L d.hf_j1
  have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
    exact (d.hc0 d.c₀).mpr rfl
  have h_reaches_col_r0 : ∀ j : Fin m, reaches (n + m) d.E d.L (n + j.val) d.f → A d.r₀ j = false := by
    intro j hjf
    rw [← d.hRep d.r₀ j, ← evalT_eq_eval d sd hf_not]
    have h_z : ∀ bf bn, evalT d bf bn (oneEachRaw n m d.r₀ j) = evalT d bf bn (fun _ => false) := by
      intro bf bn
      have ha1 := value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
        fun w _ hwr => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
      have ha2 := evalT_indep_of_reaches_f d sd bf bn hjf (x := fun w => decide (w = n + j.val)) (y := fun _ => false)
        fun w _ hne => by simp [hne]
      exact ha1.trans ha2
    cases value (n + m) d.E (oneEachRaw n m d.r₀ j) (fun _ => none) d.f <;> simp only [Bool.not_false, Bool.not_true]
    · rw [h_z false true]; exact T_010_false hg d sd hA00 hf_not
    · rw [h_z true false]; exact T_100_false hg d sd hf_not
  have h_reaches_row_c0 : ∀ i : Fin n, reaches (n + m) d.E d.L i.val d.f → A i d.c₀ = false := by
    intro i hif
    rw [← d.hRep i d.c₀, ← evalT_eq_eval d sd hf_not]
    have h_z : ∀ bf bn, evalT d bf bn (oneEachRaw n m i d.c₀) = evalT d bf bn (fun _ => false) := by
      intro bf bn
      have ha1 := value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩)
        (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
        fun w _ hwr => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hwr)), Or.inl⟩
      have ha2 := evalT_indep_of_reaches_f d sd bf bn hif (x := fun w => decide (w = i.val)) (y := fun _ => false)
        fun w _ hne => by simp [hne]
      exact ha1.trans ha2
    cases value (n + m) d.E (oneEachRaw n m i d.c₀) (fun _ => none) d.f <;> simp only [Bool.not_false, Bool.not_true]
    · rw [h_z false true]; exact T_010_false hg d sd hA00 hf_not
    · rw [h_z true false]; exact T_100_false hg d sd hf_not
  have h_f_z_row : ∀ i : Fin n, reaches (n + m) d.E d.L i.val d.f →
      value (n + m) d.E (fun w => decide (w = i.val)) (fun _ => none) d.f = true := by
    intro i hif
    by_contra hzf
    have hzf0 := Bool.eq_false_iff.mpr hzf
    have hrow_eq : ∀ j : Fin m, A i j = A d.r₀ j := by
      intro j
      by_cases hfj : value (n + m) d.E (oneEachRaw n m i j) (fun _ => none) d.f = true
      · have hjf : reaches (n + m) d.E d.L (n + j.val) d.f := by
          by_contra hnjf
          have := value_agree_inputs d.hL (fun _ => none) hf_live
            (x := oneEachRaw n m i j) (y := fun w => decide (w = i.val))
            fun w _ hwf => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right (fun e => hnjf (e ▸ hwf)), Or.inl⟩
          rw [this, hzf0] at hfj; cases hfj
        have hAi : A i j = false := by
          rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hfj, Bool.not_true]
          have h1 := evalT_indep_of_reaches_f d sd true false hif (x := oneEachRaw n m i j) (y := fun w => decide (w = n + j.val))
            fun w _ hwi => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwi, Or.inr⟩
          have h2 := evalT_indep_of_reaches_f d sd true false hjf (x := fun w => decide (w = n + j.val)) (y := fun _ => false)
            fun w _ hwj => by simp [hwj]
          rw [h1, h2]; exact T_100_false hg d sd hf_not
        rw [hAi, h_reaches_col_r0 j hjf]
      · have hfj0 := Bool.eq_false_iff.mpr hfj
        have hfr0 : value (n + m) d.E (oneEachRaw n m d.r₀ j) (fun _ => none) d.f = false := by
          by_contra hr1
          have hr1t := Bool.eq_true_of_not_eq_false hr1
          have h0j : value (n + m) d.E (fun w => decide (w = n + j.val)) (fun _ => none) d.f = true := by
            rw [← value_agree_inputs d.hL (fun _ => none) hf_live
              (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
              fun w _ hwf => by
                simp only [oneEachRaw, decide_eq_decide]
                exact ⟨fun h => h.resolve_left (fun e => hr0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inr⟩]
            exact hr1t
          have hij := eval_mono_bound d.hL d.hFan (x := fun w => decide (w = n + j.val)) (y := oneEachRaw n m i j)
            (fix₀ := fun _ => none) (fix₁ := fun _ => none)
            (fun _ _ _ _ h => by cases h)
            (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
            (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
            hf_live hfq h0j
          rw [hij] at hfj0; cases hfj0
        rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hfj0, Bool.not_false]
        rw [← d.hRep d.r₀ j, ← evalT_eq_eval d sd hf_not, hfr0, Bool.not_false]
        have h1 := evalT_indep_of_reaches_f d sd false true hif (x := oneEachRaw n m i j) (y := fun w => decide (w = n + j.val))
          fun w _ hwi => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hwi, Or.inr⟩
        have h2 := value_agree_inputs d.hL (fixBranch d false true) (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (x := oneEachRaw n m d.r₀ j) (y := fun w => decide (w = n + j.val))
          fun w _ hwr => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hwr)), Or.inr⟩
        exact h1.trans h2.symm
    have hine : i ≠ d.r₀ := fun e => hr0_away (e ▸ (hif.trans (f_reaches_root d)))
    exact hine (hg.1 (funext hrow_eq))
  have h_f_z_col : ∀ j : Fin m, reaches (n + m) d.E d.L (n + j.val) d.f →
      value (n + m) d.E (fun w => decide (w = n + j.val)) (fun _ => none) d.f = true := by
    intro j hjf
    by_contra hzf
    have hzf0 := Bool.eq_false_iff.mpr hzf
    have hcol_eq : ∀ i : Fin n, A i j = A i d.c₀ := by
      intro i
      by_cases hfi : value (n + m) d.E (oneEachRaw n m i j) (fun _ => none) d.f = true
      · have hif : reaches (n + m) d.E d.L i.val d.f := by
          by_contra hnif
          have := value_agree_inputs d.hL (fun _ => none) hf_live
            (x := oneEachRaw n m i j) (y := fun w => decide (w = n + j.val))
            fun w _ hwf => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left (fun e => hnif (e ▸ hwf)), Or.inr⟩
          rw [this, hzf0] at hfi; cases hfi
        have hAj : A i j = false := by
          rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hfi, Bool.not_true]
          have h1 := evalT_indep_of_reaches_f d sd true false hjf (x := oneEachRaw n m i j) (y := fun w => decide (w = i.val))
            fun w _ hwj => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwj, Or.inl⟩
          have h2 := evalT_indep_of_reaches_f d sd true false hif (x := fun w => decide (w = i.val)) (y := fun _ => false)
            fun w _ hwi => by simp [hwi]
          rw [h1, h2]; exact T_100_false hg d sd hf_not
        rw [hAj, h_reaches_row_c0 i hif]
      · have hfi0 := Bool.eq_false_iff.mpr hfi
        have hfc0 : value (n + m) d.E (oneEachRaw n m i d.c₀) (fun _ => none) d.f = false := by
          by_contra hc1
          have hc1t := Bool.eq_true_of_not_eq_false hc1
          have hi0 : value (n + m) d.E (fun w => decide (w = i.val)) (fun _ => none) d.f = true := by
            rw [← value_agree_inputs d.hL (fun _ => none) hf_live
              (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
              fun w _ hwf => by
                simp only [oneEachRaw, decide_eq_decide]
                exact ⟨fun h => h.resolve_right (fun e => hc0_away ((e ▸ hwf).trans (f_reaches_root d))), Or.inl⟩]
            exact hc1t
          have hij := eval_mono_bound d.hL d.hFan (x := fun w => decide (w = i.val)) (y := oneEachRaw n m i j)
            (fix₀ := fun _ => none) (fix₁ := fun _ => none)
            (fun _ _ _ _ h => by cases h)
            (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
            (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
            hf_live hfq hi0
          rw [hij] at hfi0; cases hfi0
        rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hfi0, Bool.not_false]
        rw [← d.hRep i d.c₀, ← evalT_eq_eval d sd hf_not, hfc0, Bool.not_false]
        have h1 := evalT_indep_of_reaches_f d sd false true hjf (x := oneEachRaw n m i j) (y := fun w => decide (w = i.val))
          fun w _ hwj => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hwj, Or.inl⟩
        have h2 := value_agree_inputs d.hL (fixBranch d false true) (Or.inr ⟨d.r, d.hrL, rfl⟩)
          (x := oneEachRaw n m i d.c₀) (y := fun w => decide (w = i.val))
          fun w _ hwc => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hwc)), Or.inl⟩
        exact h1.trans h2.symm
    have hjne : j ≠ d.c₀ := fun e => hc0_away (e ▸ (hjf.trans (f_reaches_root d)))
    exact hjne (hg.2.1 (funext hcol_eq))
  obtain ⟨k₀, hk₀⟩ := hg.2.2.1 d.r₀
  have hk0_f : reaches (n + m) d.E d.L k₀.val d.f := by
    by_contra hnf
    exact contradict_IncR_of_unate hg d hk₀ (single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := k₀.val) (by have := k₀.isLt; omega)
      (fun a b c hr _ e1 e2 => d.hsingle a (fun ha => by rw [activeReach_none_iff] at hr; exact hnf (ha ▸ hr)) b c e1 e2)
      (Or.inr ⟨d.r, d.hrL, rfl⟩))
  obtain ⟨l₀, hl₀⟩ := hg.2.2.2.1 d.c₀
  have hl0_f : reaches (n + m) d.E d.L (n + l₀.val) d.f := by
    by_contra hnf
    exact contradict_IncC_of_unate hg d hl₀ (single_path_unate d.hL d.hFan d.hNotLen (skip := none) (fix := fun _ => none)
      (fun _ => by simp) (fun _ h => by cases h) (i := n + l₀.val) (by have := l₀.isLt; omega)
      (fun a b c hr _ e1 e2 => d.hsingle a (fun ha => by rw [activeReach_none_iff] at hr; exact hnf (ha ▸ hr)) b c e1 e2)
      (Or.inr ⟨d.r, d.hrL, rfl⟩))
  have hr_uniq : ∀ i₁ i₂ : Fin n, reaches (n + m) d.E d.L i₁.val d.f → reaches (n + m) d.E d.L i₂.val d.f → i₁ = i₂ := by
    intro i₁ i₂ h1 h2
    apply hg.1; funext j
    have f1 : value (n + m) d.E (oneEachRaw n m i₁ j) (fun _ => none) d.f = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
        hf_live hfq (h_f_z_row i₁ h1)
    have f2 : value (n + m) d.E (oneEachRaw n m i₂ j) (fun _ => none) d.f = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
        hf_live hfq (h_f_z_row i₂ h2)
    rw [← d.hRep i₁ j, ← d.hRep i₂ j, ← evalT_eq_eval d sd hf_not, ← evalT_eq_eval d sd hf_not, f1, f2, Bool.not_true]
    have e1 := evalT_indep_of_reaches_f d sd true false h1 (x := oneEachRaw n m i₁ j) (y := fun w => decide (w = n + j.val))
      fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hw, Or.inr⟩
    have e2 := evalT_indep_of_reaches_f d sd true false h2 (x := oneEachRaw n m i₂ j) (y := fun w => decide (w = n + j.val))
      fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_left hw, Or.inr⟩
    exact e1.trans e2.symm
  have hc_uniq : ∀ j₁ j₂ : Fin m, reaches (n + m) d.E d.L (n + j₁.val) d.f → reaches (n + m) d.E d.L (n + j₂.val) d.f → j₁ = j₂ := by
    intro j₁ j₂ h1 h2
    apply hg.2.1; funext i
    dsimp only
    have f1 : value (n + m) d.E (oneEachRaw n m i j₁) (fun _ => none) d.f = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
        hf_live hfq (h_f_z_col j₁ h1)
    have f2 : value (n + m) d.E (oneEachRaw n m i j₂) (fun _ => none) d.f = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
        hf_live hfq (h_f_z_col j₂ h2)
    rw [← d.hRep i j₁, ← d.hRep i j₂, ← evalT_eq_eval d sd hf_not, ← evalT_eq_eval d sd hf_not, f1, f2, Bool.not_true]
    have e1 := evalT_indep_of_reaches_f d sd true false h1 (x := oneEachRaw n m i j₁) (y := fun w => decide (w = i.val))
      fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hw, Or.inl⟩
    have e2 := evalT_indep_of_reaches_f d sd true false h2 (x := oneEachRaw n m i j₂) (y := fun w => decide (w = i.val))
      fun w _ hw => by simp only [oneEachRaw, decide_eq_decide]; exact ⟨fun h => h.resolve_right hw, Or.inl⟩
    exact e1.trans e2.symm
  refine ⟨k₀, l₀, fun i => ⟨fun hi => hr_uniq i k₀ hi hk0_f, fun e => e ▸ hk0_f⟩,
    fun j => ⟨fun hj => hc_uniq j l₀ hj hl0_f, fun e => e ▸ hl0_f⟩, fun i j => ?_⟩
  by_cases hij : i = k₀ ∨ j = l₀
  · rw [decide_eq_true hij]
    rcases hij with rfl | rfl
    · exact eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw)
        hf_live hfq (h_f_z_row i hk0_f)
    · exact eval_mono_bound d.hL d.hFan (fix₀ := fun _ => none) (fix₁ := fun _ => none)
        (fun _ _ _ _ h => by cases h)
        (fun k hk hlt _ => ⟨rfl, fun ho => by have := (d.hjnot k hk).mp ho; change n + m + k < n + m + d.j_not at hlt; omega⟩)
        (fun w _ hw => by simp only [oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw)
        hf_live hfq (h_f_z_col j hl0_f)
  · rw [decide_eq_false hij]
    have hni : ¬ reaches (n + m) d.E d.L i.val d.f := fun h => hij (Or.inl (hr_uniq i k₀ h hk0_f))
    have hnj : ¬ reaches (n + m) d.E d.L (n + j.val) d.f := fun h => hij (Or.inr (hc_uniq j l₀ h hl0_f))
    rw [value_agree_inputs d.hL (fun _ => none) hf_live
      (x := oneEachRaw n m i j) (y := fun _ => false) fun w _ hwf => by
        simp only [oneEachRaw, decide_eq_false_iff_not, not_or]
        exact ⟨fun e => hni (e ▸ hwf), fun e => hnj (e ▸ hwf)⟩]
    exact false_of_no_not_reach d hf_live fun hqf => by have := reaches_le hqf; omega

-- Block C.3: TreeOK Rectangles, Unique r₃ / c₃, Residual B-Matching

inductive FreePath (N : ℕ) (C : Circuit) (L : Finset ℕ) (fix : ℕ → Option Bool) (a : ℕ) : ℕ → Prop
  | refl : fix a = none → FreePath N C L fix a a
  | tail {b c : ℕ} : FreePath N C L fix a b → edgeTo N C L b c → fix c = none → FreePath N C L fix a c

theorem FreePath_le {N : ℕ} {C : Circuit} {L : Finset ℕ} {fix : ℕ → Option Bool} {a b : ℕ}
    (h : FreePath N C L fix a b) : a ≤ b := by
  induction h with
  | refl _ => exact le_rfl
  | tail _ e _ ih => exact le_trans ih (le_of_lt (edgeTo_lt e))

theorem FreePath_fix_left {N : ℕ} {C : Circuit} {L : Finset ℕ} {fix : ℕ → Option Bool} {a b : ℕ}
    (h : FreePath N C L fix a b) : fix a = none := by
  induction h with
  | refl ha => exact ha
  | tail _ _ _ ih => exact ih

theorem FreePath_head {N : ℕ} {C : Circuit} {L : Finset ℕ} {fix : ℕ → Option Bool} {a c : ℕ}
    (h : FreePath N C L fix a c) :
    a = c ∨ ∃ b, edgeTo N C L a b ∧ fix b = none ∧ FreePath N C L fix b c := by
  induction h with
  | refl _ => exact Or.inl rfl
  | tail _ e hc ih =>
    rcases ih with rfl | ⟨b, eab, hfb, hbu⟩
    · exact Or.inr ⟨_, e, hc, .refl hc⟩
    · exact Or.inr ⟨b, eab, hfb, .tail hbu e hc⟩

theorem FreePath_last_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {fix : ℕ → Option Bool}
    (huniq : ∀ a, fix a = none → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {a b₁ b₂ w : ℕ}
    (hb₁ : FreePath N C L fix a b₁) (hb₂ : FreePath N C L fix a b₂)
    (e₁ : edgeTo N C L b₁ w) (e₂ : edgeTo N C L b₂ w) : b₁ = b₂ := by
  have hmain : ∀ d a, b₁ - a = d →
      FreePath N C L fix a b₁ → FreePath N C L fix a b₂ →
      edgeTo N C L b₁ w → edgeTo N C L b₂ w → b₁ = b₂ := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro a hd h₁ h₂ ew₁ ew₂
      rcases FreePath_head h₁ with rfl | ⟨u₁, eau₁, _, hu₁b₁⟩
      · rcases FreePath_head h₂ with rfl | ⟨u₂, eau₂, _, hu₂b₂⟩
        · rfl
        · have := huniq a (FreePath_fix_left h₁) w u₂ ew₁ eau₂
          subst this
          have := FreePath_le hu₂b₂
          have := edgeTo_lt ew₂
          omega
      · rcases FreePath_head h₂ with rfl | ⟨u₂, eau₂, _, hu₂b₂⟩
        · have := huniq a (FreePath_fix_left h₂) u₁ w eau₁ ew₂
          subst this
          have := FreePath_le hu₁b₁
          have := edgeTo_lt ew₁
          omega
        · have := huniq a (FreePath_fix_left h₁) u₁ u₂ eau₁ eau₂
          subst this
          have := edgeTo_lt eau₁
          have := FreePath_le hu₁b₁
          exact ih (b₁ - u₁) (by omega) u₁ rfl hu₁b₁ hu₂b₂ ew₁ ew₂
  exact hmain (b₁ - a) a rfl hb₁ hb₂ e₁ e₂

theorem treeOK_value_fix {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hFan : FanInTwo C) (fix : ℕ → Option Bool)
    (hfixN : ∀ v < N, fix v = none)
    (hNoNot : ∀ j ∈ L, fix (N + j) = none → (gateAt C j).op ≠ .not)
    (hTwo : ∀ j ∈ L, fix (N + j) = none → ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a, b] ∧ a < N + j ∧ b < N + j)
    (huniq : ∀ a, fix a = none → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    {w : ℕ} (hw : live N L w) :
    ∃ s : Finset (Fin N), (∀ i ∈ s, FreePath N C L fix i.val w ∧ fix w = none) ∧
      TreeOK s (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix w) := by
  classical
  revert hw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with low | ⟨j, hj, rfl⟩
    · let i₀ : Fin N := ⟨w, low⟩
      refine ⟨{i₀}, fun i hi => ?_, ?_⟩
      · obtain rfl := Finset.mem_singleton.mp hi
        exact ⟨.refl (hfixN w low), hfixN w low⟩
      · have hfn : (fun x : Fin N → Bool =>
            value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix w) = fun x => x i₀ := by
          funext x; rw [val_raw low, dif_pos low]
        rw [hfn]
        right; right
        refine ⟨⟨i₀, by simp⟩, fun x y h => h i₀ (by simp), by simp [bits], rfl, ?_⟩
        intro a b c d ha hb _ _ hab _ _
        simp only [bits, edge, Finset.mem_singleton, Finset.mem_insert, decide_eq_false_iff_not,
          decide_eq_true_eq] at ha hb hab
        tauto
    · rcases Option.eq_none_or_eq_some (fix (N + j)) with hfx | ⟨b, hfx⟩
      · obtain ⟨a, b, hab, hin, ha_lt, hb_lt⟩ := hTwo j hj hfx
        have ha_mem : a ∈ (gateAt C j).inputs := by simp [hin]
        have hb_mem : b ∈ (gateAt C j).inputs := by simp [hin]
        obtain ⟨sa, hsa_sub, ha_ok⟩ := ih a ha_lt (parent_live hL hj ⟨ha_mem, ha_lt⟩)
        obtain ⟨sb, hsb_sub, hb_ok⟩ := ih b hb_lt (parent_live hL hj ⟨hb_mem, hb_lt⟩)
        have hdis : Disjoint sa sb := by
          apply Finset.disjoint_left.mpr
          intro i hia hib
          obtain ⟨hra, _⟩ := hsa_sub i hia
          obtain ⟨hrb, _⟩ := hsb_sub i hib
          have e_a : edgeTo N C L a (N + j) := ⟨j, hj, rfl, ha_mem, ha_lt⟩
          have e_b : edgeTo N C L b (N + j) := ⟨j, hj, rfl, hb_mem, hb_lt⟩
          exact hab (FreePath_last_eq huniq hra hrb e_a e_b)
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
          exact List.getElem_mem _
        have hno := hNoNot j hj hfx
        have h_or_and : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
          rcases (hFan _ hmem).1 with ho | ho | ho
          · exact Or.inl ho
          · exact Or.inr ho
          · exact False.elim (hno ho)
        let isAnd := decide ((gateAt C j).op = .and)
        have hfn_eq : (fun x : Fin N → Bool =>
            value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix (N + j)) =
            connect isAnd
              (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix a)
              (fun x : Fin N → Bool => value N C (fun v => if h : v < N then x ⟨v, h⟩ else false) fix b) := by
          funext x
          rw [val_gate hfx, hin]
          rcases h_or_and with ho | ho <;> simp [isAnd, ho, GateOp.eval, connect, ha_lt, hb_lt]
        refine ⟨sa ∪ sb, fun i hi => ?_, ?_⟩
        · rcases Finset.mem_union.mp hi with hia | hib
          · obtain ⟨hra, _⟩ := hsa_sub i hia
            exact ⟨.tail hra ⟨j, hj, rfl, ha_mem, ha_lt⟩ hfx, hfx⟩
          · obtain ⟨hrb, _⟩ := hsb_sub i hib
            exact ⟨.tail hrb ⟨j, hj, rfl, hb_mem, hb_lt⟩ hfx, hfx⟩
        · rw [hfn_eq]
          exact combined_treeOK isAnd hdis ha_ok hb_ok
      · refine ⟨∅, fun _ h => by simp at h, ?_⟩
        cases b
        · left; intro x; exact val_fixed (by omega) hfx
        · right; left; intro x; exact val_fixed (by omega) hfx

def rPt {n m : ℕ} (i : Fin n) : Fin (n + m) := ⟨i.val, by omega⟩
def cPt {n m : ℕ} (j : Fin m) : Fin (n + m) := ⟨n + j.val, by omega⟩
def sBit (k : ℕ) (w : ℕ) : Bool := decide (w = k)
def pairBit (k₁ k₂ w : ℕ) : Bool := decide (w = k₁ ∨ w = k₂)

theorem evalT_rect {n m : ℕ} {A : Fin n → Fin m → Bool}
    (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    (bf bn : Bool) (hT0 : evalT d bf bn (fun _ => false) = false)
    (i₁ i₂ : Fin n) (j₁ j₂ : Fin m)
    (h11 : evalT d bf bn (oneEachRaw n m i₁ j₁) = true)
    (h21 : evalT d bf bn (oneEachRaw n m i₂ j₁) = true)
    (h22 : evalT d bf bn (oneEachRaw n m i₂ j₂) = true) :
    evalT d bf bn (oneEachRaw n m i₁ j₂) = true ∨
      evalT d bf bn (sBit (n + j₁.val)) = true ∨
      evalT d bf bn (sBit i₂.val) = true := by
  let fFn : (Fin (n + m) → Bool) → Bool := fun x =>
    evalT d bf bn (fun v => if h : v < n + m then x ⟨v, h⟩ else false)
  have hf_mono : ∀ x y : Fin (n + m) → Bool, (∀ v, x v = true → y v = true) → fFn x = true → fFn y = true := by
    intro x y hxy hx
    exact evalT_mono d sd id id (fun v hv hxv => by
      rw [dif_pos hv] at hxv ⊢
      exact hxy ⟨v, hv⟩ hxv) hx
  have hfixN : ∀ v < n + m, fixBranch d bf bn v = none := by
    intro v hv
    have hnf := sd.d_N_le_f
    dsimp only [fixBranch]
    rw [if_neg (by omega), if_neg (by omega)]
  have hNoNot : ∀ j ∈ d.L, fixBranch d bf bn (n + m + j) = none → (gateAt d.E j).op ≠ .not := by
    intro j hj hnone ho
    have hjn := (d.hjnot j hj).mp ho
    dsimp only [fixBranch] at hnone
    by_cases h1 : n + m + j = d.f
    · rw [if_pos h1] at hnone; cases hnone
    · rw [if_neg h1, if_pos (by omega)] at hnone; cases hnone
  have hTwo : ∀ j ∈ d.L, fixBranch d bf bn (n + m + j) = none →
      ∃ a b, a ≠ b ∧ (gateAt d.E j).inputs = [a, b] ∧ a < n + m + j ∧ b < n + m + j := by
    intro j hj hnone
    have hjne : j ≠ d.j_not := by
      intro e; subst e; dsimp only [fixBranch] at hnone
      rw [if_neg (by have := jnot_input_lt d hf_not; omega), if_pos rfl] at hnone; cases hnone
    exact (d.hother_two j hj hjne).2
  have huniq : ∀ a, fixBranch d bf bn a = none → ∀ b c, edgeTo (n + m) d.E d.L a b → edgeTo (n + m) d.E d.L a c → b = c := by
    intro a ha b c eb ec
    have haf : a ≠ d.f := by intro e; subst e; dsimp only [fixBranch] at ha; rw [if_pos rfl] at ha; cases ha
    exact d.hsingle a haf b c eb ec
  obtain ⟨s, _, hs_ok⟩ := treeOK_value_fix d.hL d.hFan (fixBranch d bf bn) hfixN hNoNot hTwo huniq
    (Or.inr ⟨d.r, d.hrL, rfl⟩)
  change TreeOK s fFn at hs_ok
  have h_pair_eq (i : Fin n) (j : Fin m) :
      fFn (bits ({rPt i, cPt j} : Finset (Fin (n + m)))) = evalT d bf bn (oneEachRaw n m i j) := by
    refine value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v hv _ => ?_
    by_cases hr : v = i.val
    · subst hr; simp [bits, rPt, cPt, oneEachRaw, hv]
    · by_cases hc : v = n + j.val
      · subst hc; simp [bits, rPt, cPt, oneEachRaw, hv]
      · simp [bits, rPt, cPt, oneEachRaw, hv, hr, hc, Fin.ext_iff]
  have h_r_eq (i : Fin n) :
      fFn (bits ({rPt i} : Finset (Fin (n + m)))) = evalT d bf bn (sBit i.val) := by
    refine value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v hv _ => ?_
    simp [bits, rPt, sBit, hv, Fin.ext_iff]
  have h_c_eq (j : Fin m) :
      fFn (bits ({cPt j} : Finset (Fin (n + m)))) = evalT d bf bn (sBit (n + j.val)) := by
    refine value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩) fun v hv _ => ?_
    simp [bits, cPt, sBit, hv, Fin.ext_iff]
  rw [← h_pair_eq] at h11 h21 h22 ⊢
  rw [← h_c_eq, ← h_r_eq]
  rcases hs_ok with h0 | h1 | ⟨_, _, _, _, hRect⟩
  · have := h0 (bits {rPt i₁, cPt j₁})
    rw [this] at h11; cases h11
  · exact Or.inl (h1 _)
  · by_cases hc1 : fFn (bits {cPt j₁}) = true
    · exact Or.inr (Or.inl hc1)
    · by_cases hr2 : fFn (bits {rPt i₂}) = true
      · exact Or.inr (Or.inr hr2)
      · by_cases hr1 : fFn (bits {rPt i₁}) = true
        · left
          exact hf_mono _ _ (fun v hv => by
            simp only [bits, Finset.mem_singleton, Finset.mem_insert, decide_eq_true_eq] at hv ⊢
            exact Or.inl hv) hr1
        · by_cases hc2 : fFn (bits {cPt j₂}) = true
          · left
            exact hf_mono _ _ (fun v hv => by
              simp only [bits, Finset.mem_singleton, Finset.mem_insert, decide_eq_true_eq] at hv ⊢
              exact Or.inr hv) hc2
          · exact Or.inl (hRect (rPt i₁) (cPt j₁) (rPt i₂) (cPt j₂)
              (Bool.eq_false_iff.mpr hr1) (Bool.eq_false_iff.mpr hc1)
              (Bool.eq_false_iff.mpr hr2) (Bool.eq_false_iff.mpr hc2)
              h11 h21 h22)

theorem reaches_from_d_f {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) :
    let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
    (j_hit ∈ d.L ∧ j_hit ≠ d.j_not ∧ edgeTo (n + m) d.E d.L d.f (n + m + j_hit)) ∧
      ∀ j ∈ d.L, edgeTo (n + m) d.E d.L d.f (n + m + j) → j = d.j_not ∨ j = j_hit := by
  intro j_hit
  have hfq := jnot_input_lt d hf_not
  have hnot_bef : before d.E (n + m) d.j_not d.f := ⟨by rw [hf_not]; simp, hfq⟩
  have hnot_split : d.j_not = d.j₁ ∨ d.j_not = d.j₂ := d.hf_two d.j_not d.hjnotL hnot_bef
  by_cases h1 : d.j₁ = d.j_not
  · have h_hit : j_hit = d.j₂ := by simp [j_hit, h1]
    rw [h_hit]
    refine ⟨⟨d.hj2L, fun e => d.hj12 (h1.trans e.symm), ⟨d.j₂, d.hj2L, rfl, d.hf_j2⟩⟩,
      fun j hj ⟨j', _, h_eq, hbef⟩ => ?_⟩
    have hj_eq : j' = j := (Nat.add_left_cancel h_eq).symm
    rw [hj_eq] at hbef
    rcases d.hf_two j hj hbef with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr rfl
  · have h_hit : j_hit = d.j₁ := by simp [j_hit, h1]
    rw [h_hit]
    have h2 : d.j₂ = d.j_not := (hnot_split.resolve_left (fun e => h1 e.symm)).symm
    refine ⟨⟨d.hj1L, h1, ⟨d.j₁, d.hj1L, rfl, d.hf_j1⟩⟩,
      fun j hj ⟨j', _, h_eq, hbef⟩ => ?_⟩
    have hj_eq : j' = j := (Nat.add_left_cancel h_eq).symm
    rw [hj_eq] at hbef
    rcases d.hf_two j hj hbef with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl h2

theorem value_indep_bf_of_no_jhit {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    (x : ℕ → Bool) (bf₀ bf₁ bn : Bool) :
    let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
    ∀ u, live (n + m) d.L u → u ≠ d.f → ¬ reaches (n + m) d.E d.L (n + m + j_hit) u →
      value (n + m) d.E x (fixBranch d bf₀ bn) u = value (n + m) d.E x (fixBranch d bf₁ bn) u := by
  intro j_hit u hu hnf hnreach
  have hrdf := reaches_from_d_f d hf_not
  revert hu hnf hnreach
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hnf hnreach
    rcases hu with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
    · by_cases hjq : j = d.j_not
      · subst hjq
        have hne : n + m + d.j_not ≠ d.f := by intro e; exact hnf e
        have hf0 : fixBranch d bf₀ bn (n + m + d.j_not) = some bn := by
          dsimp only [fixBranch]; rw [if_neg hne, if_pos rfl]
        have hf1 : fixBranch d bf₁ bn (n + m + d.j_not) = some bn := by
          dsimp only [fixBranch]; rw [if_neg hne, if_pos rfl]
        rw [val_fixed (by omega) hf0, val_fixed (by omega) hf1]
      · have hfx0 : fixBranch d bf₀ bn (n + m + j) = none := by
          dsimp only [fixBranch]; rw [if_neg hnf, if_neg (by omega)]
        have hfx1 : fixBranch d bf₁ bn (n + m + j) = none := by
          dsimp only [fixBranch]; rw [if_neg hnf, if_neg (by omega)]
        have hjnhit : j ≠ j_hit := fun e => hnreach (e ▸ Relation.ReflTransGen.refl)
        rw [val_gate hfx0, val_gate hfx1]
        have hmap : List.map (fun a => if a < n + m + j then value (n + m) d.E x (fixBranch d bf₀ bn) a else false)
              (gateAt d.E j).inputs =
            List.map (fun a => if a < n + m + j then value (n + m) d.E x (fixBranch d bf₁ bn) a else false)
              (gateAt d.E j).inputs := by
          apply List.map_congr_left
          intro a ha
          by_cases halt : a < n + m + j
          · simp only [halt, ↓reduceIte]
            have eaj : edgeTo (n + m) d.E d.L a (n + m + j) := ⟨j, hj, rfl, ha, halt⟩
            have hanf : a ≠ d.f := by
              intro e; subst e
              rcases hrdf.2 j hj eaj with h | h
              · exact hjq h
              · exact hjnhit h
            exact ih a halt (parent_live d.hL hj ⟨ha, halt⟩) hanf
              fun h => hnreach (Relation.ReflTransGen.tail h eaj)
          · simp only [halt, ↓reduceIte]
        rw [hmap]

theorem value_mono_node_above {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (sd : SplitData n m A d) (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {m₀ : ℕ} (hm0L : ∃ jm ∈ d.L, m₀ = n + m + jm)
    (hm0_reach : reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) m₀)
    {x y : ℕ → Bool} (hxy : ∀ v < n + m, x v = true → y v = true)
    (hm0_val : value (n + m) d.E x (fixBranch d true false) m₀ = true →
      value (n + m) d.E y (fixBranch d false true) m₀ = true) :
    evalT d true false x = true → evalT d false true y = true := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  have hrdf := reaches_from_d_f d hf_not
  have hjhit_gt : d.f < n + m + j_hit := edgeTo_lt hrdf.1.2.2
  have hmain : ∀ u, live (n + m) d.L u →
      ((¬ reaches (n + m) d.E d.L (n + m + j_hit) u ∧ u ≠ d.f) ∨ reaches (n + m) d.E d.L m₀ u) →
      value (n + m) d.E x (fixBranch d true false) u = true →
      value (n + m) d.E y (fixBranch d false true) u = true := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu hok hval
      rcases hok with ⟨hnreach, hnf⟩ | hm0u
      · rw [value_indep_bf_of_no_jhit d hf_not x true false false u hu hnf hnreach] at hval
        exact eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d false false) (fix₁ := fixBranch d false true)
          (fun k _ _ b₀ hb₀ => by
            dsimp only [fixBranch] at hb₀ ⊢
            by_cases h1 : n + m + k = d.f
            · rw [if_pos h1] at hb₀ ⊢; cases hb₀; exact ⟨false, rfl, id⟩
            · by_cases h2 : n + m + k = n + m + d.j_not
              · rw [if_neg h1, if_pos h2] at hb₀ ⊢; cases hb₀; exact ⟨true, rfl, fun e => by cases e⟩
              · rw [if_neg h1, if_neg h2] at hb₀; cases hb₀)
          (fun k hk _ hnone => by
            dsimp only [fixBranch] at hnone ⊢
            by_cases h1 : n + m + k = d.f
            · rw [if_pos h1] at hnone; cases hnone
            · by_cases h2 : n + m + k = n + m + d.j_not
              · rw [if_neg h1, if_pos h2] at hnone; cases hnone
              · rw [if_neg h1, if_neg h2] at hnone ⊢; exact ⟨rfl, fun ho => h2 (by rw [(d.hjnot k hk).mp ho])⟩)
          hxy hu (Nat.lt_succ_self _) hval
      · by_cases heq : u = m₀
        · subst heq; exact hm0_val hval
        · have hlt : m₀ < u := Nat.lt_of_le_of_ne (reaches_le hm0u) (Ne.symm heq)
          have hm0_ge : n + m + j_hit ≤ m₀ := reaches_le hm0_reach
          rcases hu with low | ⟨j, hj, rfl⟩
          · obtain ⟨jm, _, rfl⟩ := hm0L; omega
          · have hfq := jnot_input_lt d hf_not
            have hjq : j ≠ d.j_not := by
              intro e; subst e
              have := reaches_le hm0_reach
              have hm0_not := hm0_reach.trans hm0u
              rcases hm0_not.cases_tail with h | ⟨a, ha_reach, eaq⟩
              · have := hrdf.1.2.1; omega
              · have hm_lt := reaches_le ha_reach
                obtain ⟨k', _, hk', ha_mem, ha_lt⟩ := eaq
                have hk_eq : k' = d.j_not := by omega
                rw [hk_eq] at ha_mem ha_lt
                rw [hf_not] at ha_mem
                simp only [List.mem_singleton] at ha_mem
                omega
            have hjnf : n + m + j ≠ d.f := by omega
            have hfxF : fixBranch d true false (n + m + j) = none := by
              dsimp only [fixBranch]; rw [if_neg hjnf, if_neg (by omega)]
            have hfxB : fixBranch d false true (n + m + j) = none := by
              dsimp only [fixBranch]; rw [if_neg hjnf, if_neg (by omega)]
            obtain ⟨hao, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j hj hjq
            have h_child_ok : ∀ v, v ∈ (gateAt d.E j).inputs → v < n + m + j →
                (¬ reaches (n + m) d.E d.L (n + m + j_hit) v ∧ v ≠ d.f) ∨ reaches (n + m) d.E d.L m₀ v := by
              intro v hv_mem hv_lt
              by_cases hm0v : reaches (n + m) d.E d.L m₀ v
              · exact Or.inr hm0v
              · left
                have evu : edgeTo (n + m) d.E d.L v (n + m + j) := ⟨j, hj, rfl, hv_mem, hv_lt⟩
                refine ⟨fun hhitv => ?_, fun hvf => ?_⟩
                · rcases reaches_total_of_gt d.hsingle hjhit_gt hhitv hm0_reach with h | h
                  · rcases h.cases_head with rfl | ⟨v', evv', hv'm⟩
                    · exact hm0v Relation.ReflTransGen.refl
                    · have hv_eq := d.hsingle v (by have := reaches_le hhitv; omega) v' (n + m + j) evv' evu
                      rw [hv_eq] at hv'm
                      have := reaches_le hv'm
                      omega
                  · exact hm0v h
                · subst hvf
                  rcases hrdf.2 j hj evu with h | h
                  · exact hjq h
                  · exact absurd h (by omega)
            rw [val_gate hfxF, hin] at hval
            rw [val_gate hfxB, hin]
            have ha_ok := ih a ha_lt (parent_live d.hL hj ⟨by rw [hin]; simp, ha_lt⟩) (h_child_ok a (by rw [hin]; simp) ha_lt)
            have hb_ok := ih b hb_lt (parent_live d.hL hj ⟨by rw [hin]; simp, hb_lt⟩) (h_child_ok b (by rw [hin]; simp) hb_lt)
            rcases hao with ho | ho <;>
              simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, List.any, id_eq,
                Bool.and_true, Bool.or_false] at hval ⊢
            · obtain ⟨ha1, hb1⟩ := Bool.and_eq_true_iff.mp hval
              simp [ha_ok ha1, hb_ok hb1]
            · rcases Bool.or_eq_true_iff.mp hval with ha1 | hb1
              · simp [ha_ok ha1]
              · simp [hb_ok hb1]
  obtain ⟨jm, hjmL, rfl⟩ := hm0L
  exact hmain (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    (Or.inr (reaches_root_of_closed d.hL d.huse jm hjmL))

theorem evalT_cut_above {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    {u₀ : ℕ} (hu0_live : live (n + m) d.L u₀) (hu0_nf : u₀ ≠ d.f) (hu0_le : u₀ ≤ n + m + d.r)
    (bf bn : Bool) {x y : ℕ → Bool}
    (hxy : ∀ v < n + m, x v ≠ y v → ¬ reaches (n + m) d.E d.L v d.f ∧ reaches (n + m) d.E d.L v u₀)
    (hu0_eq : value (n + m) d.E x (fixBranch d bf bn) u₀ = value (n + m) d.E y (fixBranch d bf bn) u₀) :
    evalT d bf bn x = evalT d bf bn y := by
  have hmain : ∀ w, live (n + m) d.L w →
      ((∀ v < n + m, reaches (n + m) d.E d.L v w → x v = y v) ∨ reaches (n + m) d.E d.L u₀ w) →
      value (n + m) d.E x (fixBranch d bf bn) w = value (n + m) d.E y (fixBranch d bf bn) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hok
      rcases hok with hagree | hu0w
      · exact value_agree_inputs d.hL (fixBranch d bf bn) hw hagree
      · by_cases heq : w = u₀
        · subst heq; exact hu0_eq
        · have hlt : u₀ < w := Nat.lt_of_le_of_ne (reaches_le hu0w) (Ne.symm heq)
          rcases hw with low | ⟨j, hj, rfl⟩
          · have := reaches_lt_eq low hu0w; omega
          · rcases Option.eq_none_or_eq_some (fixBranch d bf bn (n + m + j)) with hfx | ⟨b, hfx⟩
            · have h_child : ∀ a ∈ (gateAt d.E j).inputs, a < n + m + j →
                  (∀ v < n + m, reaches (n + m) d.E d.L v a → x v = y v) ∨ reaches (n + m) d.E d.L u₀ a := by
                intro a ha halt
                by_cases hu0a : reaches (n + m) d.E d.L u₀ a
                · exact Or.inr hu0a
                · left
                  intro v hv hva
                  by_contra hne
                  obtain ⟨hvnf, hvu0⟩ := hxy v hv hne
                  have eaw : edgeTo (n + m) d.E d.L a (n + m + j) := ⟨j, hj, rfl, ha, halt⟩
                  rcases reaches_total_of_no_f d.hsingle hvnf hvu0 hva with h | h
                  · exact hu0a h
                  · rcases h.cases_head with h0 | ⟨c, eac, hcu0⟩
                    · exact hu0a (h0 ▸ Relation.ReflTransGen.refl)
                    · have hanf : a ≠ d.f := fun e => hvnf (e ▸ hva)
                      have hc_eq := d.hsingle a hanf c (n + m + j) eac eaw
                      rw [hc_eq] at hcu0
                      have := reaches_le hcu0
                      omega
              rw [val_gate hfx, val_gate hfx]
              have hmap : List.map (fun a => if a < n + m + j then value (n + m) d.E x (fixBranch d bf bn) a else false)
                    (gateAt d.E j).inputs =
                  List.map (fun a => if a < n + m + j then value (n + m) d.E y (fixBranch d bf bn) a else false)
                    (gateAt d.E j).inputs := by
                apply List.map_congr_left
                intro a ha
                by_cases halt : a < n + m + j
                · simp only [halt, ↓reduceIte]
                  exact ih a halt (parent_live d.hL hj ⟨ha, halt⟩) (h_child a ha halt)
                · simp only [halt, ↓reduceIte]
              rw [hmap]
            · rw [val_fixed (by omega) hfx, val_fixed (by omega) hfx]
  exact hmain (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    (by
      by_cases hr : reaches (n + m) d.E d.L u₀ (n + m + d.r)
      · exact Or.inr hr
      · left; intro v hv hvr; by_contra hne
        obtain ⟨hvnf, hvu0⟩ := hxy v hv hne
        rcases reaches_total_of_no_f d.hsingle hvnf hvu0 hvr with h | h
        · exact hr h
        · have := reaches_le h; have := le_antisymm hu0_le this; subst this
          exact hr Relation.ReflTransGen.refl)

theorem F_witness_struct {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {w : ℕ} (hwN : w < n + m) (hwnf : ¬ reaches (n + m) d.E d.L w d.f)
    (hF : evalT d true false (sBit w) = true)
    (hB : evalT d false true (sBit w) = false) :
    let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
    let s_hit := n + m + j_hit
    (reaches (n + m) d.E d.L w s_hit ∧ (gateAt d.E j_hit).op = .and) ∨
    ∃ jm ∈ d.L, s_hit < n + m + jm ∧ (gateAt d.E jm).op = .and ∧
      ∃ a b, a ≠ b ∧ a ∈ (gateAt d.E jm).inputs ∧ b ∈ (gateAt d.E jm).inputs ∧
        a < n + m + jm ∧ b < n + m + jm ∧
        reaches (n + m) d.E d.L s_hit a ∧ reaches (n + m) d.E d.L w b ∧
        ¬ reaches (n + m) d.E d.L w a ∧ ¬ reaches (n + m) d.E d.L s_hit b ∧
        value (n + m) d.E (fun _ => false) (fixBranch d false true) a = false ∧
        value (n + m) d.E (sBit w) (fixBranch d true false) b = true ∧
        value (n + m) d.E (fun _ => false) (fixBranch d true false) a = true := by
  classical
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hT100 : evalT d true false (fun _ => false) = false := T_100_false hg d sd hf_not
  have hw_root : reaches (n + m) d.E d.L w (n + m + d.r) := by
    by_contra hnr
    have heq := value_agree_inputs d.hL (fixBranch d true false) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      (x := sBit w) (y := fun _ => false)
      fun v _ hvr => by
        simp only [sBit, decide_eq_false_iff_not]
        intro e; subst e; exact hnr hvr
    change evalT d true false (sBit w) = evalT d true false (fun _ => false) at heq
    rw [hF, hT100] at heq; cases heq
  have hhit_root : reaches (n + m) d.E d.L s_hit (n + m + d.r) :=
    reaches_root_of_closed d.hL d.huse j_hit hrdf.1.1
  let S := (Finset.range (n + m + d.r + 1)).filter fun u =>
    reaches (n + m) d.E d.L w u ∧ reaches (n + m) d.E d.L s_hit u
  have hS_ne : S.Nonempty := ⟨n + m + d.r, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), hw_root, hhit_root⟩⟩
  let m₀ := S.min' hS_ne
  have hm0_mem := Finset.mem_filter.mp (S.min'_mem hS_ne)
  have hm0_le : m₀ ≤ n + m + d.r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm0_mem.1)
  obtain ⟨hw_m0, hhit_m0⟩ := hm0_mem.2
  have hs_le_m0 : s_hit ≤ m₀ := reaches_le hhit_m0
  have hm0_nf : m₀ ≠ d.f := by have := edgeTo_lt hrdf.1.2.2; omega
  have hm0_live : live (n + m) d.L m₀ := reaches_live (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) hhit_m0
  have hm0_gate : ∃ jm ∈ d.L, m₀ = n + m + jm := by
    rcases hm0_live with low | h
    · omega
    · exact h
  obtain ⟨jm, hjmL, hm0_eq⟩ := hm0_gate
  by_cases heq_hit : m₀ = s_hit
  · left
    have hw_hit : reaches (n + m) d.E d.L w s_hit := heq_hit ▸ hw_m0
    refine ⟨hw_hit, ?_⟩
    obtain ⟨hao, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j_hit hrdf.1.1 hrdf.1.2.1
    rcases hao with ho | ho
    · exact ho
    · exfalso
      have hf_in_hit : d.f ∈ (gateAt d.E j_hit).inputs := by
        rcases hrdf.1.2.2 with ⟨k', _, h_eq, hf, _⟩
        have : k' = j_hit := by dsimp only [j_hit]; exact (Nat.add_left_cancel h_eq).symm
        rwa [← this]
      have hf_lt_hit : d.f < s_hit := edgeTo_lt hrdf.1.2.2
      have hsnf : s_hit ≠ d.f := Nat.ne_of_gt hf_lt_hit
      have h_s_true (x : ℕ → Bool) : value (n + m) d.E x (fixBranch d true false) s_hit = true := by
        have hfx : fixBranch d true false s_hit = none := by
          dsimp only [fixBranch]; rw [if_neg hsnf, if_neg (by intro e; apply hrdf.1.2.1; exact Nat.add_left_cancel e)]
        have hff : fixBranch d true false d.f = some true := by
          dsimp only [fixBranch]; rw [if_pos rfl]
        have hfval : value (n + m) d.E x (fixBranch d true false) d.f = true :=
          val_fixed sd.d_N_le_f hff
        change value (n + m) d.E x (fixBranch d true false) (n + m + j_hit) = true
        rw [val_gate hfx, hin]
        rw [hin] at hf_in_hit
        rcases List.mem_pair.mp hf_in_hit with rfl | rfl <;>
          simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.any, id_eq,
            Bool.or_false, hfval, Bool.true_or, Bool.or_true]
      have hcut := evalT_cut_above d (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) hsnf (reaches_le hhit_root)
        true false (x := sBit w) (y := fun _ => false)
        (fun v _ hne => by
          have : v = w := by by_contra hnw; simp [sBit, hnw] at hne
          subst this; exact ⟨hwnf, hw_hit⟩)
        (by rw [h_s_true, h_s_true])
      rw [hF, hT100] at hcut; cases hcut
  · right
    have hs_lt_m0 : s_hit < m₀ := Nat.lt_of_le_of_ne hs_le_m0 (Ne.symm heq_hit)
    have hjm_ne : jm ≠ d.j_not := by
      intro e; subst e
      rcases hhit_m0.cases_tail with h | ⟨a, ha, eaq⟩
      · exact heq_hit h
      · obtain ⟨k', _, hk', ha_mem, ha_lt⟩ := eaq
        have hk_eq : k' = d.j_not := by omega
        rw [hk_eq] at ha_mem ha_lt
        rw [hf_not] at ha_mem
        simp only [List.mem_singleton] at ha_mem
        have := reaches_le ha; have := edgeTo_lt hrdf.1.2.2; omega
    obtain ⟨hao, u, v, huv, hin, hu_lt, hv_lt⟩ := d.hother_two jm hjmL hjm_ne
    have hfxF : fixBranch d true false m₀ = none := by
      rw [hm0_eq]; dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
    have hfxB : fixBranch d false true m₀ = none := by
      rw [hm0_eq]; dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
    have h_m0_split : ∃ c_h ∈ (gateAt d.E jm).inputs, ∃ c_w ∈ (gateAt d.E jm).inputs,
        c_h ≠ c_w ∧ c_h < n + m + jm ∧ c_w < n + m + jm ∧
        reaches (n + m) d.E d.L s_hit c_h ∧ reaches (n + m) d.E d.L w c_w := by
      rcases hhit_m0.cases_tail with h | ⟨a₁, ha₁, ⟨k₁, _, hk1, ha1_mem, ha1_lt⟩⟩
      · exact False.elim (heq_hit h)
      · rcases hw_m0.cases_tail with h | ⟨a₂, ha₂, ⟨k₂, _, hk2, ha2_mem, ha2_lt⟩⟩
        · omega
        · have hk1_eq : k₁ = jm := by omega
          have hk2_eq : k₂ = jm := by omega
          rw [hk1_eq] at ha1_mem ha1_lt
          rw [hk2_eq] at ha2_mem ha2_lt
          have ha12 : a₁ ≠ a₂ := by
            intro e; subst e
            have hlt1 : a₁ < n + m + d.r + 1 := by omega
            have := S.min'_le a₁ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt1, ha₂, ha₁⟩)
            omega
          exact ⟨a₁, ha1_mem, a₂, ha2_mem, ha12, ha1_lt, ha2_lt, ha₁, ha₂⟩
    obtain ⟨a, ha_mem, b, hb_mem, hab, ha_lt, hb_lt, hsa, hwb⟩ := h_m0_split
    have hnw_a : ¬ reaches (n + m) d.E d.L w a := by
      intro hwa
      have ha_lt_r : a < n + m + d.r + 1 := by omega
      have := S.min'_le a (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_r, hwa, hsa⟩)
      omega
    have hns_b : ¬ reaches (n + m) d.E d.L s_hit b := by
      intro hsb
      have hb_lt_r : b < n + m + d.r + 1 := by omega
      have := S.min'_le b (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt_r, hwb, hsb⟩)
      omega
    have h_a_agree (bf bn : Bool) :
        value (n + m) d.E (sBit w) (fixBranch d bf bn) a =
        value (n + m) d.E (fun _ => false) (fixBranch d bf bn) a := by
      apply value_agree_inputs d.hL (fixBranch d bf bn) (parent_live d.hL hjmL ⟨ha_mem, ha_lt⟩)
      intro z _ hza
      simp only [sBit, decide_eq_false_iff_not]
      intro e; subst e; exact hnw_a hza
    have h_m0_ne : value (n + m) d.E (sBit w) (fixBranch d true false) m₀ ≠
        value (n + m) d.E (fun _ => false) (fixBranch d true false) m₀ := by
      intro heq
      have hcut := evalT_cut_above d hm0_live hm0_nf hm0_le true false
        (x := sBit w) (y := fun _ => false)
        (fun z _ hne => by
          have : z = w := by by_contra hnw; simp [sBit, hnw] at hne
          subst this; exact ⟨hwnf, hw_m0⟩)
        heq
      rw [hF, hT100] at hcut; cases hcut
    have h_m0_mono : value (n + m) d.E (fun _ => false) (fixBranch d true false) m₀ = true →
        value (n + m) d.E (sBit w) (fixBranch d true false) m₀ = true :=
      eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d true false) (fix₁ := fixBranch d true false)
        (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
        (fun k hk _ hnone => ⟨hnone, fun ho => by
          dsimp only [fixBranch] at hnone
          by_cases h1 : n + m + k = d.f
          · rw [if_pos h1] at hnone; cases hnone
          · rw [if_neg h1, if_pos (by rw [(d.hjnot k hk).mp ho])] at hnone; cases hnone⟩)
        (fun _ _ hf => by cases hf) hm0_live (Nat.lt_succ_self _)
    have h_m0_0F : value (n + m) d.E (fun _ => false) (fixBranch d true false) m₀ = false := by
      cases h0 : value (n + m) d.E (fun _ => false) (fixBranch d true false) m₀ with
      | false => rfl
      | true => exact False.elim (h_m0_ne ((h_m0_mono h0).trans h0.symm))
    have h_m0_wF : value (n + m) d.E (sBit w) (fixBranch d true false) m₀ = true := by
      cases hw : value (n + m) d.E (sBit w) (fixBranch d true false) m₀ with
      | true => rfl
      | false => exact False.elim (h_m0_ne (hw.trans h_m0_0F.symm))
    have hbnf : b ≠ d.f := fun e => hwnf (e ▸ hwb)
    have hb_F_le_B : value (n + m) d.E (sBit w) (fixBranch d true false) b = true →
        value (n + m) d.E (sBit w) (fixBranch d false true) b = true := by
      intro hbF
      rw [value_indep_bf_of_no_jhit d hf_not (sBit w) true false false b
        (parent_live d.hL hjmL ⟨hb_mem, hb_lt⟩) hbnf hns_b] at hbF
      exact eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d false false) (fix₁ := fixBranch d false true)
        (fun k _ _ b₀ hb₀ => by
          dsimp only [fixBranch] at hb₀ ⊢
          by_cases h1 : n + m + k = d.f
          · rw [if_pos h1] at hb₀ ⊢; cases hb₀; exact ⟨false, rfl, id⟩
          · by_cases h2 : n + m + k = n + m + d.j_not
            · rw [if_neg h1, if_pos h2] at hb₀ ⊢; cases hb₀; exact ⟨true, rfl, fun e => by cases e⟩
            · rw [if_neg h1, if_neg h2] at hb₀; cases hb₀)
        (fun k hk _ hnone => by
          dsimp only [fixBranch] at hnone ⊢
          by_cases h1 : n + m + k = d.f
          · rw [if_pos h1] at hnone; cases hnone
          · by_cases h2 : n + m + k = n + m + d.j_not
            · rw [if_neg h1, if_pos h2] at hnone; cases hnone
            · rw [if_neg h1, if_neg h2] at hnone ⊢; exact ⟨rfl, fun ho => h2 (by rw [(d.hjnot k hk).mp ho])⟩)
        (fun _ _ h => h) (parent_live d.hL hjmL ⟨hb_mem, hb_lt⟩) (Nat.lt_succ_self _) hbF
    have h_pair_eq : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
      rw [hin] at ha_mem hb_mem
      rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
        rcases List.mem_pair.mp hb_mem with rfl | rfl
      · exact False.elim (hab rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact False.elim (hab rfl)
    have hm_eval (x : ℕ → Bool) (bf bn : Bool) (hfix : fixBranch d bf bn m₀ = none) :
        value (n + m) d.E x (fixBranch d bf bn) m₀ =
        (gateAt d.E jm).op.eval
          [value (n + m) d.E x (fixBranch d bf bn) a,
           value (n + m) d.E x (fixBranch d bf bn) b] := by
      rw [hm0_eq, val_gate (hm0_eq ▸ hfix), hin]
      rcases h_pair_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hao with ho | ho <;>
        simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, List.any, id_eq,
          Bool.and_true, Bool.or_false] <;>
        first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _
    have ho_and : (gateAt d.E jm).op = .and := by
      rcases hao with ho | ho
      · exact ho
      · exfalso
        have h0F := h_m0_0F; have hwF := h_m0_wF
        rw [hm_eval _ true false hfxF, ho] at h0F hwF
        simp only [GateOp.eval, List.any, id_eq, Bool.or_false, Bool.or_eq_false_iff] at h0F
        rw [h_a_agree, h0F.1] at hwF
        simp only [GateOp.eval, List.any, id_eq, Bool.or_false, Bool.false_or] at hwF
        have hbB := hb_F_le_B hwF
        have hmB : value (n + m) d.E (sBit w) (fixBranch d false true) m₀ = true := by
          rw [hm_eval _ false true hfxB, ho]
          simp only [GateOp.eval, List.any, id_eq, Bool.or_false, hbB, Bool.or_true]
        have hmono := value_mono_node_above d sd hf_not ⟨jm, hjmL, hm0_eq⟩ hhit_m0
          (x := sBit w) (y := sBit w) (fun _ _ h => h) (fun _ => hmB) hF
        rw [hmono] at hB; cases hB
    have hwF := h_m0_wF; have h0F := h_m0_0F
    rw [hm_eval _ true false hfxF, ho_and] at hwF h0F
    simp only [GateOp.eval, List.all, id_eq, Bool.and_true, Bool.and_eq_true] at hwF
    have haF : value (n + m) d.E (fun _ => false) (fixBranch d true false) a = true := by
      rw [← h_a_agree]; exact hwF.1
    have hbF : value (n + m) d.E (sBit w) (fixBranch d true false) b = true := hwF.2
    have haB0 : value (n + m) d.E (fun _ => false) (fixBranch d false true) a = false := by
      by_contra h1
      have haBt := Bool.eq_true_of_not_eq_false h1
      have haBw : value (n + m) d.E (sBit w) (fixBranch d false true) a = true := by
        rw [h_a_agree]; exact haBt
      have hbBw := hb_F_le_B hbF
      have hmB : value (n + m) d.E (sBit w) (fixBranch d false true) m₀ = true := by
        rw [hm_eval _ false true hfxB, ho_and]
        simp only [GateOp.eval, List.all, id_eq, Bool.and_true, haBw, hbBw, Bool.and_self]
      have hmono := value_mono_node_above d sd hf_not ⟨jm, hjmL, hm0_eq⟩ hhit_m0
        (x := sBit w) (y := sBit w) (fun _ _ h => h) (fun _ => hmB) hF
      rw [hmono] at hB; cases hB
    refine ⟨jm, hjmL, hm0_eq ▸ hs_lt_m0, ho_and, a, b, hab, ha_mem, hb_mem, hm0_eq ▸ ha_lt,
      hm0_eq ▸ hb_lt, hsa, hwb, hnw_a, hns_b, haB0, hbF, haF⟩

theorem pair_other_eq {x y₁ y₂ u v : ℕ} (hy1 : x ≠ y₁) (hy2 : x ≠ y₂)
    (hx : x = u ∨ x = v) (h1 : y₁ = u ∨ y₁ = v) (h2 : y₂ = u ∨ y₂ = v) : y₁ = y₂ := by
  rcases hx with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first | rfl | exact absurd rfl hy1 | exact absurd rfl hy2

theorem value_agree_of_no_f_q {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (x : ℕ → Bool) (bf₀ bf₁ bn₀ bn₁ : Bool) :
    ∀ w, live (n + m) d.L w → ¬ reaches (n + m) d.E d.L d.f w →
      ¬ reaches (n + m) d.E d.L (n + m + d.j_not) w →
      value (n + m) d.E x (fixBranch d bf₀ bn₀) w =
        value (n + m) d.E x (fixBranch d bf₁ bn₁) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnf hnq
    rcases hw with low | ⟨j, hj, rfl⟩
    · rw [val_raw low, val_raw low]
    · have hne_f : n + m + j ≠ d.f := fun e => hnf (by rw [← e]; exact .refl)
      have hne_q : n + m + j ≠ n + m + d.j_not := fun e => hnq (by rw [← e]; exact .refl)
      have hfx1 : fixBranch d bf₀ bn₀ (n + m + j) = none := by
        dsimp only [fixBranch]; rw [if_neg hne_f, if_neg hne_q]
      have hfx2 : fixBranch d bf₁ bn₁ (n + m + j) = none := by
        dsimp only [fixBranch]; rw [if_neg hne_f, if_neg hne_q]
      rw [val_gate hfx1, val_gate hfx2]
      have hmap : List.map (fun a => if a < n + m + j then value (n + m) d.E x (fixBranch d bf₀ bn₀) a else false)
            (gateAt d.E j).inputs =
          List.map (fun a => if a < n + m + j then value (n + m) d.E x (fixBranch d bf₁ bn₁) a else false)
            (gateAt d.E j).inputs := by
        apply List.map_congr_left
        intro a ha
        by_cases halt : a < n + m + j
        · simp only [halt, ↓reduceIte]
          have eau : edgeTo (n + m) d.E d.L a (n + m + j) := ⟨j, hj, rfl, ha, halt⟩
          exact ih a halt (parent_live d.hL hj ⟨ha, halt⟩)
            (fun h => hnf (h.tail eau)) (fun h => hnq (h.tail eau))
        · simp only [halt, ↓reduceIte]
      rw [hmap]

theorem q_not_below_killed_node {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {m₀ : ℕ} (hm0L : ∃ jm ∈ d.L, m₀ = n + m + jm)
    (hqm : reaches (n + m) d.E d.L (n + m + d.j_not) m₀)
    (hhitm : reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) m₀)
    {x : ℕ → Bool}
    (hmB : value (n + m) d.E x (fixBranch d false true) m₀ = false)
    (hB : evalT d false true x = true) :
    evalT d true false x = true := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  have hrdf := reaches_from_d_f d hf_not
  have hfq := jnot_input_lt d hf_not
  have hjhit_gt : d.f < n + m + j_hit := edgeTo_lt hrdf.1.2.2
  have hmain : ∀ u, live (n + m) d.L u →
      ((¬ reaches (n + m) d.E d.L d.f u ∧ ¬ reaches (n + m) d.E d.L (n + m + d.j_not) u) ∨
        reaches (n + m) d.E d.L m₀ u) →
      value (n + m) d.E x (fixBranch d false true) u = true →
      value (n + m) d.E x (fixBranch d true false) u = true := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu hok hval
      rcases hok with ⟨hnf, hnq⟩ | hm0u
      · rw [← value_agree_of_no_f_q d x false true true false u hu hnf hnq]; exact hval
      · by_cases heq : u = m₀
        · subst heq; rw [hmB] at hval; cases hval
        · have hlt : m₀ < u := Nat.lt_of_le_of_ne (reaches_le hm0u) (Ne.symm heq)
          rcases hu with low | ⟨j, hj, rfl⟩
          · obtain ⟨jm, _, rfl⟩ := hm0L; omega
          · have hqm_le := reaches_le hqm
            have hjq : j ≠ d.j_not := by omega
            have hjnf : n + m + j ≠ d.f := by omega
            have hfxB : fixBranch d false true (n + m + j) = none := by
              dsimp only [fixBranch]; rw [if_neg hjnf, if_neg (by omega)]
            have hfxF : fixBranch d true false (n + m + j) = none := by
              dsimp only [fixBranch]; rw [if_neg hjnf, if_neg (by omega)]
            obtain ⟨hao, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j hj hjq
            have h_child_ok : ∀ v, v ∈ (gateAt d.E j).inputs → v < n + m + j →
                (¬ reaches (n + m) d.E d.L d.f v ∧ ¬ reaches (n + m) d.E d.L (n + m + d.j_not) v) ∨
                  reaches (n + m) d.E d.L m₀ v := by
              intro v hv_mem hv_lt
              by_cases hm0v : reaches (n + m) d.E d.L m₀ v
              · exact Or.inr hm0v
              · left
                have evu : edgeTo (n + m) d.E d.L v (n + m + j) := ⟨j, hj, rfl, hv_mem, hv_lt⟩
                have hno_from (s : ℕ) (hsgt : d.f < s) (hsm : reaches (n + m) d.E d.L s m₀) :
                    ¬ reaches (n + m) d.E d.L s v := by
                  intro hsv
                  rcases reaches_total_of_gt d.hsingle hsgt hsv hsm with h | h
                  · rcases h.cases_head with rfl | ⟨v', evv', hv'm⟩
                    · exact hm0v Relation.ReflTransGen.refl
                    · have hv_eq := d.hsingle v (by have := reaches_le hsv; omega) v' (n + m + j) evv' evu
                      rw [hv_eq] at hv'm
                      have := reaches_le hv'm; omega
                  · exact hm0v h
                have hnqv := hno_from (n + m + d.j_not) hfq hqm
                have hnhv := hno_from (n + m + j_hit) hjhit_gt hhitm
                refine ⟨fun hfv => ?_, hnqv⟩
                rcases hfv.cases_head with rfl | ⟨s', efs, hs'v⟩
                · rcases hrdf.2 j hj evu with h | h
                  · exact hjq h
                  · have : j = j_hit := by simp only [j_hit]; exact h
                    have := reaches_le hhitm; omega
                · obtain ⟨j', hj', hse, hemem, helt⟩ := efs
                  subst hse
                  have efs' : edgeTo (n + m) d.E d.L d.f (n + m + j') := ⟨j', hj', rfl, hemem, helt⟩
                  rcases hrdf.2 j' hj' efs' with h | h
                  · exact hnqv (h ▸ hs'v)
                  · have hj'eq : j' = j_hit := by simp only [j_hit]; exact h
                    exact hnhv (hj'eq ▸ hs'v)
            rw [val_gate hfxB, hin] at hval
            rw [val_gate hfxF, hin]
            have ha_ok := ih a ha_lt (parent_live d.hL hj ⟨by rw [hin]; simp, ha_lt⟩) (h_child_ok a (by rw [hin]; simp) ha_lt)
            have hb_ok := ih b hb_lt (parent_live d.hL hj ⟨by rw [hin]; simp, hb_lt⟩) (h_child_ok b (by rw [hin]; simp) hb_lt)
            rcases hao with ho | ho <;>
              simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, List.any, id_eq,
                Bool.and_true, Bool.or_false] at hval ⊢
            · obtain ⟨ha1, hb1⟩ := Bool.and_eq_true_iff.mp hval
              simp [ha_ok ha1, hb_ok hb1]
            · rcases Bool.or_eq_true_iff.mp hval with ha1 | hb1
              · simp [ha_ok ha1]
              · simp [hb_ok hb1]
  obtain ⟨jm, hjmL, rfl⟩ := hm0L
  exact hmain (n + m + d.r) (Or.inr ⟨d.r, d.hrL, rfl⟩)
    (Or.inr (reaches_root_of_closed d.hL d.huse jm hjmL)) hB

theorem contradict_earlier_witness {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {w₁ : ℕ} (h1nf : ¬ reaches (n + m) d.E d.L w₁ d.f)
    (h1F : evalT d true false (sBit w₁) = true)
    {jm : ℕ} (hjmL : jm ∈ d.L)
    (hs_lt : n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁) < n + m + jm)
    (ho : (gateAt d.E jm).op = .and)
    {a b : ℕ} (hab : a ≠ b) (ha_mem : a ∈ (gateAt d.E jm).inputs) (hb_mem : b ∈ (gateAt d.E jm).inputs)
    (ha_lt : a < n + m + jm) (hb_lt : b < n + m + jm)
    (hsa : reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) a)
    (hnsb : ¬ reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) b)
    (haF : value (n + m) d.E (fun _ => false) (fixBranch d true false) a = true)
    (hb0 : value (n + m) d.E (fun _ => false) (fixBranch d true false) b = false)
    (hw1a : reaches (n + m) d.E d.L w₁ a) : False := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hjhit_gt : d.f < s_hit := edgeTo_lt hrdf.1.2.2
  have hn_w1b : ¬ reaches (n + m) d.E d.L w₁ b := by
    intro hw1b
    rcases reaches_total_of_no_f d.hsingle h1nf hw1a hw1b with h | h
    · rcases h.cases_head with rfl | ⟨c, eac, hcb⟩
      · exact hab rfl
      · have hanf : a ≠ d.f := by have := reaches_le hsa; omega
        have hc_eq := d.hsingle a hanf c (n + m + jm) eac ⟨jm, hjmL, rfl, ha_mem, ha_lt⟩
        rw [hc_eq] at hcb; have := reaches_le hcb; omega
    · rcases h.cases_head with rfl | ⟨c, ebc, hca⟩
      · exact hab rfl
      · have hbnf : b ≠ d.f := fun e => h1nf (e ▸ hw1b)
        have hc_eq := d.hsingle b hbnf c (n + m + jm) ebc ⟨jm, hjmL, rfl, hb_mem, hb_lt⟩
        rw [hc_eq] at hca; have := reaches_le hca; omega
  have hb_eq : value (n + m) d.E (sBit w₁) (fixBranch d true false) b = false :=
    (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hjmL ⟨hb_mem, hb_lt⟩)
      (x := sBit w₁) (y := fun _ => false)
      fun v _ hvb => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hn_w1b hvb).trans hb0
  have hm0_nf : n + m + jm ≠ d.f := by omega
  have hjq : jm ≠ d.j_not := by
    intro e; subst e
    have hsa' := hsa.tail ⟨d.j_not, d.hjnotL, rfl, ha_mem, ha_lt⟩
    rcases hsa'.cases_tail with h | ⟨u, hu, eu⟩
    · exact absurd h (by omega)
    · obtain ⟨k', _, hk', hu_mem, _⟩ := eu
      have : k' = d.j_not := by omega
      rw [this, hf_not] at hu_mem; simp only [List.mem_singleton] at hu_mem
      have := reaches_le hu; omega
  have hfxF : fixBranch d true false (n + m + jm) = none := by
    dsimp only [fixBranch]; rw [if_neg hm0_nf, if_neg (by omega)]
  have ha_eq : value (n + m) d.E (sBit w₁) (fixBranch d true false) a =
      value (n + m) d.E (fun _ => false) (fixBranch d true false) a :=
    eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d true false) (fix₁ := fixBranch d true false)
      (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
      (fun k hk _ hnone => ⟨hnone, fun ho' => by
        dsimp only [fixBranch] at hnone
        by_cases h1 : n + m + k = d.f
        · rw [if_pos h1] at hnone; cases hnone
        · rw [if_neg h1, if_pos (by rw [(d.hjnot k hk).mp ho'])] at hnone; cases hnone⟩)
      (fun _ _ hf => by cases hf) (parent_live d.hL hjmL ⟨ha_mem, ha_lt⟩) (Nat.lt_succ_self _) haF
    |> fun h1 => h1.trans haF.symm
  have hm0_f1 : value (n + m) d.E (sBit w₁) (fixBranch d true false) (n + m + jm) = false := by
    rw [val_gate hfxF]
    obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm hjmL hjq
    rw [hin] at ha_mem hb_mem ⊢
    rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
      rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
      simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, id_eq,
        Bool.and_true, hb_eq, Bool.and_false, Bool.false_and] at *
  have hm0_f0 : value (n + m) d.E (fun _ => false) (fixBranch d true false) (n + m + jm) = false := by
    rw [val_gate hfxF]
    obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm hjmL hjq
    rw [hin] at ha_mem hb_mem ⊢
    rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
      rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
      simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, id_eq,
        Bool.and_true, hb0, Bool.and_false, Bool.false_and] at *
  have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) hm0_nf
    (reaches_le (reaches_root_of_closed d.hL d.huse jm hjmL)) true false
    (x := sBit w₁) (y := fun _ => false)
    (fun v _ hne => by
      have : v = w₁ := by by_contra hnw; simp [sBit, hnw] at hne
      subst this; exact ⟨h1nf, Relation.ReflTransGen.tail hw1a ⟨jm, hjmL, rfl, ha_mem, ha_lt⟩⟩)
    (hm0_f1.trans hm0_f0.symm)
  rw [h1F, T_100_false hg d sd hf_not] at hcut; cases hcut

theorem step_to_and_child {n m : ℕ} {A : Fin n → Fin m → Bool} (d : CollisionData n m A)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {m₁ jm : ℕ} (hjmL : jm ∈ d.L) (hs1 : reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) m₁)
    (hm12 : m₁ < n + m + jm) (hrm : reaches (n + m) d.E d.L m₁ (n + m + jm))
    {a b : ℕ} (hab : a ≠ b) (ha_mem : a ∈ (gateAt d.E jm).inputs) (hb_mem : b ∈ (gateAt d.E jm).inputs)
    (ha_lt : a < n + m + jm) (hb_lt : b < n + m + jm)
    (hsa : reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) a)
    (hnsb : ¬ reaches (n + m) d.E d.L (n + m + (if d.j₁ = d.j_not then d.j₂ else d.j₁)) b) :
    reaches (n + m) d.E d.L m₁ a := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hjhit_gt : d.f < s_hit := edgeTo_lt hrdf.1.2.2
  rcases hrm.cases_tail with h | ⟨c, hmc, ⟨k', _, hk', hc_mem, hc_lt⟩⟩
  · omega
  · have : k' = jm := by omega
    rw [this] at hc_mem hc_lt
    have hs_c := hs1.trans hmc
    have hc_eq : c = a ∨ c = b := by
      have hne : jm ≠ d.j_not := by
        intro e; subst e
        have := hs_c.tail ⟨d.j_not, d.hjnotL, rfl, hc_mem, hc_lt⟩
        rcases this.cases_tail with h0 | ⟨u, hu, eu⟩
        · have := reaches_le hs1; omega
        · obtain ⟨ku, _, hku, hum, _⟩ := eu
          have : ku = d.j_not := by omega
          rw [this, hf_not] at hum; simp only [List.mem_singleton] at hum
          have := reaches_le hu; omega
      obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm hjmL hne
      rw [hin] at hc_mem ha_mem hb_mem
      rcases List.mem_pair.mp hc_mem with rfl | rfl <;>
        rcases List.mem_pair.mp ha_mem with eu | eu <;>
        rcases List.mem_pair.mp hb_mem with ev | ev
      all_goals first
        | exact Or.inl eu.symm
        | exact Or.inr ev.symm
        | exact False.elim (hab (eu.trans ev.symm))
    rcases hc_eq with rfl | rfl
    · exact hmc
    · exact False.elim (hnsb hs_c)

theorem no_two_F_witnesses {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {w₁ w₂ : ℕ} (hw1N : w₁ < n + m) (hw2N : w₂ < n + m) (hne : w₁ ≠ w₂)
    (h1nf : ¬ reaches (n + m) d.E d.L w₁ d.f) (h2nf : ¬ reaches (n + m) d.E d.L w₂ d.f)
    (h1F : evalT d true false (sBit w₁) = true) (h2F : evalT d true false (sBit w₂) = true)
    (h1B : evalT d false true (sBit w₁) = false) (h2B : evalT d false true (sBit w₂) = false)
    {y : ℕ → Bool} (hy : ∀ v < n + m, y v = true → v ≠ w₁ ∧ v ≠ w₂ ∧ ¬ reaches (n + m) d.E d.L v d.f) :
    evalT d false true (fun v => sBit w₁ v || y v) =
      evalT d false true (fun v => sBit w₂ v || y v) := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hjhit_gt : d.f < s_hit := edgeTo_lt hrdf.1.2.2
  have hs1 := F_witness_struct hg d sd hf_not hw1N h1nf h1F h1B
  have hs2 := F_witness_struct hg d sd hf_not hw2N h2nf h2F h2B
  change (reaches (n + m) d.E d.L w₁ s_hit ∧ (gateAt d.E j_hit).op = .and) ∨ _ at hs1
  change (reaches (n + m) d.E d.L w₂ s_hit ∧ (gateAt d.E j_hit).op = .and) ∨ _ at hs2
  have hs_hit_and_kill : (gateAt d.E j_hit).op = .and → ∀ x : ℕ → Bool,
      value (n + m) d.E x (fixBranch d false true) s_hit = false := by
    intro ho x
    have hf_in : d.f ∈ (gateAt d.E j_hit).inputs := by
      rcases hrdf.1.2.2 with ⟨k', _, h_eq, hf, _⟩
      have : k' = j_hit := by dsimp only [j_hit]; exact (Nat.add_left_cancel h_eq).symm
      rwa [← this]
    have hsnf : s_hit ≠ d.f := by omega
    have hfx : fixBranch d false true s_hit = none := by
      dsimp only [fixBranch]; rw [if_neg hsnf, if_neg (by intro e; apply hrdf.1.2.1; exact Nat.add_left_cancel e)]
    have hff : value (n + m) d.E x (fixBranch d false true) d.f = false :=
      val_fixed sd.d_N_le_f (by dsimp only [fixBranch]; rw [if_pos rfl])
    obtain ⟨_, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j_hit hrdf.1.1 hrdf.1.2.1
    change value (n + m) d.E x (fixBranch d false true) (n + m + j_hit) = false
    rw [val_gate hfx, hin]
    rw [hin] at hf_in
    rcases List.mem_pair.mp hf_in with rfl | rfl <;>
      simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, id_eq,
        Bool.and_true, hff, Bool.false_and, Bool.and_false]
  rcases hs1 with ⟨hw1_hit, ho1⟩ | ⟨j₁, hj1L, hs1_lt, ho1, a₁, b₁, hab1, ha1_mem, hb1_mem, ha1_lt, hb1_lt, hs_a1, hw1_b1, hnw1_a1, hns_b1, ha1B0, hb1F, ha1F⟩
  · rcases hs2 with ⟨hw2_hit, _⟩ | ⟨j₂, hj2L, hs2_lt, ho2, a₂, b₂, hab2, ha2_mem, hb2_mem, ha2_lt, hb2_lt, hs_a2, hw2_b2, hnw2_a2, hns_b2, ha2B0, hb2F, ha2F⟩
    · refine evalT_cut_above d (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) (by omega)
        (reaches_le (reaches_root_of_closed d.hL d.huse j_hit hrdf.1.1)) false true
        (fun v _ hne => by
          by_cases h1 : v = w₁
          · subst h1; exact ⟨h1nf, hw1_hit⟩
          · by_cases h2 : v = w₂
            · subst h2; exact ⟨h2nf, hw2_hit⟩
            · exfalso; apply hne; simp [sBit, h1, h2])
        (by rw [hs_hit_and_kill ho1, hs_hit_and_kill ho1])
    · have hj2_ne : j₂ ≠ d.j_not := by
        intro e; subst e
        have := hs_a2.tail ⟨d.j_not, d.hjnotL, rfl, ha2_mem, ha2_lt⟩
        rcases this.cases_tail with h | ⟨u, hu, eu⟩
        · exact absurd h (by omega)
        · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
          rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
      have hb2_0 : value (n + m) d.E (fun _ => false) (fixBranch d true false) b₂ = false := by
        by_contra h1
        have hbt := Bool.eq_true_of_not_eq_false h1
        have hfx : fixBranch d true false (n + m + j₂) = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two j₂ hj2L hj2_ne
        have hm0_t : value (n + m) d.E (fun _ => false) (fixBranch d true false) (n + m + j₂) = true := by
          rw [val_gate hfx, hin]
          rw [hin] at ha2_mem hb2_mem
          rcases List.mem_pair.mp ha2_mem with rfl | rfl <;>
            rcases List.mem_pair.mp hb2_mem with rfl | rfl <;>
            first | exact False.elim (hab2 rfl) | simp [GateOp.eval, ho2, ha2_lt, hb2_lt, ha2F, hbt]
        have hcut := evalT_cut_above d (Or.inr ⟨j₂, hj2L, rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse j₂ hj2L)) true false
          (x := sBit w₂) (y := fun _ => false)
          (fun v _ hnev => by
            have : v = w₂ := by by_contra hnw; simp [sBit, hnw] at hnev
            subst this; exact ⟨h2nf, Relation.ReflTransGen.tail hw2_b2 ⟨j₂, hj2L, rfl, hb2_mem, hb2_lt⟩⟩)
          (by
            have hm2_w : value (n + m) d.E (sBit w₂) (fixBranch d true false) (n + m + j₂) = true := by
              have ha2w : value (n + m) d.E (sBit w₂) (fixBranch d true false) a₂ = true :=
                (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hj2L ⟨ha2_mem, ha2_lt⟩)
                  (x := sBit w₂) (y := fun _ => false)
                  fun v _ hva => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw2_a2 hva).trans ha2F
              rw [val_gate hfx, hin]
              rw [hin] at ha2_mem hb2_mem
              rcases List.mem_pair.mp ha2_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hb2_mem with rfl | rfl <;>
                first | exact False.elim (hab2 rfl) | simp [GateOp.eval, ho2, ha2_lt, hb2_lt, ha2w, hb2F]
            exact hm2_w.trans hm0_t.symm)
        rw [h2F, T_100_false hg d sd hf_not] at hcut; cases hcut
      exact False.elim (contradict_earlier_witness hg d sd hf_not h1nf h1F hj2L hs2_lt ho2 hab2
        ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hns_b2 ha2F hb2_0 (hw1_hit.trans hs_a2))
  · rcases hs2 with ⟨hw2_hit, _⟩ | ⟨j₂, hj2L, hs2_lt, ho2, a₂, b₂, hab2, ha2_mem, hb2_mem, ha2_lt, hb2_lt, hs_a2, hw2_b2, hnw2_a2, hns_b2, ha2B0, hb2F, ha2F⟩
    · have hj1_ne : j₁ ≠ d.j_not := by
        intro e; subst e
        have := hs_a1.tail ⟨d.j_not, d.hjnotL, rfl, ha1_mem, ha1_lt⟩
        rcases this.cases_tail with h | ⟨u, hu, eu⟩
        · exact absurd h (by omega)
        · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
          rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
      have hb1_0 : value (n + m) d.E (fun _ => false) (fixBranch d true false) b₁ = false := by
        by_contra h1
        have hbt := Bool.eq_true_of_not_eq_false h1
        have hfx : fixBranch d true false (n + m + j₁) = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two j₁ hj1L hj1_ne
        have hm0_t : value (n + m) d.E (fun _ => false) (fixBranch d true false) (n + m + j₁) = true := by
          rw [val_gate hfx, hin]
          rw [hin] at ha1_mem hb1_mem
          rcases List.mem_pair.mp ha1_mem with rfl | rfl <;>
            rcases List.mem_pair.mp hb1_mem with rfl | rfl <;>
            first | exact False.elim (hab1 rfl) | simp [GateOp.eval, ho1, ha1_lt, hb1_lt, ha1F, hbt]
        have hcut := evalT_cut_above d (Or.inr ⟨j₁, hj1L, rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse j₁ hj1L)) true false
          (x := sBit w₁) (y := fun _ => false)
          (fun v _ hnev => by
            have : v = w₁ := by by_contra hnw; simp [sBit, hnw] at hnev
            subst this; exact ⟨h1nf, Relation.ReflTransGen.tail hw1_b1 ⟨j₁, hj1L, rfl, hb1_mem, hb1_lt⟩⟩)
          (by
            have hm1_w : value (n + m) d.E (sBit w₁) (fixBranch d true false) (n + m + j₁) = true := by
              have ha1w : value (n + m) d.E (sBit w₁) (fixBranch d true false) a₁ = true :=
                (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hj1L ⟨ha1_mem, ha1_lt⟩)
                  (x := sBit w₁) (y := fun _ => false)
                  fun v _ hva => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw1_a1 hva).trans ha1F
              rw [val_gate hfx, hin]
              rw [hin] at ha1_mem hb1_mem
              rcases List.mem_pair.mp ha1_mem with rfl | rfl <;>
                rcases List.mem_pair.mp hb1_mem with rfl | rfl <;>
                first | exact False.elim (hab1 rfl) | simp [GateOp.eval, ho1, ha1_lt, hb1_lt, ha1w, hb1F]
            exact hm1_w.trans hm0_t.symm)
        rw [h1F, T_100_false hg d sd hf_not] at hcut; cases hcut
      exact False.elim (contradict_earlier_witness hg d sd hf_not h2nf h2F hj1L hs1_lt ho1 hab1
        ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hns_b1 ha1F hb1_0 (hw2_hit.trans hs_a1))
    · have hs_m1 : reaches (n + m) d.E d.L s_hit (n + m + j₁) :=
        Relation.ReflTransGen.tail hs_a1 ⟨j₁, hj1L, rfl, ha1_mem, ha1_lt⟩
      have hs_m2 : reaches (n + m) d.E d.L s_hit (n + m + j₂) :=
        Relation.ReflTransGen.tail hs_a2 ⟨j₂, hj2L, rfl, ha2_mem, ha2_lt⟩
      have hb0_of_F {w' jm' a' b' : ℕ} (hjm' : jm' ∈ d.L) (hs' : s_hit < n + m + jm')
          (ho' : (gateAt d.E jm').op = .and) (hab' : a' ≠ b')
          (ha'm : a' ∈ (gateAt d.E jm').inputs) (hb'm : b' ∈ (gateAt d.E jm').inputs)
          (ha'lt : a' < n + m + jm') (hb'lt : b' < n + m + jm')
          (hsa' : reaches (n + m) d.E d.L s_hit a') (hw'b : reaches (n + m) d.E d.L w' b')
          (hnw'a : ¬ reaches (n + m) d.E d.L w' a') (ha'F : value (n + m) d.E (fun _ => false) (fixBranch d true false) a' = true)
          (hb'F : value (n + m) d.E (sBit w') (fixBranch d true false) b' = true)
          (hw'nf : ¬ reaches (n + m) d.E d.L w' d.f) (hw'F : evalT d true false (sBit w') = true) :
          value (n + m) d.E (fun _ => false) (fixBranch d true false) b' = false := by
        by_contra h1
        have hbt := Bool.eq_true_of_not_eq_false h1
        have hjm_ne' : jm' ≠ d.j_not := by
          intro e; subst e
          have := hsa'.tail ⟨d.j_not, d.hjnotL, rfl, ha'm, ha'lt⟩
          rcases this.cases_tail with h | ⟨u, hu, eu⟩
          · omega
          · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
            rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
        have hfx : fixBranch d true false (n + m + jm') = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm' hjm' hjm_ne'
        have hm0_t : value (n + m) d.E (fun _ => false) (fixBranch d true false) (n + m + jm') = true := by
          rw [val_gate hfx, hin]; rw [hin] at ha'm hb'm
          rcases List.mem_pair.mp ha'm with rfl | rfl <;>
            rcases List.mem_pair.mp hb'm with rfl | rfl <;>
            first | exact False.elim (hab' rfl) | simp [GateOp.eval, ho', ha'lt, hb'lt, ha'F, hbt]
        have hm_w : value (n + m) d.E (sBit w') (fixBranch d true false) (n + m + jm') = true := by
          have haw : value (n + m) d.E (sBit w') (fixBranch d true false) a' = true :=
            (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hjm' ⟨ha'm, ha'lt⟩)
              (x := sBit w') (y := fun _ => false)
              fun v _ hva => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw'a hva).trans ha'F
          rw [val_gate hfx, hin]; rw [hin] at ha'm hb'm
          rcases List.mem_pair.mp ha'm with rfl | rfl <;>
            rcases List.mem_pair.mp hb'm with rfl | rfl <;>
            first | exact False.elim (hab' rfl) | simp [GateOp.eval, ho', ha'lt, hb'lt, haw, hb'F]
        have hcut := evalT_cut_above d (Or.inr ⟨jm', hjm', rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse jm' hjm')) true false
          (x := sBit w') (y := fun _ => false)
          (fun v _ hnev => by
            have : v = w' := by by_contra hnw; simp [sBit, hnw] at hnev
            subst this; exact ⟨hw'nf, Relation.ReflTransGen.tail hw'b ⟨jm', hjm', rfl, hb'm, hb'lt⟩⟩)
          (hm_w.trans hm0_t.symm)
        rw [hw'F, T_100_false hg d sd hf_not] at hcut; cases hcut
      rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
      · rcases reaches_total_of_gt d.hsingle hjhit_gt hs_m1 hs_m2 with h12 | h21
        · have hm1_a2 := step_to_and_child d hf_not hj2L hs_m1 (by omega) h12 hab2 ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hns_b2
          have hb2_0 := hb0_of_F hj2L hs2_lt ho2 hab2 ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hw2_b2 hnw2_a2 ha2F hb2F h2nf h2F
          exact False.elim (contradict_earlier_witness hg d sd hf_not h1nf h1F hj2L hs2_lt ho2 hab2
            ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hns_b2 ha2F hb2_0
            ((Relation.ReflTransGen.tail hw1_b1 ⟨j₁, hj1L, rfl, hb1_mem, hb1_lt⟩).trans hm1_a2))
        · have := reaches_le h21; omega
      · subst heq
        have ha_eq : a₁ = a₂ := by
          rcases reaches_total_of_gt d.hsingle hjhit_gt hs_a1 hs_a2 with h | h
          · rcases h.cases_head with rfl | ⟨c, ec, hc⟩
            · rfl
            · have hc_eq := d.hsingle a₁ (by have := reaches_le hs_a1; omega) c (n + m + j₁) ec ⟨j₁, hj1L, rfl, ha1_mem, ha1_lt⟩
              rw [hc_eq] at hc; have := reaches_le hc; omega
          · rcases h.cases_head with rfl | ⟨c, ec, hc⟩
            · rfl
            · have hc_eq := d.hsingle a₂ (by have := reaches_le hs_a2; omega) c (n + m + j₁) ec ⟨j₁, hj1L, rfl, ha2_mem, ha2_lt⟩
              rw [hc_eq] at hc; have := reaches_le hc; omega
        subst ha_eq
        have hjq1 : j₁ ≠ d.j_not := by
          intro e; subst e
          have := hs_m1.cases_tail
          rcases this with h | ⟨u, hu, eu⟩
          · omega
          · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
            rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two j₁ hj1L hjq1
        have ha1_mem0 := ha1_mem; have hb1_mem0 := hb1_mem; have hb2_mem0 := hb2_mem
        have hb_eq : b₁ = b₂ := by
          rw [hin] at ha1_mem hb1_mem hb2_mem
          exact pair_other_eq hab1 hab2 (List.mem_pair.mp ha1_mem) (List.mem_pair.mp hb1_mem) (List.mem_pair.mp hb2_mem)
        subst hb_eq
        have hfxB : fixBranch d false true (n + m + j₁) = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        have ha_agree : value (n + m) d.E (fun v => sBit w₁ v || y v) (fixBranch d false true) a₁ =
            value (n + m) d.E (fun v => sBit w₂ v || y v) (fixBranch d false true) a₁ :=
          value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hj1L ⟨ha1_mem0, ha1_lt⟩)
            fun v _ hva => by
              have hnw1 : v ≠ w₁ := fun e => hnw1_a1 (e ▸ hva)
              have hnw2 : v ≠ w₂ := fun e => hnw2_a2 (e ▸ hva)
              simp [sBit, hnw1, hnw2]
        have hb_F_to_B (w' : ℕ) (hb'F : value (n + m) d.E (sBit w') (fixBranch d true false) b₁ = true)
            (hw'nf : ¬ reaches (n + m) d.E d.L w' d.f) (hw'b : reaches (n + m) d.E d.L w' b₁) :
            value (n + m) d.E (fun v => sBit w' v || y v) (fixBranch d false true) b₁ = true := by
          rw [value_indep_bf_of_no_jhit d hf_not (sBit w') true false false b₁
            (parent_live d.hL hj1L ⟨hb1_mem0, hb1_lt⟩) (fun e => hw'nf (e ▸ hw'b)) hns_b1] at hb'F
          exact eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d false false) (fix₁ := fixBranch d false true)
            (fun k _ _ b₀ hb₀ => by
              dsimp only [fixBranch] at hb₀ ⊢
              by_cases h1 : n + m + k = d.f
              · rw [if_pos h1] at hb₀ ⊢; cases hb₀; exact ⟨false, rfl, id⟩
              · by_cases h2 : n + m + k = n + m + d.j_not
                · rw [if_neg h1, if_pos h2] at hb₀ ⊢; cases hb₀; exact ⟨true, rfl, fun e => by cases e⟩
                · rw [if_neg h1, if_neg h2] at hb₀; cases hb₀)
            (fun k hk _ hnone => by
              dsimp only [fixBranch] at hnone ⊢
              by_cases h1 : n + m + k = d.f
              · rw [if_pos h1] at hnone; cases hnone
              · by_cases h2 : n + m + k = n + m + d.j_not
                · rw [if_neg h1, if_pos h2] at hnone; cases hnone
                · rw [if_neg h1, if_neg h2] at hnone ⊢; exact ⟨rfl, fun ho => h2 (by rw [(d.hjnot k hk).mp ho])⟩)
            (fun _ _ h => by simp [h]) (parent_live d.hL hj1L ⟨hb1_mem0, hb1_lt⟩) (Nat.lt_succ_self _) hb'F
        have hb1_t := hb_F_to_B w₁ hb1F h1nf hw1_b1
        have hb2_t := hb_F_to_B w₂ hb2F h2nf hw2_b2
        have hm0_eq : value (n + m) d.E (fun v => sBit w₁ v || y v) (fixBranch d false true) (n + m + j₁) =
            value (n + m) d.E (fun v => sBit w₂ v || y v) (fixBranch d false true) (n + m + j₁) := by
          rw [val_gate hfxB, val_gate hfxB, hin]
          rw [hin] at ha1_mem0 hb1_mem0
          rcases List.mem_pair.mp ha1_mem0 with rfl | rfl <;>
            rcases List.mem_pair.mp hb1_mem0 with rfl | rfl <;>
            first | exact False.elim (hab1 rfl) | simp [GateOp.eval, ho1, ha1_lt, hb1_lt, ha_agree, hb1_t, hb2_t]
        exact evalT_cut_above d (Or.inr ⟨j₁, hj1L, rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse j₁ hj1L)) false true
          (fun v hv hnev => by
            by_cases h1 : v = w₁
            · subst h1; exact ⟨h1nf, Relation.ReflTransGen.tail hw1_b1 ⟨j₁, hj1L, rfl, hb1_mem, hb1_lt⟩⟩
            · by_cases h2 : v = w₂
              · subst h2; exact ⟨h2nf, Relation.ReflTransGen.tail hw2_b2 ⟨j₁, hj1L, rfl, hb1_mem, hb2_lt⟩⟩
              · exfalso; apply hnev; simp [sBit, h1, h2])
          hm0_eq
      · rcases reaches_total_of_gt d.hsingle hjhit_gt hs_m2 hs_m1 with h21 | h12
        · have hm2_a1 := step_to_and_child d hf_not hj1L hs_m2 (by omega) h21 hab1 ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hns_b1
          have hb1_0 := hb0_of_F hj1L hs1_lt ho1 hab1 ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hw1_b1 hnw1_a1 ha1F hb1F h1nf h1F
          exact False.elim (contradict_earlier_witness hg d sd hf_not h2nf h2F hj1L hs1_lt ho1 hab1
            ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hns_b1 ha1F hb1_0
            ((Relation.ReflTransGen.tail hw2_b2 ⟨j₂, hj2L, rfl, hb2_mem, hb2_lt⟩).trans hm2_a1))
        · have := reaches_le h12; omega

theorem F_witness_pair_false {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {w₁ w₂ : ℕ} (hw1N : w₁ < n + m) (hw2N : w₂ < n + m) (hne : w₁ ≠ w₂)
    (h1nf : ¬ reaches (n + m) d.E d.L w₁ d.f) (h2nf : ¬ reaches (n + m) d.E d.L w₂ d.f)
    (h1F : evalT d true false (sBit w₁) = true) (h2F : evalT d true false (sBit w₂) = true)
    (h1B : evalT d false true (sBit w₁) = false) (h2B : evalT d false true (sBit w₂) = false) :
    evalT d false true (pairBit w₁ w₂) = false := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hjhit_gt : d.f < s_hit := edgeTo_lt hrdf.1.2.2
  have hs1 := F_witness_struct hg d sd hf_not hw1N h1nf h1F h1B
  have hs2 := F_witness_struct hg d sd hf_not hw2N h2nf h2F h2B
  change (reaches (n + m) d.E d.L w₁ s_hit ∧ (gateAt d.E j_hit).op = .and) ∨ _ at hs1
  change (reaches (n + m) d.E d.L w₂ s_hit ∧ (gateAt d.E j_hit).op = .and) ∨ _ at hs2
  have hs_hit_and_kill : (gateAt d.E j_hit).op = .and → ∀ x : ℕ → Bool,
      value (n + m) d.E x (fixBranch d false true) s_hit = false := by
    intro ho x
    have hf_in : d.f ∈ (gateAt d.E j_hit).inputs := by
      rcases hrdf.1.2.2 with ⟨k', _, h_eq, hf, _⟩
      have : k' = j_hit := by dsimp only [j_hit]; exact (Nat.add_left_cancel h_eq).symm
      rwa [← this]
    have hsnf : s_hit ≠ d.f := by omega
    have hfx : fixBranch d false true s_hit = none := by
      dsimp only [fixBranch]; rw [if_neg hsnf, if_neg (by intro e; apply hrdf.1.2.1; exact Nat.add_left_cancel e)]
    have hff : value (n + m) d.E x (fixBranch d false true) d.f = false :=
      val_fixed sd.d_N_le_f (by dsimp only [fixBranch]; rw [if_pos rfl])
    obtain ⟨_, a, b, _, hin, ha_lt, hb_lt⟩ := d.hother_two j_hit hrdf.1.1 hrdf.1.2.1
    change value (n + m) d.E x (fixBranch d false true) (n + m + j_hit) = false
    rw [val_gate hfx, hin]
    rw [hin] at hf_in
    rcases List.mem_pair.mp hf_in with rfl | rfl <;>
      simp only [List.map, ha_lt, hb_lt, ↓reduceIte, GateOp.eval, ho, List.all, id_eq,
        Bool.and_true, hff, Bool.false_and, Bool.and_false]
  rcases hs1 with ⟨hw1_hit, ho1⟩ | ⟨j₁, hj1L, hs1_lt, ho1, a₁, b₁, hab1, ha1_mem, hb1_mem, ha1_lt, hb1_lt, hs_a1, hw1_b1, hnw1_a1, hns_b1, ha1B0, hb1F, ha1F⟩
  · refine (evalT_cut_above d (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) (by omega)
      (reaches_le (reaches_root_of_closed d.hL d.huse j_hit hrdf.1.1)) false true
      (x := pairBit w₁ w₂) (y := sBit w₂)
      (fun v _ hne' => by
        have : v = w₁ := by by_contra hn1; simp [pairBit, sBit, hn1] at hne'
        subst this; exact ⟨h1nf, hw1_hit⟩)
      (by rw [hs_hit_and_kill ho1, hs_hit_and_kill ho1])).trans h2B
  · rcases hs2 with ⟨hw2_hit, ho2⟩ | ⟨j₂, hj2L, hs2_lt, ho2, a₂, b₂, hab2, ha2_mem, hb2_mem, ha2_lt, hb2_lt, hs_a2, hw2_b2, hnw2_a2, hns_b2, ha2B0, hb2F, ha2F⟩
    · refine (evalT_cut_above d (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) (by omega)
        (reaches_le (reaches_root_of_closed d.hL d.huse j_hit hrdf.1.1)) false true
        (x := pairBit w₁ w₂) (y := sBit w₁)
        (fun v _ hne' => by
          have : v = w₂ := by by_contra hn2; simp [pairBit, sBit, hn2] at hne'
          subst this; exact ⟨h2nf, hw2_hit⟩)
        (by rw [hs_hit_and_kill ho2, hs_hit_and_kill ho2])).trans h1B
    · have hs_m1 := Relation.ReflTransGen.tail hs_a1 ⟨j₁, hj1L, rfl, ha1_mem, ha1_lt⟩
      have hs_m2 := Relation.ReflTransGen.tail hs_a2 ⟨j₂, hj2L, rfl, ha2_mem, ha2_lt⟩
      have hb0_of_F {w' jm' a' b' : ℕ} (hjm' : jm' ∈ d.L) (hs' : s_hit < n + m + jm')
          (ho' : (gateAt d.E jm').op = .and) (hab' : a' ≠ b')
          (ha'm : a' ∈ (gateAt d.E jm').inputs) (hb'm : b' ∈ (gateAt d.E jm').inputs)
          (ha'lt : a' < n + m + jm') (hb'lt : b' < n + m + jm')
          (hsa' : reaches (n + m) d.E d.L s_hit a') (hw'b : reaches (n + m) d.E d.L w' b')
          (hnw'a : ¬ reaches (n + m) d.E d.L w' a') (ha'F : value (n + m) d.E (fun _ => false) (fixBranch d true false) a' = true)
          (hb'F : value (n + m) d.E (sBit w') (fixBranch d true false) b' = true)
          (hw'nf : ¬ reaches (n + m) d.E d.L w' d.f) (hw'F : evalT d true false (sBit w') = true) :
          value (n + m) d.E (fun _ => false) (fixBranch d true false) b' = false := by
        by_contra h1
        have hbt := Bool.eq_true_of_not_eq_false h1
        have hjm_ne' : jm' ≠ d.j_not := by
          intro e; subst e
          have := hsa'.tail ⟨d.j_not, d.hjnotL, rfl, ha'm, ha'lt⟩
          rcases this.cases_tail with h | ⟨u, hu, eu⟩
          · omega
          · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
            rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
        have hfx : fixBranch d true false (n + m + jm') = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm' hjm' hjm_ne'
        have hm0_t : value (n + m) d.E (fun _ => false) (fixBranch d true false) (n + m + jm') = true := by
          rw [val_gate hfx, hin]; rw [hin] at ha'm hb'm
          rcases List.mem_pair.mp ha'm with rfl | rfl <;>
            rcases List.mem_pair.mp hb'm with rfl | rfl <;>
            first | exact False.elim (hab' rfl) | simp [GateOp.eval, ho', ha'lt, hb'lt, ha'F, hbt]
        have hm_w : value (n + m) d.E (sBit w') (fixBranch d true false) (n + m + jm') = true := by
          have haw : value (n + m) d.E (sBit w') (fixBranch d true false) a' = true :=
            (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hjm' ⟨ha'm, ha'lt⟩)
              (x := sBit w') (y := fun _ => false)
              fun v _ hva => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw'a hva).trans ha'F
          rw [val_gate hfx, hin]; rw [hin] at ha'm hb'm
          rcases List.mem_pair.mp ha'm with rfl | rfl <;>
            rcases List.mem_pair.mp hb'm with rfl | rfl <;>
            first | exact False.elim (hab' rfl) | simp [GateOp.eval, ho', ha'lt, hb'lt, haw, hb'F]
        have hcut := evalT_cut_above d (Or.inr ⟨jm', hjm', rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse jm' hjm')) true false
          (x := sBit w') (y := fun _ => false)
          (fun v _ hnev => by
            have : v = w' := by by_contra hnw; simp [sBit, hnw] at hnev
            subst this; exact ⟨hw'nf, Relation.ReflTransGen.tail hw'b ⟨jm', hjm', rfl, hb'm, hb'lt⟩⟩)
          (hm_w.trans hm0_t.symm)
        rw [hw'F, T_100_false hg d sd hf_not] at hcut; cases hcut
      rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
      · rcases reaches_total_of_gt d.hsingle hjhit_gt hs_m1 hs_m2 with h12 | h21
        · have hm1_a2 := step_to_and_child d hf_not hj2L hs_m1 (by omega) h12 hab2 ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hns_b2
          have hb2_0 := hb0_of_F hj2L hs2_lt ho2 hab2 ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hw2_b2 hnw2_a2 ha2F hb2F h2nf h2F
          exact False.elim (contradict_earlier_witness hg d sd hf_not h1nf h1F hj2L hs2_lt ho2 hab2
            ha2_mem hb2_mem ha2_lt hb2_lt hs_a2 hns_b2 ha2F hb2_0
            ((Relation.ReflTransGen.tail hw1_b1 ⟨j₁, hj1L, rfl, hb1_mem, hb1_lt⟩).trans hm1_a2))
        · have := reaches_le h21; omega
      · subst heq
        have ha_eq : a₁ = a₂ := by
          rcases reaches_total_of_gt d.hsingle hjhit_gt hs_a1 hs_a2 with h | h
          · rcases h.cases_head with rfl | ⟨c, ec, hc⟩
            · rfl
            · have hc_eq := d.hsingle a₁ (by have := reaches_le hs_a1; omega) c (n + m + j₁) ec ⟨j₁, hj1L, rfl, ha1_mem, ha1_lt⟩
              rw [hc_eq] at hc; have := reaches_le hc; omega
          · rcases h.cases_head with rfl | ⟨c, ec, hc⟩
            · rfl
            · have hc_eq := d.hsingle a₂ (by have := reaches_le hs_a2; omega) c (n + m + j₁) ec ⟨j₁, hj1L, rfl, ha2_mem, ha2_lt⟩
              rw [hc_eq] at hc; have := reaches_le hc; omega
        subst ha_eq
        have hjq1 : j₁ ≠ d.j_not := by
          intro e; subst e
          rcases hs_m1.cases_tail with h | ⟨u, hu, eu⟩
          · omega
          · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
            rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
        have hfxB : fixBranch d false true (n + m + j₁) = none := by
          dsimp only [fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
        have ha_pair : value (n + m) d.E (pairBit w₁ w₂) (fixBranch d false true) a₁ = false :=
          (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hj1L ⟨ha1_mem, ha1_lt⟩)
            (x := pairBit w₁ w₂) (y := fun _ => false)
            fun v _ hva => by simp only [pairBit, decide_eq_false_iff_not, not_or]; exact ⟨fun e => hnw1_a1 (e ▸ hva), fun e => hnw2_a2 (e ▸ hva)⟩).trans ha1B0
        have ha_s2 : value (n + m) d.E (sBit w₂) (fixBranch d false true) a₁ = false :=
          (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hj1L ⟨ha1_mem, ha1_lt⟩)
            (x := sBit w₂) (y := fun _ => false)
            fun v _ hva => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw2_a2 hva).trans ha1B0
        obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two j₁ hj1L hjq1
        have hm0_eq : value (n + m) d.E (pairBit w₁ w₂) (fixBranch d false true) (n + m + j₁) =
            value (n + m) d.E (sBit w₂) (fixBranch d false true) (n + m + j₁) := by
          rw [val_gate hfxB, val_gate hfxB, hin]
          rw [hin] at ha1_mem
          rcases List.mem_pair.mp ha1_mem with rfl | rfl <;>
            simp [GateOp.eval, ho1, ha_pair, ha_s2]
        refine (evalT_cut_above d (Or.inr ⟨j₁, hj1L, rfl⟩) (by omega)
          (reaches_le (reaches_root_of_closed d.hL d.huse j₁ hj1L)) false true
          (x := pairBit w₁ w₂) (y := sBit w₂)
          (fun v _ hnev => by
            have : v = w₁ := by by_contra hn1; simp [pairBit, sBit, hn1] at hnev
            subst this; exact ⟨h1nf, Relation.ReflTransGen.tail hw1_b1 ⟨j₁, hj1L, rfl, hb1_mem, hb1_lt⟩⟩)
          hm0_eq).trans h2B
      · rcases reaches_total_of_gt d.hsingle hjhit_gt hs_m2 hs_m1 with h21 | h12
        · have hm2_a1 := step_to_and_child d hf_not hj1L hs_m2 (by omega) h21 hab1 ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hns_b1
          have hb1_0 := hb0_of_F hj1L hs1_lt ho1 hab1 ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hw1_b1 hnw1_a1 ha1F hb1F h1nf h1F
          exact False.elim (contradict_earlier_witness hg d sd hf_not h2nf h2F hj1L hs1_lt ho1 hab1
            ha1_mem hb1_mem ha1_lt hb1_lt hs_a1 hns_b1 ha1F hb1_0
            ((Relation.ReflTransGen.tail hw2_b2 ⟨j₂, hj2L, rfl, hb2_mem, hb2_lt⟩).trans hm2_a1))
        · have := reaches_le h12; omega

theorem F_witness_match_unique {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hf_not : (gateAt d.E d.j_not).inputs = [d.f])
    {w_f w_m w_2 w_c : ℕ} (hfn : w_f < n + m) (hmn : w_m < n + m) (h2n : w_2 < n + m) (hcn : w_c < n + m)
    (hfm : w_f ≠ w_m) (hf2 : w_f ≠ w_2) (hm2 : w_m ≠ w_2)
    (hfnf : ¬ reaches (n + m) d.E d.L w_f d.f) (hmnf : ¬ reaches (n + m) d.E d.L w_m d.f)
    (h2nf : ¬ reaches (n + m) d.E d.L w_2 d.f) (hcnf : ¬ reaches (n + m) d.E d.L w_c d.f)
    (hfF : evalT d true false (sBit w_f) = true) (hfB : evalT d false true (sBit w_f) = false)
    (hmB : evalT d false true (sBit w_m) = false) (hfmB : evalT d false true (pairBit w_f w_m) = true)
    (h2B : evalT d false true (sBit w_2) = false) (h2mB : evalT d false true (pairBit w_2 w_m) = true)
    (hcB : evalT d false true (sBit w_c) = true) (hcF : evalT d true false (sBit w_c) = false) :
    evalT d true false (sBit w_2) = true := by
  let j_hit := if d.j₁ = d.j_not then d.j₂ else d.j₁
  let s_hit := n + m + j_hit
  have hrdf := reaches_from_d_f d hf_not
  have hfq := jnot_input_lt d hf_not
  have hjhit_gt : d.f < s_hit := edgeTo_lt hrdf.1.2.2
  have hsf := F_witness_struct hg d sd hf_not hfn hfnf hfF hfB
  change (reaches (n + m) d.E d.L w_f s_hit ∧ (gateAt d.E j_hit).op = .and) ∨ _ at hsf
  rcases hsf with ⟨hwf_hit, ho⟩ | ⟨jm, hjmL, hs_lt, ho, a, b, hab, ha_mem, hb_mem, ha_lt, hb_lt, hs_a, hwf_b, hnw_a, hns_b, haB0, hwf_bF, haF⟩
  · exfalso
    have hkill : ∀ x, value (n + m) d.E x (fixBranch d false true) s_hit = false := by
      intro x
      have hf_in : d.f ∈ (gateAt d.E j_hit).inputs := by
        rcases hrdf.1.2.2 with ⟨k', _, h_eq, hf, _⟩
        have : k' = j_hit := by dsimp only [j_hit]; exact (Nat.add_left_cancel h_eq).symm
        rwa [← this]
      have hsnf : s_hit ≠ d.f := by omega
      have hfx : fixBranch d false true s_hit = none := by
        dsimp only [fixBranch]; rw [if_neg hsnf, if_neg (by intro e; apply hrdf.1.2.1; exact Nat.add_left_cancel e)]
      have hff : value (n + m) d.E x (fixBranch d false true) d.f = false :=
        val_fixed sd.d_N_le_f (by dsimp only [fixBranch]; rw [if_pos rfl])
      obtain ⟨_, a', b', _, hin, ha', hb'⟩ := d.hother_two j_hit hrdf.1.1 hrdf.1.2.1
      change value (n + m) d.E x (fixBranch d false true) (n + m + j_hit) = false
      rw [val_gate hfx, hin]; rw [hin] at hf_in
      rcases List.mem_pair.mp hf_in with rfl | rfl <;>
        simp [GateOp.eval, ho, ha', hb', hff]
    have hcut := evalT_cut_above d (Or.inr ⟨j_hit, hrdf.1.1, rfl⟩) (by omega)
      (reaches_le (reaches_root_of_closed d.hL d.huse j_hit hrdf.1.1)) false true
      (x := pairBit w_f w_m) (y := sBit w_m)
      (fun v _ hne => by
        have : v = w_f := by by_contra hnf; simp [pairBit, sBit, hnf] at hne
        subst this; exact ⟨hfnf, hwf_hit⟩)
      (by rw [hkill, hkill])
    rw [hfmB, hmB] at hcut; cases hcut
  · let m₀ := n + m + jm
    have hm0_le := reaches_le (reaches_root_of_closed d.hL d.huse jm hjmL)
    have hs_m0 : reaches (n + m) d.E d.L s_hit m₀ := Relation.ReflTransGen.tail hs_a ⟨jm, hjmL, rfl, ha_mem, ha_lt⟩
    have hjq : jm ≠ d.j_not := by
      intro e; subst e
      rcases hs_m0.cases_tail with h | ⟨u, hu, eu⟩
      · omega
      · obtain ⟨ku, _, _, hum, _⟩ := eu; have : ku = d.j_not := by omega
        rw [this, hf_not] at hum; simp at hum; have := reaches_le hu; omega
    obtain ⟨_, u, v, _, hin, _, _⟩ := d.hother_two jm hjmL hjq
    have hfxB : fixBranch d false true m₀ = none := by
      dsimp only [m₀, fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
    have hfxF : fixBranch d true false m₀ = none := by
      dsimp only [m₀, fixBranch]; rw [if_neg (by omega), if_neg (by omega)]
    have ha_mem0 := ha_mem
    have hb_mem0 := hb_mem
    have hwm_a : reaches (n + m) d.E d.L w_m a := by
      have hwm_m0 : reaches (n + m) d.E d.L w_m m₀ := by
        by_contra hnr
        have hnw_ma : ¬ reaches (n + m) d.E d.L w_m a := fun h => hnr (Relation.ReflTransGen.tail h ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩)
        have ha1 : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) a = false :=
          (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
            (x := pairBit w_f w_m) (y := fun _ => false)
            fun z _ hza => by simp only [pairBit, decide_eq_false_iff_not, not_or]; exact ⟨fun e => hnw_a (e ▸ hza), fun e => hnw_ma (e ▸ hza)⟩).trans haB0
        have ha2 : value (n + m) d.E (sBit w_m) (fixBranch d false true) a = false :=
          (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
            (x := sBit w_m) (y := fun _ => false)
            fun z _ hza => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw_ma hza).trans haB0
        have hm0_eq : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) m₀ =
            value (n + m) d.E (sBit w_m) (fixBranch d false true) m₀ := by
          change value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) (n + m + jm) =
            value (n + m) d.E (sBit w_m) (fixBranch d false true) (n + m + jm)
          rw [val_gate hfxB, val_gate hfxB, hin]; rw [hin] at ha_mem
          rcases List.mem_pair.mp ha_mem with rfl | rfl <;> simp [GateOp.eval, ho, ha1, ha2]
        have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le false true
          (fun z _ hne => by
            have : z = w_f := by by_contra hnf; simp [pairBit, sBit, hnf] at hne
            subst this; exact ⟨hfnf, Relation.ReflTransGen.tail hwf_b ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩⟩)
          hm0_eq
        rw [hfmB, hmB] at hcut; cases hcut
      rcases hwm_m0.cases_tail with h | ⟨c, hmc, ⟨kc, _, hkc, hc_mem, hc_lt⟩⟩
      · omega
      · have : kc = jm := by omega
        rw [this] at hc_mem hc_lt
        have hc_or : c = a ∨ c = b := by
          rw [hin] at hc_mem ha_mem hb_mem
          rcases List.mem_pair.mp hc_mem with rfl | rfl <;>
            rcases List.mem_pair.mp ha_mem with eu | eu <;>
            rcases List.mem_pair.mp hb_mem with ev | ev
          all_goals first | exact Or.inl eu.symm | exact Or.inr ev.symm | exact False.elim (hab (eu.trans ev.symm))
        rcases hc_or with hca | hcb
        · exact hca ▸ hmc
        · exfalso
          rw [hcb] at hmc
          have hnw_ma : ¬ reaches (n + m) d.E d.L w_m a := by
            intro hma
            rcases reaches_total_of_no_f d.hsingle hmnf hma hmc with h | h
            · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
              · exact hab rfl
              · have hc_eq := d.hsingle a (by have := reaches_le hs_a; omega) d' m₀ ed' ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩
                rw [hc_eq] at hd'; have := reaches_le hd'; omega
            · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
              · exact hab rfl
              · have hc_eq := d.hsingle b (fun e => hmnf (e ▸ hmc)) d' m₀ ed' ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩
                rw [hc_eq] at hd'; have := reaches_le hd'; omega
          have ha1 : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) a = false :=
            (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
              (x := pairBit w_f w_m) (y := fun _ => false)
              fun z _ hza => by simp only [pairBit, decide_eq_false_iff_not, not_or]; exact ⟨fun e => hnw_a (e ▸ hza), fun e => hnw_ma (e ▸ hza)⟩).trans haB0
          have ha2 : value (n + m) d.E (sBit w_m) (fixBranch d false true) a = false :=
            (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
              (x := sBit w_m) (y := fun _ => false)
              fun z _ hza => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw_ma hza).trans haB0
          have hm0_eq : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) m₀ =
              value (n + m) d.E (sBit w_m) (fixBranch d false true) m₀ := by
            change value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) (n + m + jm) =
              value (n + m) d.E (sBit w_m) (fixBranch d false true) (n + m + jm)
            rw [val_gate hfxB, val_gate hfxB, hin]; rw [hin] at ha_mem
            rcases List.mem_pair.mp ha_mem with rfl | rfl <;> simp [GateOp.eval, ho, ha1, ha2]
          have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le false true
            (fun z _ hne => by
              have : z = w_f := by by_contra hnf; simp [pairBit, sBit, hnf] at hne
              subst this; exact ⟨hfnf, Relation.ReflTransGen.tail hwf_b ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩⟩)
            hm0_eq
          rw [hfmB, hmB] at hcut; cases hcut
    have hnwm_b : ¬ reaches (n + m) d.E d.L w_m b := by
      intro hmb
      rcases reaches_total_of_no_f d.hsingle hmnf hwm_a hmb with h | h
      · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
        · exact hab rfl
        · have := d.hsingle a (by have := reaches_le hs_a; omega) d' m₀ ed' ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩
          rw [this] at hd'; have := reaches_le hd'; omega
      · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
        · exact hab rfl
        · have := d.hsingle b (fun e => hmnf (e ▸ hmb)) d' m₀ ed' ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩
          rw [this] at hd'; have := reaches_le hd'; omega
    have hbB0 : value (n + m) d.E (fun _ => false) (fixBranch d false true) b = false := by
      by_contra h1
      have hbt := Bool.eq_true_of_not_eq_false h1
      have h_mono_b (x : ℕ → Bool) : value (n + m) d.E x (fixBranch d false true) b = true :=
        eval_mono_bound d.hL d.hFan (fix₀ := fixBranch d false true) (fix₁ := fixBranch d false true)
          (fun k _ _ b₀ hb₀ => ⟨b₀, hb₀, id⟩)
          (fun k hk _ hnone => ⟨hnone, fun ho' => by
            dsimp only [fixBranch] at hnone
            by_cases h1' : n + m + k = d.f
            · rw [if_pos h1'] at hnone; cases hnone
            · rw [if_neg h1', if_pos (by rw [(d.hjnot k hk).mp ho'])] at hnone; cases hnone⟩)
          (fun _ _ hf => by cases hf) (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩) (Nat.lt_succ_self _) hbt
      have ha_eq : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) a =
          value (n + m) d.E (sBit w_m) (fixBranch d false true) a :=
        value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
          fun z _ hza => by
            have hnwf : z ≠ w_f := fun e => hnw_a (e ▸ hza)
            simp [pairBit, sBit, hnwf]
      have hm0_eq : value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) m₀ =
          value (n + m) d.E (sBit w_m) (fixBranch d false true) m₀ := by
        change value (n + m) d.E (pairBit w_f w_m) (fixBranch d false true) (n + m + jm) =
          value (n + m) d.E (sBit w_m) (fixBranch d false true) (n + m + jm)
        rw [val_gate hfxB, val_gate hfxB, hin]; rw [hin] at ha_mem hb_mem
        rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
          rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
          first | exact False.elim (hab rfl) | simp [GateOp.eval, ho, ha_eq, h_mono_b (pairBit w_f w_m), h_mono_b (sBit w_m)]
      have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le false true
        (fun z _ hne => by
          have : z = w_f := by by_contra hnf; simp [pairBit, sBit, hnf] at hne
          subst this; exact ⟨hfnf, Relation.ReflTransGen.tail hwf_b ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩⟩)
        hm0_eq
      rw [hfmB, hmB] at hcut; cases hcut
    have hnq_m0 : ¬ reaches (n + m) d.E d.L (n + m + d.j_not) m₀ := by
      intro hqm
      have hn_both : ¬ (reaches (n + m) d.E d.L w_c a ∧ reaches (n + m) d.E d.L w_c b) := by
        rintro ⟨hca, hcb⟩
        rcases reaches_total_of_no_f d.hsingle hcnf hca hcb with h | h
        · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
          · exact hab rfl
          · have := d.hsingle a (by have := reaches_le hs_a; omega) d' m₀ ed' ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩
            rw [this] at hd'; have := reaches_le hd'; omega
        · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
          · exact hab rfl
          · have := d.hsingle b (fun e => hcnf (e ▸ hcb)) d' m₀ ed' ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩
            rw [this] at hd'; have := reaches_le hd'; omega
      have hmB_wc : value (n + m) d.E (sBit w_c) (fixBranch d false true) m₀ = false := by
        change value (n + m) d.E (sBit w_c) (fixBranch d false true) (n + m + jm) = false
        rw [val_gate hfxB, hin]; rw [hin] at ha_mem hb_mem
        by_cases hca : reaches (n + m) d.E d.L w_c a
        · have hcb : ¬ reaches (n + m) d.E d.L w_c b := fun h => hn_both ⟨hca, h⟩
          have hb0_wc : value (n + m) d.E (sBit w_c) (fixBranch d false true) b = false :=
            (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩)
              (x := sBit w_c) (y := fun _ => false)
              fun z _ hzb => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hcb hzb).trans hbB0
          rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
            rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
            simp [GateOp.eval, ho, ha_lt, hb_lt, hb0_wc]
        · have ha0_wc : value (n + m) d.E (sBit w_c) (fixBranch d false true) a = false :=
            (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
              (x := sBit w_c) (y := fun _ => false)
              fun z _ hza => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hca hza).trans haB0
          rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
            rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
            simp [GateOp.eval, ho, ha_lt, hb_lt, ha0_wc]
      have hres := q_not_below_killed_node d hf_not ⟨jm, hjmL, rfl⟩ hqm hs_m0 hmB_wc hcB
      rw [hres] at hcF; cases hcF
    have hw2_b : reaches (n + m) d.E d.L w_2 b := by
      by_contra hnw2b
      have hb1 : value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) b = false :=
        (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩)
          (x := pairBit w_2 w_m) (y := fun _ => false)
          fun z _ hzb => by simp only [pairBit, decide_eq_false_iff_not, not_or]; exact ⟨fun e => hnw2b (e ▸ hzb), fun e => hnwm_b (e ▸ hzb)⟩).trans hbB0
      have hb2 : value (n + m) d.E (sBit w_2) (fixBranch d false true) b = false :=
        (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩)
          (x := sBit w_2) (y := fun _ => false)
          fun z _ hzb => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw2b hzb).trans hbB0
      have hm0_eq : value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) m₀ =
          value (n + m) d.E (sBit w_2) (fixBranch d false true) m₀ := by
        change value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) (n + m + jm) =
          value (n + m) d.E (sBit w_2) (fixBranch d false true) (n + m + jm)
        rw [val_gate hfxB, val_gate hfxB, hin]; rw [hin] at hb_mem
        rcases List.mem_pair.mp hb_mem with rfl | rfl <;> simp [GateOp.eval, ho, hb1, hb2]
      have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le false true
        (fun z _ hne => by
          have : z = w_m := by by_contra hnm; simp [pairBit, sBit, hnm] at hne
          subst this; exact ⟨hmnf, Relation.ReflTransGen.tail hwm_a ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩⟩)
        hm0_eq
      rw [h2mB, h2B] at hcut; cases hcut
    have hnw2_a : ¬ reaches (n + m) d.E d.L w_2 a := by
      intro hw2a
      rcases reaches_total_of_no_f d.hsingle h2nf hw2a hw2_b with h | h
      · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
        · exact hab rfl
        · have := d.hsingle a (by have := reaches_le hs_a; omega) d' m₀ ed' ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩
          rw [this] at hd'; have := reaches_le hd'; omega
      · rcases h.cases_head with rfl | ⟨d', ed', hd'⟩
        · exact hab rfl
        · have := d.hsingle b (fun e => h2nf (e ▸ hw2_b)) d' m₀ ed' ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩
          rw [this] at hd'; have := reaches_le hd'; omega
    have hw2_bB : value (n + m) d.E (sBit w_2) (fixBranch d false true) b = true := by
      by_contra hb0
      have hb0' := Bool.eq_false_iff.mpr hb0
      have hbm : value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) b = false :=
        (value_agree_inputs d.hL (fixBranch d false true) (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩)
          (x := pairBit w_2 w_m) (y := sBit w_2)
          fun z _ hzb => by simp only [pairBit, sBit, decide_eq_decide]; exact ⟨fun h => h.resolve_right (fun e => hnwm_b (e ▸ hzb)), Or.inl⟩).trans hb0'
      have hm0_eq : value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) m₀ =
          value (n + m) d.E (sBit w_2) (fixBranch d false true) m₀ := by
        change value (n + m) d.E (pairBit w_2 w_m) (fixBranch d false true) (n + m + jm) =
          value (n + m) d.E (sBit w_2) (fixBranch d false true) (n + m + jm)
        rw [val_gate hfxB, val_gate hfxB, hin]; rw [hin] at hb_mem
        rcases List.mem_pair.mp hb_mem with rfl | rfl <;> simp [GateOp.eval, ho, hbm, hb0']
      have hcut := evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le false true
        (fun z _ hne => by
          have : z = w_m := by by_contra hnm; simp [pairBit, sBit, hnm] at hne
          subst this; exact ⟨hmnf, Relation.ReflTransGen.tail hwm_a ⟨jm, hjmL, rfl, ha_mem0, ha_lt⟩⟩)
        hm0_eq
      rw [h2mB, h2B] at hcut; cases hcut
    have hnq_b : ¬ reaches (n + m) d.E d.L (n + m + d.j_not) b :=
      fun hqb => hnq_m0 (Relation.ReflTransGen.tail hqb ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩)
    have hnf_b : ¬ reaches (n + m) d.E d.L d.f b := by
      intro hfb
      rcases hfb.cases_head with rfl | ⟨s', efs, hsb⟩
      · exact h2nf hw2_b
      · obtain ⟨js', hjs', hseq, hsmem, hslt⟩ := efs
        subst hseq
        have efs' : edgeTo (n + m) d.E d.L d.f (n + m + js') := ⟨js', hjs', rfl, hsmem, hslt⟩
        rcases hrdf.2 js' hjs' efs' with h | h
        · exact hnq_b (h ▸ hsb)
        · rw [h] at hsb; exact hns_b hsb
    have hw2_bF : value (n + m) d.E (sBit w_2) (fixBranch d true false) b = true :=
      (value_agree_of_no_f_q d (sBit w_2) true false false true b
        (parent_live d.hL hjmL ⟨hb_mem0, hb_lt⟩) hnf_b hnq_b).trans hw2_bB
    have ha_w2 : value (n + m) d.E (sBit w_2) (fixBranch d true false) a = true :=
      (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
        (x := sBit w_2) (y := fun _ => false)
        fun z _ hza => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw2_a hza).trans haF
    have ha_wf : value (n + m) d.E (sBit w_f) (fixBranch d true false) a = true :=
      (value_agree_inputs d.hL (fixBranch d true false) (parent_live d.hL hjmL ⟨ha_mem0, ha_lt⟩)
        (x := sBit w_f) (y := fun _ => false)
        fun z _ hza => by simp only [sBit, decide_eq_false_iff_not]; intro e; subst e; exact hnw_a hza).trans haF
    have hm0_eq : value (n + m) d.E (sBit w_2) (fixBranch d true false) m₀ =
        value (n + m) d.E (sBit w_f) (fixBranch d true false) m₀ := by
      change value (n + m) d.E (sBit w_2) (fixBranch d true false) (n + m + jm) =
        value (n + m) d.E (sBit w_f) (fixBranch d true false) (n + m + jm)
      rw [val_gate hfxF, val_gate hfxF, hin]; rw [hin] at ha_mem hb_mem
      rcases List.mem_pair.mp ha_mem with rfl | rfl <;>
        rcases List.mem_pair.mp hb_mem with rfl | rfl <;>
        first | exact False.elim (hab rfl) | simp [GateOp.eval, ho, ha_w2, ha_wf, hw2_bF, hwf_bF]
    exact (evalT_cut_above d (Or.inr ⟨jm, hjmL, rfl⟩) (by omega) hm0_le true false
      (fun z _ hne => by
        by_cases h2 : z = w_2
        · subst h2; exact ⟨h2nf, Relation.ReflTransGen.tail hw2_b ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩⟩
        · by_cases hf' : z = w_f
          · subst hf'; exact ⟨hfnf, Relation.ReflTransGen.tail hwf_b ⟨jm, hjmL, rfl, hb_mem0, hb_lt⟩⟩
          · exfalso; apply hne; simp [sBit, h2, hf'])
      hm0_eq).trans hfF

theorem core_classification {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hg : Good n m A) (d : CollisionData n m A) (sd : SplitData n m A d)
    (hA00 : A d.r₀ d.c₀ = false) (hf_not : (gateAt d.E d.j_not).inputs = [d.f]) :
    ∃ (u₁ r₂ r₃ : Fin n) (v₁ c₂ c₃ : Fin m),
      d.r₀ ≠ u₁ ∧ d.r₀ ≠ r₂ ∧ d.r₀ ≠ r₃ ∧ u₁ ≠ r₂ ∧ u₁ ≠ r₃ ∧ r₂ ≠ r₃ ∧
      d.c₀ ≠ v₁ ∧ d.c₀ ≠ c₂ ∧ d.c₀ ≠ c₃ ∧ v₁ ≠ c₂ ∧ v₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      (∀ j : Fin m, A d.r₀ j = decide (j = c₂)) ∧
      (∀ j : Fin m, A u₁ j = decide (j = c₃)) ∧
      (∀ i : Fin n, A i d.c₀ = decide (i = r₂)) ∧
      (∀ i : Fin n, A i v₁ = decide (i = r₃)) ∧
      (∀ j : Fin m, j ≠ v₁ → A r₂ j = true) ∧
      (∀ i : Fin n, i ≠ u₁ → A i c₂ = true) ∧
      A r₃ c₃ = false ∧
      (let R_rest := Finset.univ.filter fun i : Fin n => i ≠ d.r₀ ∧ i ≠ u₁ ∧ i ≠ r₂;
       let C_rest := Finset.univ.filter fun j : Fin m => j ≠ d.c₀ ∧ j ≠ v₁ ∧ j ≠ c₂;
       let R_B := R_rest.filter fun i => ∃ j ∈ C_rest, A i j = true;
       let C_B := C_rest.filter fun j => ∃ i ∈ R_rest, A i j = true;
       (∀ i ∈ R_rest, i ≠ r₃ → i ∈ R_B) ∧
       (∀ j ∈ C_rest, j ≠ c₃ → j ∈ C_B) ∧
       ∃ (e_B : {r // r ∈ R_B} ≃ {c // c ∈ C_B}),
         ∀ (r : {r // r ∈ R_B}) (c : {c // c ∈ C_B}), A r.1 c.1 = decide (e_B r = c)) := by
  classical
  obtain ⟨u₁, v₁, hu1_r, hv1_c, hf_eval⟩ := f_singleton_row_col hg d sd hA00 hf_not
  have hr0_away : ¬ reaches (n + m) d.E d.L d.r₀.val (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.r₀.isLt; omega)]
    exact (d.hr0 d.r₀).mpr rfl
  have hc0_away : ¬ reaches (n + m) d.E d.L (n + d.c₀.val) (n + m + d.r) := by
    rw [reaches_root_iff_used d.hrL d.hL d.huse (by have := d.c₀.isLt; omega)]
    exact (d.hc0 d.c₀).mpr rfl
  have hr0_u1 : d.r₀ ≠ u₁ := fun e => hr0_away ((hu1_r u₁).mpr rfl |> fun h => (e ▸ h).trans (f_reaches_root d))
  have hc0_v1 : d.c₀ ≠ v₁ := fun e => hc0_away ((hv1_c v₁).mpr rfl |> fun h => (e ▸ h).trans (f_reaches_root d))
  let B : (ℕ → Bool) → Bool := evalT d false true
  let F : (ℕ → Bool) → Bool := evalT d true false
  have hT010 : B (fun _ => false) = false := T_010_false hg d sd hA00 hf_not
  have hT100 : F (fun _ => false) = false := T_100_false hg d sd hf_not
  have hAB : ∀ i j, i ≠ u₁ → j ≠ v₁ → A i j = B (oneEachRaw n m i j) := by
    intro i j hi hj
    rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hf_eval i j]
    simp [hi, hj, B]
  have hAF : ∀ i j, i = u₁ ∨ j = v₁ → A i j = F (oneEachRaw n m i j) := by
    intro i j huv
    rw [← d.hRep i j, ← evalT_eq_eval d sd hf_not, hf_eval i j]
    simp [huv, F]
  have hB_r0_eq (j : Fin m) (bf bn : Bool) :
      evalT d bf bn (oneEachRaw n m d.r₀ j) = evalT d bf bn (sBit (n + j.val)) :=
    value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      fun w _ hw => by simp only [oneEachRaw, sBit, decide_eq_decide]; exact ⟨fun h => h.resolve_left (fun e => hr0_away (e ▸ hw)), Or.inr⟩
  have hB_c0_eq (i : Fin n) (bf bn : Bool) :
      evalT d bf bn (oneEachRaw n m i d.c₀) = evalT d bf bn (sBit i.val) :=
    value_agree_inputs d.hL (fixBranch d bf bn) (Or.inr ⟨d.r, d.hrL, rfl⟩)
      fun w _ hw => by simp only [oneEachRaw, sBit, decide_eq_decide]; exact ⟨fun h => h.resolve_right (fun e => hc0_away (e ▸ hw)), Or.inl⟩
  have h_u1_eq (j : Fin m) (bf bn : Bool) :
      evalT d bf bn (oneEachRaw n m u₁ j) = evalT d bf bn (sBit (n + j.val)) :=
    evalT_indep_of_reaches_f d sd bf bn ((hu1_r u₁).mpr rfl)
      fun w _ hw => by simp only [oneEachRaw, sBit, decide_eq_decide]; exact ⟨fun h => h.resolve_left hw, Or.inr⟩
  have h_v1_eq (i : Fin n) (bf bn : Bool) :
      evalT d bf bn (oneEachRaw n m i v₁) = evalT d bf bn (sBit i.val) :=
    evalT_indep_of_reaches_f d sd bf bn ((hv1_c v₁).mpr rfl)
      fun w _ hw => by simp only [oneEachRaw, sBit, decide_eq_decide]; exact ⟨fun h => h.resolve_right hw, Or.inl⟩
  have hBv1 : B (sBit (n + v₁.val)) = false :=
    (evalT_indep_of_reaches_f d sd false true ((hv1_c v₁).mpr rfl) fun w _ hw => by simp [sBit, hw]).trans hT010
  have hBu1 : B (sBit u₁.val) = false :=
    (evalT_indep_of_reaches_f d sd false true ((hu1_r u₁).mpr rfl) fun w _ hw => by simp [sBit, hw]).trans hT010
  have hFv1 : F (sBit (n + v₁.val)) = false :=
    (evalT_indep_of_reaches_f d sd true false ((hv1_c v₁).mpr rfl) fun w _ hw => by simp [sBit, hw]).trans hT100
  have hFu1 : F (sBit u₁.val) = false :=
    (evalT_indep_of_reaches_f d sd true false ((hu1_r u₁).mpr rfl) fun w _ hw => by simp [sBit, hw]).trans hT100
  have hBc0 : B (sBit (n + d.c₀.val)) = false :=
    (value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hw => by simp only [sBit, decide_eq_false_iff_not]; intro e; exact hc0_away (e ▸ hw)).trans hT010
  have hBr0 : B (sBit d.r₀.val) = false :=
    (value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hw => by simp only [sBit, decide_eq_false_iff_not]; intro e; exact hr0_away (e ▸ hw)).trans hT010
  have hFc0 : F (sBit (n + d.c₀.val)) = false :=
    (value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hw => by simp only [sBit, decide_eq_false_iff_not]; intro e; exact hc0_away (e ▸ hw)).trans hT100
  have hFr0 : F (sBit d.r₀.val) = false :=
    (value_agree_inputs d.hL _ (Or.inr ⟨d.r, d.hrL, rfl⟩) fun w _ hw => by simp only [sBit, decide_eq_false_iff_not]; intro e; exact hr0_away (e ▸ hw)).trans hT100
  have hA_r0_B (j : Fin m) : A d.r₀ j = B (sBit (n + j.val)) := by
    by_cases hj : j = v₁
    · rw [hj]; exact (hAF d.r₀ v₁ (Or.inr rfl)).trans ((h_v1_eq d.r₀ true false).trans (hFr0.trans hBv1.symm))
    · exact (hAB d.r₀ j hr0_u1 hj).trans (hB_r0_eq j false true)
  have hA_c0_B (i : Fin n) : A i d.c₀ = B (sBit i.val) := by
    by_cases hi : i = u₁
    · rw [hi]; exact (hAF u₁ d.c₀ (Or.inl rfl)).trans ((h_u1_eq d.c₀ true false).trans (hFc0.trans hBu1.symm))
    · exact (hAB i d.c₀ hi hc0_v1).trans (hB_c0_eq i false true)
  have hA_u1_F (j : Fin m) : A u₁ j = F (sBit (n + j.val)) := by
    exact (hAF u₁ j (Or.inl rfl)).trans (h_u1_eq j true false)
  have hA_v1_F (i : Fin n) : A i v₁ = F (sBit i.val) := by
    exact (hAF i v₁ (Or.inr rfl)).trans (h_v1_eq i true false)
  -- c₂
  obtain ⟨c₂, hc2_r0⟩ := (no_empty_or_full_row hg.2.2.1 d.r₀).1
  have hBc2 : B (sBit (n + c₂.val)) = true := by rw [← hA_r0_B]; exact hc2_r0
  have hc2_c0 : d.c₀ ≠ c₂ := fun e => by subst e; rw [hBc0] at hBc2; cases hBc2
  have hc2_v1 : v₁ ≠ c₂ := fun e => by subst e; rw [hBv1] at hBc2; cases hBc2
  have h_col_B (j : Fin m) (hBj : B (sBit (n + j.val)) = true) :
      (∀ i : Fin n, i ≠ u₁ → A i j = true) ∧ F (sBit (n + j.val)) = false := by
    have hjn : j ≠ v₁ := fun e => by subst e; rw [hBv1] at hBj; cases hBj
    have hall : ∀ i : Fin n, i ≠ u₁ → A i j = true := fun i hi => by
      rw [hAB i j hi hjn]
      exact evalT_mono d sd id id (fun w _ hw => by simp only [sBit, oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inr hw) hBj
    refine ⟨hall, ?_⟩
    by_contra hFt
    have hFt' := Bool.eq_true_of_not_eq_false hFt
    obtain ⟨i_empty, hie⟩ := (no_empty_or_full_col hg.2.2.2.1 j).2
    by_cases hiu : i_empty = u₁
    · subst hiu; rw [hA_u1_F, hFt'] at hie; cases hie
    · rw [hall i_empty hiu] at hie; cases hie
  have hc2_spec := h_col_B c₂ hBc2
  have hFc2 : F (sBit (n + c₂.val)) = false := hc2_spec.2
  have hA_r0_iff (j : Fin m) : A d.r₀ j = decide (j = c₂) := by
    by_cases hj : j = c₂
    · subst hj; simp [hc2_r0]
    · rw [decide_eq_false hj]
      by_contra h1
      have ht := Bool.eq_true_of_not_eq_false h1
      have hBj : B (sBit (n + j.val)) = true := by rw [← hA_r0_B]; exact ht
      have hj_spec := h_col_B j hBj
      apply hj; apply hg.2.1; funext i; dsimp only
      by_cases hiu : i = u₁
      · subst hiu; simp [hA_u1_F, hj_spec.2, hFc2]
      · simp [hj_spec.1 i hiu, hc2_spec.1 i hiu]
  -- r₂
  obtain ⟨r₂, hr2_c0⟩ := (no_empty_or_full_col hg.2.2.2.1 d.c₀).1
  have hBr2 : B (sBit r₂.val) = true := by rw [← hA_c0_B]; exact hr2_c0
  have hr2_r0 : d.r₀ ≠ r₂ := fun e => by subst e; rw [hBr0] at hBr2; cases hBr2
  have hr2_u1 : u₁ ≠ r₂ := fun e => by subst e; rw [hBu1] at hBr2; cases hBr2
  have h_row_B (i : Fin n) (hBi : B (sBit i.val) = true) :
      (∀ j : Fin m, j ≠ v₁ → A i j = true) ∧ F (sBit i.val) = false := by
    have hin : i ≠ u₁ := fun e => by subst e; rw [hBu1] at hBi; cases hBi
    have hall : ∀ j : Fin m, j ≠ v₁ → A i j = true := fun j hj => by
      rw [hAB i j hin hj]
      exact evalT_mono d sd id id (fun w _ hw => by simp only [sBit, oneEachRaw, decide_eq_true_eq] at hw ⊢; exact Or.inl hw) hBi
    refine ⟨hall, ?_⟩
    by_contra hFt
    have hFt' := Bool.eq_true_of_not_eq_false hFt
    obtain ⟨j_empty, hje⟩ := (no_empty_or_full_row hg.2.2.1 i).2
    by_cases hjv : j_empty = v₁
    · subst hjv; rw [hA_v1_F, hFt'] at hje; cases hje
    · rw [hall j_empty hjv] at hje; cases hje
  have hr2_spec := h_row_B r₂ hBr2
  have hFr2 : F (sBit r₂.val) = false := hr2_spec.2
  have hA_c0_iff (i : Fin n) : A i d.c₀ = decide (i = r₂) := by
    by_cases hi : i = r₂
    · subst hi; simp [hr2_c0]
    · rw [decide_eq_false hi]
      by_contra h1
      have ht := Bool.eq_true_of_not_eq_false h1
      have hBi : B (sBit i.val) = true := by rw [← hA_c0_B]; exact ht
      have hi_spec := h_row_B i hBi
      apply hi; apply hg.1; funext j
      by_cases hjv : j = v₁
      · subst hjv; simp [hA_v1_F, hi_spec.2, hFr2]
      · simp [hi_spec.1 j hjv, hr2_spec.1 j hjv]
  -- c₃ and r₃
  obtain ⟨c₃, hc3_u1⟩ := (no_empty_or_full_row hg.2.2.1 u₁).1
  have hFc3 : F (sBit (n + c₃.val)) = true := by rw [← hA_u1_F]; exact hc3_u1
  have hc3_c0 : d.c₀ ≠ c₃ := fun e => by subst e; rw [hFc0] at hFc3; cases hFc3
  have hc3_v1 : v₁ ≠ c₃ := fun e => by subst e; rw [hFv1] at hFc3; cases hFc3
  have hc3_c2 : c₂ ≠ c₃ := fun e => by subst e; rw [hFc2] at hFc3; cases hFc3
  have hBc3 : B (sBit (n + c₃.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [hc3_c2.symm]
  have hA_u1_iff (j : Fin m) : A u₁ j = decide (j = c₃) := by
    by_cases hj : j = c₃
    · subst hj; simp [hc3_u1]
    · rw [decide_eq_false hj]
      by_contra h1
      have ht := Bool.eq_true_of_not_eq_false h1
      have hFj : F (sBit (n + j.val)) = true := by rw [← hA_u1_F]; exact ht
      have hj_v1 : j ≠ v₁ := fun e => by subst e; rw [hFv1] at hFj; cases hFj
      have hj_c2 : j ≠ c₂ := fun e => by subst e; rw [hFc2] at hFj; cases hFj
      have hBj : B (sBit (n + j.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [hj_c2]
      have hjnf : ¬ reaches (n + m) d.E d.L (n + j.val) d.f := fun h => hj_v1 ((hv1_c j).mp h)
      have hc3nf : ¬ reaches (n + m) d.E d.L (n + c₃.val) d.f := fun h => hc3_v1.symm ((hv1_c c₃).mp h)
      apply hj; apply hg.2.1; funext i; dsimp only
      by_cases hiu : i = u₁
      · subst hiu; simp [ht, hc3_u1]
      · rw [hAB i j hiu hj_v1, hAB i c₃ hiu hc3_v1.symm]
        have heqB := no_two_F_witnesses hg d sd hf_not (by omega) (by omega) (fun e => hj (Fin.ext (Nat.add_left_cancel e)))
          hjnf hc3nf hFj hFc3 hBj hBc3 (y := sBit i.val) fun z _ hz => by
            have : z = i.val := by by_contra hzi; simp [sBit, hzi] at hz
            subst this; exact ⟨by omega, by omega, fun h => hiu ((hu1_r i).mp h)⟩
        have h_p1 : oneEachRaw n m i j = fun v => sBit (n + j.val) v || sBit i.val v := by
          funext v; by_cases h1 : v = i.val <;> by_cases h2 : v = n + j.val <;> simp [oneEachRaw, sBit, h1, h2]
        have h_p2 : oneEachRaw n m i c₃ = fun v => sBit (n + c₃.val) v || sBit i.val v := by
          funext v; by_cases h1 : v = i.val <;> by_cases h2 : v = n + c₃.val <;> simp [oneEachRaw, sBit, h1, h2]
        rw [h_p1, h_p2]; exact heqB
  obtain ⟨r₃, hr3_v1⟩ := (no_empty_or_full_col hg.2.2.2.1 v₁).1
  have hFr3 : F (sBit r₃.val) = true := by rw [← hA_v1_F]; exact hr3_v1
  have hr3_r0 : d.r₀ ≠ r₃ := fun e => by subst e; rw [hFr0] at hFr3; cases hFr3
  have hr3_u1 : u₁ ≠ r₃ := fun e => by subst e; rw [hFu1] at hFr3; cases hFr3
  have hr3_r2 : r₂ ≠ r₃ := fun e => by subst e; rw [hFr2] at hFr3; cases hFr3
  have hBr3 : B (sBit r₃.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [hr3_r2.symm]
  have hA_v1_iff (i : Fin n) : A i v₁ = decide (i = r₃) := by
    by_cases hi : i = r₃
    · subst hi; simp [hr3_v1]
    · rw [decide_eq_false hi]
      by_contra h1
      have ht := Bool.eq_true_of_not_eq_false h1
      have hFi : F (sBit i.val) = true := by rw [← hA_v1_F]; exact ht
      have hi_u1 : i ≠ u₁ := fun e => by subst e; rw [hFu1] at hFi; cases hFi
      have hi_r2 : i ≠ r₂ := fun e => by subst e; rw [hFr2] at hFi; cases hFi
      have hBi : B (sBit i.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [hi_r2]
      have hinf : ¬ reaches (n + m) d.E d.L i.val d.f := fun h => hi_u1 ((hu1_r i).mp h)
      have hr3nf : ¬ reaches (n + m) d.E d.L r₃.val d.f := fun h => hr3_u1.symm ((hu1_r r₃).mp h)
      apply hi; apply hg.1; funext j
      by_cases hjv : j = v₁
      · subst hjv; simp [ht, hr3_v1]
      · rw [hAB i j hi_u1 hjv, hAB r₃ j hr3_u1.symm hjv]
        have heqB := no_two_F_witnesses hg d sd hf_not (by omega) (by omega) (by intro e; apply hi; ext; exact e)
          hinf hr3nf hFi hFr3 hBi hBr3 (y := sBit (n + j.val)) fun z _ hz => by
            have : z = n + j.val := by by_contra hzj; simp [sBit, hzj] at hz
            subst this; exact ⟨by omega, by omega, fun h => hjv ((hv1_c j).mp h)⟩
        have h_p1 : oneEachRaw n m i j = fun v => sBit i.val v || sBit (n + j.val) v := by
          funext v; simp [oneEachRaw, sBit]
        have h_p2 : oneEachRaw n m r₃ j = fun v => sBit r₃.val v || sBit (n + j.val) v := by
          funext v; simp [oneEachRaw, sBit]
        rw [h_p1, h_p2]; exact heqB
  have hr3_nf : ¬ reaches (n + m) d.E d.L r₃.val d.f := fun h => hr3_u1.symm ((hu1_r r₃).mp h)
  have hc3_nf : ¬ reaches (n + m) d.E d.L (n + c₃.val) d.f := fun h => hc3_v1.symm ((hv1_c c₃).mp h)
  have hr3_c3_false : A r₃ c₃ = false := by
    rw [hAB r₃ c₃ hr3_u1.symm hc3_v1.symm]
    exact F_witness_pair_false hg d sd hf_not (by omega) (by omega) (by omega) hr3_nf hc3_nf hFr3 hFc3 hBr3 hBc3
  let R_rest := Finset.univ.filter fun i : Fin n => i ≠ d.r₀ ∧ i ≠ u₁ ∧ i ≠ r₂
  let C_rest := Finset.univ.filter fun j : Fin m => j ≠ d.c₀ ∧ j ≠ v₁ ∧ j ≠ c₂
  let R_B := R_rest.filter fun i => ∃ j ∈ C_rest, A i j = true
  let C_B := C_rest.filter fun j => ∃ i ∈ R_rest, A i j = true
  have hR_cov : ∀ i ∈ R_rest, i ≠ r₃ → i ∈ R_B := by
    intro i hi hi3
    rw [Finset.mem_filter]; refine ⟨hi, ?_⟩
    by_contra hnone
    have hi_spec := (Finset.mem_filter.mp hi).2
    apply hi_spec.1; apply hg.1; funext j
    rw [hA_r0_iff]
    by_cases hj0 : j = d.c₀
    · subst hj0; rw [hA_c0_iff]; simp [hi_spec.2.2, hc2_c0]
    · by_cases hjv : j = v₁
      · subst hjv; rw [hA_v1_iff]; simp [hi3, hc2_v1]
      · by_cases hj2 : j = c₂
        · subst hj2; simp [hc2_spec.1 i hi_spec.2.1]
        · have hjC : j ∈ C_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjv, hj2⟩
          have hfij : A i j = false := Bool.eq_false_iff.mpr fun h => hnone ⟨j, hjC, h⟩
          simp [hfij, hj2]
  have hC_cov : ∀ j ∈ C_rest, j ≠ c₃ → j ∈ C_B := by
    intro j hj hj3
    rw [Finset.mem_filter]; refine ⟨hj, ?_⟩
    by_contra hnone
    have hj_spec := (Finset.mem_filter.mp hj).2
    apply hj_spec.1; apply hg.2.1; funext i; dsimp only
    rw [hA_c0_iff]
    by_cases hi0 : i = d.r₀
    · subst hi0; rw [hA_r0_iff]; simp [hj_spec.2.2, hr2_r0]
    · by_cases hiu : i = u₁
      · subst hiu; rw [hA_u1_iff]; simp [hj3, hr2_u1]
      · by_cases hi2 : i = r₂
        · subst hi2; simp [hr2_spec.1 j hj_spec.2.1]
        · have hiR : i ∈ R_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hiu, hi2⟩
          have hfij : A i j = false := Bool.eq_false_iff.mpr fun h => hnone ⟨i, hiR, h⟩
          simp [hfij, hi2]
  have hrect_B : ∀ r₁ ∈ R_B, ∀ r₂' ∈ R_B, ∀ c₁ ∈ C_B, ∀ c₂' ∈ C_B,
      A r₁ c₁ = true → A r₂' c₁ = true → A r₂' c₂' = true → A r₁ c₂' = true := by
    intro i₁ hi1 i₂ hi2 j₁ hj1 j₂ hj2 h11 h21 h22
    have si1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2
    have si2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi2).1).2
    have sj1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hj1).1).2
    have sj2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hj2).1).2
    rw [hAB i₁ j₁ si1.2.1 sj1.2.1] at h11
    rw [hAB i₂ j₁ si2.2.1 sj1.2.1] at h21
    rw [hAB i₂ j₂ si2.2.1 sj2.2.1] at h22
    rw [hAB i₁ j₂ si1.2.1 sj2.2.1]
    rcases evalT_rect d sd hf_not false true hT010 i₁ i₂ j₁ j₂ h11 h21 h22 with h | h | h
    · exact h
    · have : B (sBit (n + j₁.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [sj1.2.2]
      dsimp only [B] at this; rw [h] at this; cases this
    · have : B (sBit i₂.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [si2.2.2]
      dsimp only [B] at this; rw [h] at this; cases this
  have hneR_B : ∀ i ∈ R_B, ∃ j ∈ C_B, A i j = true := by
    intro i hi
    obtain ⟨j, hjC, hij⟩ := (Finset.mem_filter.mp hi).2
    have hiR : i ∈ R_rest := (Finset.mem_filter.mp hi).1
    exact ⟨j, Finset.mem_filter.mpr ⟨hjC, i, hiR, hij⟩, hij⟩
  have hneC_B : ∀ j ∈ C_B, ∃ i ∈ R_B, A i j = true := by
    intro j hj
    obtain ⟨i, hiR, hij⟩ := (Finset.mem_filter.mp hj).2
    have hjC : j ∈ C_rest := (Finset.mem_filter.mp hj).1
    exact ⟨i, Finset.mem_filter.mpr ⟨hiR, j, hjC, hij⟩, hij⟩
  have hc2_nf : ¬ reaches (n + m) d.E d.L (n + c₂.val) d.f := fun h => hc2_v1 ((hv1_c c₂).mp h).symm
  have hr2_nf : ¬ reaches (n + m) d.E d.L r₂.val d.f := fun h => hr2_u1 ((hu1_r r₂).mp h).symm
  have hinjR_B : ∀ i₁ ∈ R_B, ∀ i₂ ∈ R_B, i₁ ≠ i₂ → ∃ j ∈ C_B, A i₁ j ≠ A i₂ j := by
    intro i₁ hi1 i₂ hi2 hne
    by_contra hsame
    have hs : ∀ j ∈ C_B, A i₁ j = A i₂ j := fun j hj => by
      by_contra hd; exact hsame ⟨j, hj, hd⟩
    obtain ⟨c, hcB, hi1c⟩ := hneR_B i₁ hi1
    have hi2c : A i₂ c = true := by rw [← hs c hcB]; exact hi1c
    have hi1R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2
    have hi2R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi2).1).2
    have hcC := (Finset.mem_filter.mp (Finset.mem_filter.mp hcB).1).2
    have hc_nf : ¬ reaches (n + m) d.E d.L (n + c.val) d.f := fun h => hcC.2.1 ((hv1_c c).mp h)
    have hBc : B (sBit (n + c.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [hcC.2.2]
    have hi1_ne3 : i₁ ≠ r₃ := by
      intro hi1_3
      have hi2_nf : ¬ reaches (n + m) d.E d.L i₂.val d.f := fun h => hi2R.2.1 ((hu1_r i₂).mp h)
      have hBi2 : B (sBit i₂.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [hi2R.2.2]
      have hFi2 := F_witness_match_unique hg d sd hf_not (w_f := r₃.val) (w_m := n + c.val) (w_2 := i₂.val) (w_c := n + c₂.val)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro e; apply hne; ext; rw [hi1_3]; exact e) (by omega)
        hr3_nf hc_nf hi2_nf hc2_nf hFr3 hBr3 hBc
        (by rw [show pairBit _ _ = oneEachRaw n m r₃ c from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r₃ c hr3_u1.symm hcC.2.1).symm.trans (hi1_3 ▸ hi1c))
        hBi2
        (by rw [show pairBit _ _ = oneEachRaw n m i₂ c from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB i₂ c hi2R.2.1 hcC.2.1).symm.trans hi2c)
        hBc2 hFc2
      have h_eq := hA_v1_iff i₂; rw [hA_v1_F] at h_eq; dsimp only [F] at h_eq; rw [hFi2] at h_eq
      exact hne (hi1_3.trans (by simp at h_eq; exact h_eq.symm))
    have hi2_ne3 : i₂ ≠ r₃ := by
      intro hi2_3
      have hi1_nf : ¬ reaches (n + m) d.E d.L i₁.val d.f := fun h => hi1R.2.1 ((hu1_r i₁).mp h)
      have hBi1 : B (sBit i₁.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [hi1R.2.2]
      have hFi1 := F_witness_match_unique hg d sd hf_not (w_f := r₃.val) (w_m := n + c.val) (w_2 := i₁.val) (w_c := n + c₂.val)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro e; apply hne; ext; rw [hi2_3]; exact e.symm) (by omega)
        hr3_nf hc_nf hi1_nf hc2_nf hFr3 hBr3 hBc
        (by rw [show pairBit _ _ = oneEachRaw n m r₃ c from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r₃ c hr3_u1.symm hcC.2.1).symm.trans (hi2_3 ▸ hi2c))
        hBi1
        (by rw [show pairBit _ _ = oneEachRaw n m i₁ c from by funext z; simp [pairBit, oneEachRaw]]; exact (hAB i₁ c hi1R.2.1 hcC.2.1).symm.trans hi1c)
        hBc2 hFc2
      have h_eq := hA_v1_iff i₁; rw [hA_v1_F] at h_eq; dsimp only [F] at h_eq; rw [hFi1] at h_eq
      exact hne (by simp at h_eq; exact h_eq.trans hi2_3.symm)
    apply hne; apply hg.1; funext j
    by_cases hjB : j ∈ C_B
    · exact hs j hjB
    · by_cases hj0 : j = d.c₀
      · subst hj0; simp [hA_c0_iff, hi1R.2.2, hi2R.2.2]
      · by_cases hjv : j = v₁
        · subst hjv; simp [hA_v1_iff, hi1_ne3, hi2_ne3]
        · by_cases hj2 : j = c₂
          · subst hj2; simp [hc2_spec.1 i₁ hi1R.2.1, hc2_spec.1 i₂ hi2R.2.1]
          · have hjC : j ∈ C_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjv, hj2⟩
            have ha1 : A i₁ j = false := Bool.eq_false_iff.mpr fun h => hjB (Finset.mem_filter.mpr ⟨hjC, i₁, (Finset.mem_filter.mp hi1).1, h⟩)
            have ha2 : A i₂ j = false := Bool.eq_false_iff.mpr fun h => hjB (Finset.mem_filter.mpr ⟨hjC, i₂, (Finset.mem_filter.mp hi2).1, h⟩)
            rw [ha1, ha2]
  have hinjC_B : ∀ j₁ ∈ C_B, ∀ j₂ ∈ C_B, j₁ ≠ j₂ → ∃ i ∈ R_B, A i j₁ ≠ A i j₂ := by
    intro j₁ hj1 j₂ hj2 hne
    by_contra hsame
    have hs : ∀ i ∈ R_B, A i j₁ = A i j₂ := fun i hi => by
      by_contra hd; exact hsame ⟨i, hi, hd⟩
    obtain ⟨r, hrB, hrj1⟩ := hneC_B j₁ hj1
    have hrj2 : A r j₂ = true := by rw [← hs r hrB]; exact hrj1
    have hj1C := (Finset.mem_filter.mp (Finset.mem_filter.mp hj1).1).2
    have hj2C := (Finset.mem_filter.mp (Finset.mem_filter.mp hj2).1).2
    have hrR := (Finset.mem_filter.mp (Finset.mem_filter.mp hrB).1).2
    have hr_nf : ¬ reaches (n + m) d.E d.L r.val d.f := fun h => hrR.2.1 ((hu1_r r).mp h)
    have hBr : B (sBit r.val) = false := by rw [← hA_c0_B, hA_c0_iff]; simp [hrR.2.2]
    have hj1_ne3 : j₁ ≠ c₃ := by
      intro hj1_3
      have hj2_nf : ¬ reaches (n + m) d.E d.L (n + j₂.val) d.f := fun h => hj2C.2.1 ((hv1_c j₂).mp h)
      have hBj2 : B (sBit (n + j₂.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [hj2C.2.2]
      have hFj2 := F_witness_match_unique hg d sd hf_not (w_f := n + c₃.val) (w_m := r.val) (w_2 := n + j₂.val) (w_c := r₂.val)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun e => hne (Fin.ext (by rw [hj1_3]; exact Nat.add_left_cancel e))) (by omega)
        hc3_nf hr_nf hj2_nf hr2_nf hFc3 hBc3 hBr
        (by rw [show pairBit _ _ = oneEachRaw n m r c₃ from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r c₃ hrR.2.1 hc3_v1.symm).symm.trans (hj1_3 ▸ hrj1))
        hBj2
        (by rw [show pairBit _ _ = oneEachRaw n m r j₂ from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r j₂ hrR.2.1 hj2C.2.1).symm.trans hrj2)
        hBr2 hFr2
      have h_eq := hA_u1_iff j₂; rw [hA_u1_F] at h_eq; dsimp only [F] at h_eq; rw [hFj2] at h_eq
      exact hne (hj1_3.trans (by simp at h_eq; exact h_eq.symm))
    have hj2_ne3 : j₂ ≠ c₃ := by
      intro hj2_3
      have hj1_nf : ¬ reaches (n + m) d.E d.L (n + j₁.val) d.f := fun h => hj1C.2.1 ((hv1_c j₁).mp h)
      have hBj1 : B (sBit (n + j₁.val)) = false := by rw [← hA_r0_B, hA_r0_iff]; simp [hj1C.2.2]
      have hFj1 := F_witness_match_unique hg d sd hf_not (w_f := n + c₃.val) (w_m := r.val) (w_2 := n + j₁.val) (w_c := r₂.val)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun e => hne (Fin.ext (by rw [hj2_3]; exact (Nat.add_left_cancel e).symm))) (by omega)
        hc3_nf hr_nf hj1_nf hr2_nf hFc3 hBc3 hBr
        (by rw [show pairBit _ _ = oneEachRaw n m r c₃ from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r c₃ hrR.2.1 hc3_v1.symm).symm.trans (hj2_3 ▸ hrj2))
        hBj1
        (by rw [show pairBit _ _ = oneEachRaw n m r j₁ from by funext z; simp [pairBit, oneEachRaw, or_comm]]; exact (hAB r j₁ hrR.2.1 hj1C.2.1).symm.trans hrj1)
        hBr2 hFr2
      have h_eq := hA_u1_iff j₁; rw [hA_u1_F] at h_eq; dsimp only [F] at h_eq; rw [hFj1] at h_eq
      exact hne (by simp at h_eq; exact h_eq.trans hj2_3.symm)
    apply hne; apply hg.2.1; funext i; dsimp only
    by_cases hiB : i ∈ R_B
    · exact hs i hiB
    · by_cases hi0 : i = d.r₀
      · subst hi0; simp [hA_r0_iff, hj1C.2.2, hj2C.2.2]
      · by_cases hiu : i = u₁
        · subst hiu; simp [hA_u1_iff, hj1_ne3, hj2_ne3]
        · by_cases hi2 : i = r₂
          · subst hi2; simp [hr2_spec.1 j₁ hj1C.2.1, hr2_spec.1 j₂ hj2C.2.1]
          · have hiR : i ∈ R_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hiu, hi2⟩
            have ha1 : A i j₁ = false := Bool.eq_false_iff.mpr fun h => hiB (Finset.mem_filter.mpr ⟨hiR, j₁, (Finset.mem_filter.mp hj1).1, h⟩)
            have ha2 : A i j₂ = false := Bool.eq_false_iff.mpr fun h => hiB (Finset.mem_filter.mpr ⟨hiR, j₂, (Finset.mem_filter.mp hj2).1, h⟩)
            rw [ha1, ha2]
  obtain ⟨e_B, heB⟩ := deduce_matching R_B C_B A hinjR_B hinjC_B hneR_B hneC_B hrect_B
  exact ⟨u₁, r₂, r₃, v₁, c₂, c₃, hr0_u1, hr2_r0, hr3_r0, hr2_u1, hr3_u1, hr3_r2,
    hc0_v1, hc2_c0, hc3_c0, hc2_v1, hc3_v1, hc3_c2,
    hA_r0_iff, hA_u1_iff, hA_c0_iff, hA_v1_iff, hr2_spec.1, hc2_spec.1, hr3_c3_false,
    hR_cov, hC_cov, e_B, heB⟩

-- Block D: Residual Bijection & Complete Good-Matrix Classification

theorem classification_of_good {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    {A : Fin n → Fin m → Bool} (hg : Good n m A) :
    ∃ (fr fc : Bool),
      (if fr then 5 else 4) ≤ n ∧ (if fc then 5 else 4) ≤ m ∧
      n - (if fr then 1 else 0) = m - (if fc then 1 else 0) ∧
      ∃ (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
        ∀ i j, A i j =
          if (e i).val < 4 ∧ (f j).val < 4 then
            match (e i).val, (f j).val with
            | 0, 2 => true
            | 1, 3 => true
            | 2, 0 => true
            | 2, 2 => true
            | 2, 3 => true
            | 3, 1 => true
            | 3, 2 => true
            | _, _ => false
          else if (e i).val < 4 then
            decide ((e i).val = 2) || (fc && decide ((e i).val = 3 ∧ (f j).val = 4))
          else if (f j).val < 4 then
            decide ((f j).val = 2) || (fr && decide ((f j).val = 3 ∧ (e i).val = 4))
          else
            let sr := 4 + if fr then 1 else 0
            let sc := 4 + if fc then 1 else 0
            decide (sr ≤ (e i).val ∧ sc ≤ (f j).val ∧ (e i).val - sr = (f j).val - sc) := by
  classical
  obtain ⟨d⟩ := extract_collision hn hm hg
  obtain ⟨sd⟩ := split_data_of_collision hg d
  have hA00 := A_r0_c0_false hg d sd
  obtain ⟨u_not, hun_in, _⟩ := d.hjnot_in
  have hf_not : (gateAt d.E d.j_not).inputs = [d.f] := (u_not_eq_f hg d sd hA00 hun_in) ▸ hun_in
  obtain ⟨u₁, r₂, r₃, v₁, c₂, c₃,
    hr0_u1, hr0_r2, hr0_r3, hu1_r2, hu1_r3, hr2_r3,
    hc0_v1, hc0_c2, hc0_c3, hv1_c2, hv1_c3, hc2_c3,
    hA_r0, hA_u1, hA_c0, hA_v1, hr2_true, hc2_true, hr3_c3,
    hR_cov, hC_cov, e_B, heB⟩ := core_classification hg d sd hA00 hf_not
  let R_rest := Finset.univ.filter fun i : Fin n => i ≠ d.r₀ ∧ i ≠ u₁ ∧ i ≠ r₂
  let C_rest := Finset.univ.filter fun j : Fin m => j ≠ d.c₀ ∧ j ≠ v₁ ∧ j ≠ c₂
  let R_B := R_rest.filter fun i => ∃ j ∈ C_rest, A i j = true
  let C_B := C_rest.filter fun j => ∃ i ∈ R_rest, A i j = true
  let fr : Bool := decide (c₃ ∈ C_B)
  let fc : Bool := decide (r₃ ∈ R_B)
  let r_spec : Fin n := if hc3 : c₃ ∈ C_B then (e_B.symm ⟨c₃, hc3⟩).1 else d.r₀
  let c_spec : Fin m := if hr3 : r₃ ∈ R_B then (e_B ⟨r₃, hr3⟩).1 else d.c₀
  have hr_spec_mem (hc3 : c₃ ∈ C_B) : r_spec ∈ R_B := by
    dsimp only [r_spec]; rw [dif_pos hc3]; exact (e_B.symm ⟨c₃, hc3⟩).2
  have hc_spec_mem (hr3 : r₃ ∈ R_B) : c_spec ∈ C_B := by
    dsimp only [c_spec]; rw [dif_pos hr3]; exact (e_B ⟨r₃, hr3⟩).2
  have hr_spec_ne3 (hc3 : c₃ ∈ C_B) : r_spec ≠ r₃ := by
    intro h
    have heq := heB ⟨r_spec, hr_spec_mem hc3⟩ ⟨c₃, hc3⟩
    have hv : e_B ⟨r_spec, hr_spec_mem hc3⟩ = ⟨c₃, hc3⟩ := by
      have h1 : (⟨r_spec, hr_spec_mem hc3⟩ : {r // r ∈ R_B}) = e_B.symm ⟨c₃, hc3⟩ :=
        Subtype.ext (by dsimp only [r_spec]; rw [dif_pos hc3])
      rw [h1, Equiv.apply_symm_apply]
    change A r_spec c₃ = decide (e_B ⟨r_spec, hr_spec_mem hc3⟩ = ⟨c₃, hc3⟩) at heq
    rw [hv] at heq; simp at heq; rw [h, hr3_c3] at heq; cases heq
  have hc_spec_ne3 (hr3 : r₃ ∈ R_B) : c_spec ≠ c₃ := by
    intro h
    have heq := heB ⟨r₃, hr3⟩ ⟨c_spec, hc_spec_mem hr3⟩
    have hv : e_B ⟨r₃, hr3⟩ = ⟨c_spec, hc_spec_mem hr3⟩ :=
      Subtype.ext (by dsimp only [c_spec]; rw [dif_pos hr3])
    change A r₃ c_spec = decide (e_B ⟨r₃, hr3⟩ = ⟨c_spec, hc_spec_mem hr3⟩) at heq
    rw [hv] at heq; simp at heq; rw [h, hr3_c3] at heq; cases heq
  have hr_spec_R (hc3 : c₃ ∈ C_B) : r_spec ∈ R_rest := (Finset.mem_filter.mp (hr_spec_mem hc3)).1
  have hc_spec_C (hr3 : r₃ ∈ R_B) : c_spec ∈ C_rest := (Finset.mem_filter.mp (hc_spec_mem hr3)).1
  have hr_spec_r0 (hc3 : c₃ ∈ C_B) : r_spec ≠ d.r₀ := (Finset.mem_filter.mp (hr_spec_R hc3)).2.1
  have hr_spec_u1 (hc3 : c₃ ∈ C_B) : r_spec ≠ u₁ := (Finset.mem_filter.mp (hr_spec_R hc3)).2.2.1
  have hr_spec_r2 (hc3 : c₃ ∈ C_B) : r_spec ≠ r₂ := (Finset.mem_filter.mp (hr_spec_R hc3)).2.2.2
  have hc_spec_c0 (hr3 : r₃ ∈ R_B) : c_spec ≠ d.c₀ := (Finset.mem_filter.mp (hc_spec_C hr3)).2.1
  have hc_spec_v1 (hr3 : r₃ ∈ R_B) : c_spec ≠ v₁ := (Finset.mem_filter.mp (hc_spec_C hr3)).2.2.1
  have hc_spec_c2 (hr3 : r₃ ∈ R_B) : c_spec ≠ c₂ := (Finset.mem_filter.mp (hc_spec_C hr3)).2.2.2
  let R_tail := R_rest.filter fun i => i ≠ r₃ ∧ (c₃ ∈ C_B → i ≠ r_spec)
  let C_tail := C_rest.filter fun j => j ≠ c₃ ∧ (r₃ ∈ R_B → j ≠ c_spec)
  have hR_tail_B : ∀ i ∈ R_tail, i ∈ R_B := fun i hi =>
    hR_cov i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2.1
  have hC_tail_B : ∀ j ∈ C_tail, j ∈ C_B := fun j hj =>
    hC_cov j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2.1
  have heB_tail (i : Fin n) (hi : i ∈ R_tail) : (e_B ⟨i, hR_tail_B i hi⟩).1 ∈ C_tail := by
    let c := e_B ⟨i, hR_tail_B i hi⟩
    have hcC : c.1 ∈ C_rest := (Finset.mem_filter.mp c.2).1
    have hc3 : c.1 ≠ c₃ := by
      intro hc
      have hc3B : c₃ ∈ C_B := hc ▸ c.2
      have hv : e_B ⟨i, hR_tail_B i hi⟩ = ⟨c₃, hc3B⟩ := Subtype.ext hc
      have hi_eq := congrArg (fun x => (e_B.symm x).1) hv
      rw [Equiv.symm_apply_apply] at hi_eq
      exact (Finset.mem_filter.mp hi).2.2 hc3B (by dsimp only [r_spec]; rw [dif_pos hc3B]; exact hi_eq)
    have hcs : ∀ hr3 : r₃ ∈ R_B, c.1 ≠ c_spec := by
      intro hr3 hs
      have hv : e_B ⟨i, hR_tail_B i hi⟩ = e_B ⟨r₃, hr3⟩ := by
        apply Subtype.ext; dsimp only [c_spec] at hs; rw [dif_pos hr3] at hs; exact hs
      have hi_eq : i = r₃ := congrArg Subtype.val (e_B.injective hv)
      exact (Finset.mem_filter.mp hi).2.1 hi_eq
    exact Finset.mem_filter.mpr ⟨hcC, hc3, hcs⟩
  have heB_symm_tail (j : Fin m) (hj : j ∈ C_tail) : (e_B.symm ⟨j, hC_tail_B j hj⟩).1 ∈ R_tail := by
    let r := e_B.symm ⟨j, hC_tail_B j hj⟩
    have hrR : r.1 ∈ R_rest := (Finset.mem_filter.mp r.2).1
    have hr3 : r.1 ≠ r₃ := by
      intro hr
      have hr3B : r₃ ∈ R_B := hr ▸ r.2
      have hv : e_B.symm ⟨j, hC_tail_B j hj⟩ = ⟨r₃, hr3B⟩ := Subtype.ext hr
      have hj_eq := congrArg (fun x => (e_B x).1) hv
      rw [Equiv.apply_symm_apply] at hj_eq
      exact (Finset.mem_filter.mp hj).2.2 hr3B (by dsimp only [c_spec]; rw [dif_pos hr3B]; exact hj_eq)
    have hrs : ∀ hc3 : c₃ ∈ C_B, r.1 ≠ r_spec := by
      intro hc3 hs
      have hv : e_B.symm ⟨j, hC_tail_B j hj⟩ = e_B.symm ⟨c₃, hc3⟩ := by
        apply Subtype.ext; dsimp only [r_spec] at hs; rw [dif_pos hc3] at hs; exact hs
      have hj_eq : j = c₃ := congrArg Subtype.val (e_B.symm.injective hv)
      exact (Finset.mem_filter.mp hj).2.1 hj_eq
    exact Finset.mem_filter.mpr ⟨hrR, hr3, hrs⟩
  let e_tail : {i // i ∈ R_tail} ≃ {j // j ∈ C_tail} :=
    { toFun := fun ⟨i, hi⟩ => ⟨(e_B ⟨i, hR_tail_B i hi⟩).1, heB_tail i hi⟩
      invFun := fun ⟨j, hj⟩ => ⟨(e_B.symm ⟨j, hC_tail_B j hj⟩).1, heB_symm_tail j hj⟩
      left_inv := fun ⟨i, hi⟩ => by
        apply Subtype.ext
        change (e_B.symm ⟨(e_B ⟨i, hR_tail_B i hi⟩).1, hC_tail_B _ (heB_tail i hi)⟩).1 = i
        rw [show (⟨(e_B ⟨i, hR_tail_B i hi⟩).1, hC_tail_B _ (heB_tail i hi)⟩ : {c // c ∈ C_B}) =
            e_B ⟨i, hR_tail_B i hi⟩ from Subtype.ext rfl, Equiv.symm_apply_apply]
      right_inv := fun ⟨j, hj⟩ => by
        apply Subtype.ext
        change (e_B ⟨(e_B.symm ⟨j, hC_tail_B j hj⟩).1, hR_tail_B _ (heB_symm_tail j hj)⟩).1 = j
        rw [show (⟨(e_B.symm ⟨j, hC_tail_B j hj⟩).1, hR_tail_B _ (heB_symm_tail j hj)⟩ : {r // r ∈ R_B}) =
            e_B.symm ⟨j, hC_tail_B j hj⟩ from Subtype.ext rfl, Equiv.apply_symm_apply] }
  let sr : ℕ := 4 + if fr then 1 else 0
  let sc : ℕ := 4 + if fc then 1 else 0
  let coreRows : Finset (Fin n) := if c₃ ∈ C_B then {d.r₀, u₁, r₂, r₃, r_spec} else {d.r₀, u₁, r₂, r₃}
  let coreCols : Finset (Fin m) := if r₃ ∈ R_B then {d.c₀, v₁, c₂, c₃, c_spec} else {d.c₀, v₁, c₂, c₃}
  have hcoreR_card : coreRows.card = sr := by
    dsimp only [coreRows, sr, fr]
    by_cases hc3 : c₃ ∈ C_B
    · simp only [hc3, ↓reduceIte, decide_true]
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hr0_u1, hr0_r2, hr0_r3, (hr_spec_r0 hc3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hu1_r2, hu1_r3, (hr_spec_u1 hc3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hr2_r3, (hr_spec_r2 hc3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact (hr_spec_ne3 hc3).symm),
          Finset.card_singleton]
    · rw [if_neg hc3, show (4 + if decide (c₃ ∈ C_B) = true then 1 else 0) = 4 from by rw [decide_eq_false hc3]; rfl]
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hr0_u1, hr0_r2, hr0_r3⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hu1_r2, hu1_r3⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hr2_r3),
          Finset.card_singleton]
  have hcoreC_card : coreCols.card = sc := by
    dsimp only [coreCols, sc, fc]
    by_cases hr3 : r₃ ∈ R_B
    · simp only [hr3, ↓reduceIte, decide_true]
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hc0_v1, hc0_c2, hc0_c3, (hc_spec_c0 hr3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv1_c2, hv1_c3, (hc_spec_v1 hr3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hc2_c3, (hc_spec_c2 hr3).symm⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact (hc_spec_ne3 hr3).symm),
          Finset.card_singleton]
    · rw [if_neg hr3, show (4 + if decide (r₃ ∈ R_B) = true then 1 else 0) = 4 from by rw [decide_eq_false hr3]; rfl]
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hc0_v1, hc0_c2, hc0_c3⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv1_c2, hv1_c3⟩),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hc2_c3),
          Finset.card_singleton]
  have hdisjR : Disjoint coreRows R_tail := Finset.disjoint_left.mpr fun i hi1 hi2 => by
    have hs := Finset.mem_filter.mp hi2
    have hR := (Finset.mem_filter.mp hs.1).2
    dsimp only [coreRows] at hi1
    by_cases hc3 : c₃ ∈ C_B
    · rw [if_pos hc3] at hi1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi1
      rcases hi1 with rfl | rfl | rfl | rfl | rfl
      · exact hR.1 rfl
      · exact hR.2.1 rfl
      · exact hR.2.2 rfl
      · exact hs.2.1 rfl
      · exact hs.2.2 hc3 rfl
    · rw [if_neg hc3] at hi1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi1
      rcases hi1 with rfl | rfl | rfl | rfl
      · exact hR.1 rfl
      · exact hR.2.1 rfl
      · exact hR.2.2 rfl
      · exact hs.2.1 rfl
  have hdisjC : Disjoint coreCols C_tail := Finset.disjoint_left.mpr fun j hj1 hj2 => by
    have hs := Finset.mem_filter.mp hj2
    have hC := (Finset.mem_filter.mp hs.1).2
    dsimp only [coreCols] at hj1
    by_cases hr3 : r₃ ∈ R_B
    · rw [if_pos hr3] at hj1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
      rcases hj1 with rfl | rfl | rfl | rfl | rfl
      · exact hC.1 rfl
      · exact hC.2.1 rfl
      · exact hC.2.2 rfl
      · exact hs.2.1 rfl
      · exact hs.2.2 hr3 rfl
    · rw [if_neg hr3] at hj1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
      rcases hj1 with rfl | rfl | rfl | rfl
      · exact hC.1 rfl
      · exact hC.2.1 rfl
      · exact hC.2.2 rfl
      · exact hs.2.1 rfl
  have hunionR : coreRows ∪ R_tail = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i => by
    rw [Finset.mem_union]
    by_cases h1 : i = d.r₀ ∨ i = u₁ ∨ i = r₂ ∨ i = r₃ ∨ (c₃ ∈ C_B ∧ i = r_spec)
    · left; dsimp only [coreRows]
      by_cases hc3 : c₃ ∈ C_B
      · rw [if_pos hc3]; simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h1 with rfl | rfl | rfl | rfl | ⟨_, rfl⟩ <;> simp only [true_or, or_true]
      · rw [if_neg hc3]; simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h1 with rfl | rfl | rfl | rfl | ⟨hc, _⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd hc hc3
    · right; rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun e => h1 (Or.inl e), fun e => h1 (Or.inr (Or.inl e)),
        fun e => h1 (Or.inr (Or.inr (Or.inl e)))⟩,
        fun e => h1 (Or.inr (Or.inr (Or.inr (Or.inl e)))),
        fun hc3 e => h1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc3, e⟩))))⟩
  have hunionC : coreCols ∪ C_tail = Finset.univ := Finset.eq_univ_iff_forall.mpr fun j => by
    rw [Finset.mem_union]
    by_cases h1 : j = d.c₀ ∨ j = v₁ ∨ j = c₂ ∨ j = c₃ ∨ (r₃ ∈ R_B ∧ j = c_spec)
    · left; dsimp only [coreCols]
      by_cases hr3 : r₃ ∈ R_B
      · rw [if_pos hr3]; simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h1 with rfl | rfl | rfl | rfl | ⟨_, rfl⟩ <;> simp only [true_or, or_true]
      · rw [if_neg hr3]; simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h1 with rfl | rfl | rfl | rfl | ⟨hr, _⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd hr hr3
    · right; rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun e => h1 (Or.inl e), fun e => h1 (Or.inr (Or.inl e)),
        fun e => h1 (Or.inr (Or.inr (Or.inl e)))⟩,
        fun e => h1 (Or.inr (Or.inr (Or.inr (Or.inl e)))),
        fun hr3 e => h1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr3, e⟩))))⟩
  have hcardR : sr + R_tail.card = n := by
    rw [← hcoreR_card, ← Finset.card_union_of_disjoint hdisjR, hunionR, Finset.card_univ, Fintype.card_fin]
  have hcardC : sc + C_tail.card = m := by
    rw [← hcoreC_card, ← Finset.card_union_of_disjoint hdisjC, hunionC, Finset.card_univ, Fintype.card_fin]
  have htail_eq : R_tail.card = C_tail.card := by
    have := Fintype.card_congr e_tail
    simpa only [Fintype.card_coe] using this
  have hsr_pos (hc3 : c₃ ∈ C_B) : sr = 5 := by dsimp only [sr, fr]; rw [if_pos (decide_eq_true hc3)]
  have hsr_neg (hc3 : c₃ ∉ C_B) : sr = 4 := by dsimp only [sr, fr]; rw [if_neg (by rw [decide_eq_false hc3]; decide)]
  have hsc_pos (hr3 : r₃ ∈ R_B) : sc = 5 := by dsimp only [sc, fc]; rw [if_pos (decide_eq_true hr3)]
  have hsc_neg (hr3 : r₃ ∉ R_B) : sc = 4 := by dsimp only [sc, fc]; rw [if_neg (by rw [decide_eq_false hr3]; decide)]
  have hn_bound : (if fr then 5 else 4) ≤ n := by
    by_cases hc3 : c₃ ∈ C_B
    · have h5 := hsr_pos hc3; rw [h5] at hcardR; dsimp only [fr]; rw [if_pos (decide_eq_true hc3)]; omega
    · have h4 := hsr_neg hc3; rw [h4] at hcardR; dsimp only [fr]; rw [if_neg (by rw [decide_eq_false hc3]; decide)]; omega
  have hm_bound : (if fc then 5 else 4) ≤ m := by
    by_cases hr3 : r₃ ∈ R_B
    · have h5 := hsc_pos hr3; rw [h5] at hcardC; dsimp only [fc]; rw [if_pos (decide_eq_true hr3)]; omega
    · have h4 := hsc_neg hr3; rw [h4] at hcardC; dsimp only [fc]; rw [if_neg (by rw [decide_eq_false hr3]; decide)]; omega
  have heq_len : n - (if fr then 1 else 0) = m - (if fc then 1 else 0) := by
    by_cases hc3 : c₃ ∈ C_B <;> by_cases hr3 : r₃ ∈ R_B
    · have hs5 := hsr_pos hc3; rw [hs5] at hcardR; have hc5 := hsc_pos hr3; rw [hc5] at hcardC
      dsimp only [fr, fc]; rw [if_pos (decide_eq_true hc3), if_pos (decide_eq_true hr3)]; omega
    · have hs5 := hsr_pos hc3; rw [hs5] at hcardR; have hc4 := hsc_neg hr3; rw [hc4] at hcardC
      dsimp only [fr, fc]; rw [if_pos (decide_eq_true hc3), if_neg (by rw [decide_eq_false hr3]; decide)]; omega
    · have hs4 := hsr_neg hc3; rw [hs4] at hcardR; have hc5 := hsc_pos hr3; rw [hc5] at hcardC
      dsimp only [fr, fc]; rw [if_neg (by rw [decide_eq_false hc3]; decide), if_pos (decide_eq_true hr3)]; omega
    · have hs4 := hsr_neg hc3; rw [hs4] at hcardR; have hc4 := hsc_neg hr3; rw [hc4] at hcardC
      dsimp only [fr, fc]; rw [if_neg (by rw [decide_eq_false hc3]; decide), if_neg (by rw [decide_eq_false hr3]; decide)]; omega
  let finR : Fin R_tail.card ≃ {i // i ∈ R_tail} :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe R_tail)).symm
  let finC : Fin R_tail.card ≃ {j // j ∈ C_tail} := finR.trans e_tail
  let φ_R_fn (a : Fin n) : Fin n :=
    if h0 : a.val = 0 then d.r₀
    else if h1 : a.val = 1 then u₁
    else if h2 : a.val = 2 then r₂
    else if h3 : a.val = 3 then r₃
    else if h4 : c₃ ∈ C_B ∧ a.val = 4 then r_spec
    else (finR ⟨a.val - sr, by
      have := a.isLt
      by_cases hc3 : c₃ ∈ C_B
      · have h5 := hsr_pos hc3; rw [h5] at hcardR ⊢; have : a.val ≠ 4 := fun e => h4 ⟨hc3, e⟩; omega
      · have h4s := hsr_neg hc3; rw [h4s] at hcardR ⊢; omega⟩).1
  let φ_C_fn (b : Fin m) : Fin m :=
    if h0 : b.val = 0 then d.c₀
    else if h1 : b.val = 1 then v₁
    else if h2 : b.val = 2 then c₂
    else if h3 : b.val = 3 then c₃
    else if h4 : r₃ ∈ R_B ∧ b.val = 4 then c_spec
    else (finC ⟨b.val - sc, by
      have := b.isLt; rw [htail_eq]
      by_cases hr3 : r₃ ∈ R_B
      · have h5 := hsc_pos hr3; rw [h5] at hcardC ⊢; have : b.val ≠ 4 := fun e => h4 ⟨hr3, e⟩; omega
      · have h4s := hsc_neg hr3; rw [h4s] at hcardC ⊢; omega⟩).1
  have hR_val (a : Fin n) :
      (a.val = 0 ∧ φ_R_fn a = d.r₀) ∨
      (a.val = 1 ∧ φ_R_fn a = u₁) ∨
      (a.val = 2 ∧ φ_R_fn a = r₂) ∨
      (a.val = 3 ∧ φ_R_fn a = r₃) ∨
      (c₃ ∈ C_B ∧ a.val = 4 ∧ φ_R_fn a = r_spec) ∨
      (sr ≤ a.val ∧ φ_R_fn a ∈ R_tail) := by
    by_cases h0 : a.val = 0
    · exact Or.inl ⟨h0, by dsimp only [φ_R_fn]; rw [dif_pos h0]⟩
    · by_cases h1 : a.val = 1
      · exact Or.inr (Or.inl ⟨h1, by dsimp only [φ_R_fn]; rw [dif_neg h0, dif_pos h1]⟩)
      · by_cases h2 : a.val = 2
        · exact Or.inr (Or.inr (Or.inl ⟨h2, by dsimp only [φ_R_fn]; rw [dif_neg h0, dif_neg h1, dif_pos h2]⟩))
        · by_cases h3 : a.val = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, by dsimp only [φ_R_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_pos h3]⟩)))
          · by_cases h4 : c₃ ∈ C_B ∧ a.val = 4
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4.1, h4.2, by dsimp only [φ_R_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]⟩))))
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
              · by_cases hc3 : c₃ ∈ C_B
                · rw [hsr_pos hc3]; have : a.val ≠ 4 := fun e => h4 ⟨hc3, e⟩; omega
                · rw [hsr_neg hc3]; omega
              · dsimp only [φ_R_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]; exact (finR _).2
  have hC_val (b : Fin m) :
      (b.val = 0 ∧ φ_C_fn b = d.c₀) ∨
      (b.val = 1 ∧ φ_C_fn b = v₁) ∨
      (b.val = 2 ∧ φ_C_fn b = c₂) ∨
      (b.val = 3 ∧ φ_C_fn b = c₃) ∨
      (r₃ ∈ R_B ∧ b.val = 4 ∧ φ_C_fn b = c_spec) ∨
      (sc ≤ b.val ∧ φ_C_fn b ∈ C_tail) := by
    by_cases h0 : b.val = 0
    · exact Or.inl ⟨h0, by dsimp only [φ_C_fn]; rw [dif_pos h0]⟩
    · by_cases h1 : b.val = 1
      · exact Or.inr (Or.inl ⟨h1, by dsimp only [φ_C_fn]; rw [dif_neg h0, dif_pos h1]⟩)
      · by_cases h2 : b.val = 2
        · exact Or.inr (Or.inr (Or.inl ⟨h2, by dsimp only [φ_C_fn]; rw [dif_neg h0, dif_neg h1, dif_pos h2]⟩))
        · by_cases h3 : b.val = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, by dsimp only [φ_C_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_pos h3]⟩)))
          · by_cases h4 : r₃ ∈ R_B ∧ b.val = 4
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4.1, h4.2, by dsimp only [φ_C_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]⟩))))
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
              · by_cases hr3 : r₃ ∈ R_B
                · rw [hsc_pos hr3]; have : b.val ≠ 4 := fun e => h4 ⟨hr3, e⟩; omega
                · rw [hsc_neg hr3]; omega
              · dsimp only [φ_C_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]; exact (finC _).2
  have hR_tail_elim {a} (ha : φ_R_fn a ∈ R_tail) : sr ≤ a.val := by
    rcases hR_val a with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hc, _, v⟩ | ⟨hs, _⟩
    · exfalso; rw [v] at ha; exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.1 rfl
    · exfalso; rw [v] at ha; exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.2.1 rfl
    · exfalso; rw [v] at ha; exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.2.2 rfl
    · exfalso; rw [v] at ha; exact (Finset.mem_filter.mp ha).2.1 rfl
    · exfalso; rw [v] at ha; exact (Finset.mem_filter.mp ha).2.2 hc rfl
    · exact hs
  have hC_tail_elim {b} (hb : φ_C_fn b ∈ C_tail) : sc ≤ b.val := by
    rcases hC_val b with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hr, _, v⟩ | ⟨hs, _⟩
    · exfalso; rw [v] at hb; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.1 rfl
    · exfalso; rw [v] at hb; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.2.1 rfl
    · exfalso; rw [v] at hb; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.2.2 rfl
    · exfalso; rw [v] at hb; exact (Finset.mem_filter.mp hb).2.1 rfl
    · exfalso; rw [v] at hb; exact (Finset.mem_filter.mp hb).2.2 hr rfl
    · exact hs
  have hφR_tail_eq {a : Fin n} (hs : sr ≤ a.val) :
      ∃ h : a.val - sr < R_tail.card, φ_R_fn a = (finR ⟨a.val - sr, h⟩).1 := by
    have h0 : a.val ≠ 0 := by dsimp only [sr] at hs; omega
    have h1 : a.val ≠ 1 := by dsimp only [sr] at hs; omega
    have h2 : a.val ≠ 2 := by dsimp only [sr] at hs; omega
    have h3 : a.val ≠ 3 := by dsimp only [sr] at hs; omega
    have h4 : ¬ (c₃ ∈ C_B ∧ a.val = 4) := fun ⟨hc, e⟩ => by
      dsimp only [sr, fr] at hs; simp [hc] at hs; omega
    refine ⟨by have := a.isLt; omega, ?_⟩
    dsimp only [φ_R_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
  have hφC_tail_eq {b : Fin m} (hs : sc ≤ b.val) :
      ∃ h : b.val - sc < R_tail.card, φ_C_fn b = (finC ⟨b.val - sc, h⟩).1 := by
    have h0 : b.val ≠ 0 := by dsimp only [sc] at hs; omega
    have h1 : b.val ≠ 1 := by dsimp only [sc] at hs; omega
    have h2 : b.val ≠ 2 := by dsimp only [sc] at hs; omega
    have h3 : b.val ≠ 3 := by dsimp only [sc] at hs; omega
    have h4 : ¬ (r₃ ∈ R_B ∧ b.val = 4) := fun ⟨hr, e⟩ => by
      dsimp only [sc, fc] at hs; simp [hr] at hs; omega
    refine ⟨by have := b.isLt; omega, ?_⟩
    dsimp only [φ_C_fn]; rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
  have hR_is0 {a} (h : φ_R_fn a = d.r₀) : a.val = 0 := by
    rcases hR_val a with ⟨e, _⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hc, _, v⟩ | ⟨_, hm⟩
    · exact e
    · rw [v] at h; exact absurd h.symm hr0_u1
    · rw [v] at h; exact absurd h.symm hr0_r2
    · rw [v] at h; exact absurd h.symm hr0_r3
    · rw [v] at h; exact absurd h (hr_spec_r0 hc)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1
  have hR_is1 {a} (h : φ_R_fn a = u₁) : a.val = 1 := by
    rcases hR_val a with ⟨_, v⟩ | ⟨e, _⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hc, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hr0_u1
    · exact e
    · rw [v] at h; exact absurd h.symm hu1_r2
    · rw [v] at h; exact absurd h.symm hu1_r3
    · rw [v] at h; exact absurd h (hr_spec_u1 hc)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.2.1
  have hR_is2 {a} (h : φ_R_fn a = r₂) : a.val = 2 := by
    rcases hR_val a with ⟨_, v⟩ | ⟨_, v⟩ | ⟨e, _⟩ | ⟨_, v⟩ | ⟨hc, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hr0_r2
    · rw [v] at h; exact absurd h hu1_r2
    · exact e
    · rw [v] at h; exact absurd h.symm hr2_r3
    · rw [v] at h; exact absurd h (hr_spec_r2 hc)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.2.2
  have hR_is3 {a} (h : φ_R_fn a = r₃) : a.val = 3 := by
    rcases hR_val a with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨e, _⟩ | ⟨hc, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hr0_r3
    · rw [v] at h; exact absurd h hu1_r3
    · rw [v] at h; exact absurd h hr2_r3
    · exact e
    · rw [v] at h; exact absurd h (hr_spec_ne3 hc)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp hm).2.1
  have hR_is4 {a} (hc : c₃ ∈ C_B) (h : φ_R_fn a = r_spec) : a.val = 4 := by
    rcases hR_val a with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, e, _⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h.symm (hr_spec_r0 hc)
    · rw [v] at h; exact absurd h.symm (hr_spec_u1 hc)
    · rw [v] at h; exact absurd h.symm (hr_spec_r2 hc)
    · rw [v] at h; exact absurd h.symm (hr_spec_ne3 hc)
    · exact e
    · rw [h] at hm; exact absurd rfl ((Finset.mem_filter.mp hm).2.2 hc)
  have hC_is0 {b} (h : φ_C_fn b = d.c₀) : b.val = 0 := by
    rcases hC_val b with ⟨e, _⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hr, _, v⟩ | ⟨_, hm⟩
    · exact e
    · rw [v] at h; exact absurd h.symm hc0_v1
    · rw [v] at h; exact absurd h.symm hc0_c2
    · rw [v] at h; exact absurd h.symm hc0_c3
    · rw [v] at h; exact absurd h (hc_spec_c0 hr)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1
  have hC_is1 {b} (h : φ_C_fn b = v₁) : b.val = 1 := by
    rcases hC_val b with ⟨_, v⟩ | ⟨e, _⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨hr, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hc0_v1
    · exact e
    · rw [v] at h; exact absurd h.symm hv1_c2
    · rw [v] at h; exact absurd h.symm hv1_c3
    · rw [v] at h; exact absurd h (hc_spec_v1 hr)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.2.1
  have hC_is2 {b} (h : φ_C_fn b = c₂) : b.val = 2 := by
    rcases hC_val b with ⟨_, v⟩ | ⟨_, v⟩ | ⟨e, _⟩ | ⟨_, v⟩ | ⟨hr, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hc0_c2
    · rw [v] at h; exact absurd h hv1_c2
    · exact e
    · rw [v] at h; exact absurd h.symm hc2_c3
    · rw [v] at h; exact absurd h (hc_spec_c2 hr)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.2.2
  have hC_is3 {b} (h : φ_C_fn b = c₃) : b.val = 3 := by
    rcases hC_val b with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨e, _⟩ | ⟨hr, _, v⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h hc0_c3
    · rw [v] at h; exact absurd h hv1_c3
    · rw [v] at h; exact absurd h hc2_c3
    · exact e
    · rw [v] at h; exact absurd h (hc_spec_ne3 hr)
    · rw [h] at hm; exact absurd rfl (Finset.mem_filter.mp hm).2.1
  have hC_is4 {b} (hr : r₃ ∈ R_B) (h : φ_C_fn b = c_spec) : b.val = 4 := by
    rcases hC_val b with ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, v⟩ | ⟨_, e, _⟩ | ⟨_, hm⟩
    · rw [v] at h; exact absurd h.symm (hc_spec_c0 hr)
    · rw [v] at h; exact absurd h.symm (hc_spec_v1 hr)
    · rw [v] at h; exact absurd h.symm (hc_spec_c2 hr)
    · rw [v] at h; exact absurd h.symm (hc_spec_ne3 hr)
    · exact e
    · rw [h] at hm; exact absurd rfl ((Finset.mem_filter.mp hm).2.2 hr)
  have hφR_inj : Function.Injective φ_R_fn := by
    intro a₁ a₂ h
    rcases hR_val a₁ with ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨hc1, e1, v1⟩ | ⟨s1, m1⟩
    · exact Fin.ext (e1.trans (hR_is0 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hR_is1 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hR_is2 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hR_is3 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hR_is4 hc1 (v1 ▸ h).symm).symm)
    · have s2 := hR_tail_elim (h ▸ m1)
      obtain ⟨ha1, he1⟩ := hφR_tail_eq s1
      obtain ⟨ha2, he2⟩ := hφR_tail_eq s2
      rw [he1, he2] at h
      have hfin := congrArg Fin.val (finR.injective (Subtype.ext h))
      simp only at hfin
      exact Fin.ext (by omega)
  have hφC_inj : Function.Injective φ_C_fn := by
    intro b₁ b₂ h
    rcases hC_val b₁ with ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨hr1, e1, v1⟩ | ⟨s1, m1⟩
    · exact Fin.ext (e1.trans (hC_is0 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hC_is1 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hC_is2 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hC_is3 (v1 ▸ h).symm).symm)
    · exact Fin.ext (e1.trans (hC_is4 hr1 (v1 ▸ h).symm).symm)
    · have s2 := hC_tail_elim (h ▸ m1)
      obtain ⟨hb1, he1⟩ := hφC_tail_eq s1
      obtain ⟨hb2, he2⟩ := hφC_tail_eq s2
      rw [he1, he2] at h
      have hfin := congrArg Fin.val (finC.injective (Subtype.ext h))
      simp only at hfin
      exact Fin.ext (by omega)
  let φ_R : Equiv.Perm (Fin n) := Equiv.ofBijective φ_R_fn (Finite.injective_iff_bijective.mp hφR_inj)
  let φ_C : Equiv.Perm (Fin m) := Equiv.ofBijective φ_C_fn (Finite.injective_iff_bijective.mp hφC_inj)
  let e : Equiv.Perm (Fin n) := φ_R.symm
  let f : Equiv.Perm (Fin m) := φ_C.symm
  have h_main (a : Fin n) (b : Fin m) :
      A (φ_R_fn a) (φ_C_fn b) =
        if a.val < 4 ∧ b.val < 4 then
          match a.val, b.val with
          | 0, 2 => true
          | 1, 3 => true
          | 2, 0 => true
          | 2, 2 => true
          | 2, 3 => true
          | 3, 1 => true
          | 3, 2 => true
          | _, _ => false
        else if a.val < 4 then
          decide (a.val = 2) || (fc && decide (a.val = 3 ∧ b.val = 4))
        else if b.val < 4 then
          decide (b.val = 2) || (fr && decide (b.val = 3 ∧ a.val = 4))
        else
          decide (sr ≤ a.val ∧ sc ≤ b.val ∧ a.val - sr = b.val - sc) := by
    by_cases ha0 : a.val = 0
    · have hva : φ_R_fn a = d.r₀ := by dsimp only [φ_R_fn]; rw [dif_pos ha0]
      rw [hva, hA_r0]
      have heqb2 : decide (φ_C_fn b = c₂) = decide (b.val = 2) := by
        rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
        exact ⟨hC_is2, fun h => by dsimp only [φ_C_fn]; rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]⟩
      rw [heqb2]
      by_cases hb4 : b.val < 4
      · rw [if_pos ⟨by omega, hb4⟩]
        have : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 3 := by omega
        rcases this with hb | hb | hb | hb <;> simp [ha0, hb]
      · rw [if_neg (by omega), if_pos (by omega)]; simp [ha0, show b.val ≠ 2 by omega]
    · by_cases ha1 : a.val = 1
      · have hva : φ_R_fn a = u₁ := by dsimp only [φ_R_fn]; rw [dif_neg ha0, dif_pos ha1]
        rw [hva, hA_u1]
        have heqb3 : decide (φ_C_fn b = c₃) = decide (b.val = 3) := by
          rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
          exact ⟨hC_is3, fun h => by dsimp only [φ_C_fn]; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos h]⟩
        rw [heqb3]
        by_cases hb4 : b.val < 4
        · rw [if_pos ⟨by omega, hb4⟩]
          have : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 3 := by omega
          rcases this with hb | hb | hb | hb <;> simp [ha1, hb]
        · rw [if_neg (by omega), if_pos (by omega)]; simp [ha1, show b.val ≠ 3 by omega]
      · by_cases ha2 : a.val = 2
        · have hva : φ_R_fn a = r₂ := by dsimp only [φ_R_fn]; rw [dif_neg ha0, dif_neg ha1, dif_pos ha2]
          rw [hva]
          by_cases hb1 : b.val = 1
          · have hvb : φ_C_fn b = v₁ := by dsimp only [φ_C_fn]; rw [dif_neg (by omega), dif_pos hb1]
            rw [hvb, hA_v1, decide_eq_false hr2_r3, if_pos ⟨by omega, by omega⟩]; simp [ha2, hb1]
          · have hvb : φ_C_fn b ≠ v₁ := fun h => hb1 (hC_is1 h)
            rw [hr2_true _ hvb]
            by_cases hb4 : b.val < 4
            · rw [if_pos ⟨by omega, hb4⟩]
              have : b.val = 0 ∨ b.val = 2 ∨ b.val = 3 := by omega
              rcases this with hb | hb | hb <;> simp [ha2, hb]
            · rw [if_neg (by omega), if_pos (by omega)]; simp [ha2]
        · by_cases hb0 : b.val = 0
          · have hvb : φ_C_fn b = d.c₀ := by dsimp only [φ_C_fn]; rw [dif_pos hb0]
            have hva : φ_R_fn a ≠ r₂ := fun h => ha2 (hR_is2 h)
            rw [hvb, hA_c0, decide_eq_false hva]
            by_cases ha4 : a.val < 4
            · have ha3 : a.val = 3 := by omega
              rw [if_pos ⟨ha4, by omega⟩]; simp [ha3, hb0]
            · rw [if_neg (by omega), if_neg ha4, if_pos (by omega)]; simp [hb0]
          · by_cases hb1 : b.val = 1
            · have hvb : φ_C_fn b = v₁ := by dsimp only [φ_C_fn]; rw [dif_neg hb0, dif_pos hb1]
              rw [hvb, hA_v1]
              by_cases ha3 : a.val = 3
              · have hva : φ_R_fn a = r₃ := by dsimp only [φ_R_fn]; rw [dif_neg ha0, dif_neg ha1, dif_neg ha2, dif_pos ha3]
                rw [hva, if_pos ⟨by omega, by omega⟩]; simp [ha3, hb1]
              · have hva : φ_R_fn a ≠ r₃ := fun h => ha3 (hR_is3 h)
                rw [decide_eq_false hva, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp [hb1]
            · by_cases hb2 : b.val = 2
              · have hvb : φ_C_fn b = c₂ := by dsimp only [φ_C_fn]; rw [dif_neg hb0, dif_neg hb1, dif_pos hb2]
                have hva : φ_R_fn a ≠ u₁ := fun h => ha1 (hR_is1 h)
                rw [hvb, hc2_true _ hva]
                by_cases ha4 : a.val < 4
                · have ha3 : a.val = 3 := by omega
                  rw [if_pos ⟨ha4, by omega⟩]; simp [ha3, hb2]
                · rw [if_neg (by omega), if_neg ha4, if_pos (by omega)]; simp [hb2]
              · -- Here a.val ≥ 3 and b.val ≥ 3
                rcases hR_val a with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨ha3, hva⟩ | ⟨hc3, ha4, hva⟩ | ⟨hsr, hma⟩
                · omega
                · omega
                · omega
                · rcases hC_val b with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨hb3, hvb⟩ | ⟨hr3, hb4, hvb⟩ | ⟨hsc, hmb⟩
                  · omega
                  · omega
                  · omega
                  · rw [hva, hvb, hr3_c3, if_pos ⟨by omega, by omega⟩]; simp [ha3, hb3]
                  · have hfc_t : fc = true := decide_eq_true hr3
                    have hAb : A r₃ c_spec = true := by
                      have := heB ⟨r₃, hr3⟩ ⟨c_spec, hc_spec_mem hr3⟩
                      have hv : e_B ⟨r₃, hr3⟩ = ⟨c_spec, hc_spec_mem hr3⟩ :=
                        Subtype.ext (by dsimp only [c_spec]; rw [dif_pos hr3])
                      exact this.trans (decide_eq_true hv)
                    rw [hva, hvb, hAb, if_neg (by omega), if_pos (by omega)]; simp [ha3, hb4, hfc_t]
                  · have hAf : A r₃ (φ_C_fn b) = false := by
                      by_cases hr3 : r₃ ∈ R_B
                      · have hbB : φ_C_fn b ∈ C_B := hC_tail_B _ hmb
                        have hne : φ_C_fn b ≠ c_spec := (Finset.mem_filter.mp hmb).2.2 hr3
                        have hsub : e_B ⟨r₃, hr3⟩ ≠ ⟨φ_C_fn b, hbB⟩ := fun h => hne (by
                          have h1 := congrArg Subtype.val h
                          dsimp only [c_spec]; rw [dif_pos hr3]; exact h1.symm)
                        have := heB ⟨r₃, hr3⟩ ⟨φ_C_fn b, hbB⟩
                        rw [decide_eq_false hsub] at this; exact this
                      · by_contra ht
                        have hbC : φ_C_fn b ∈ C_rest := (Finset.mem_filter.mp hmb).1
                        have hr3R : r₃ ∈ R_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0_r3.symm, hu1_r3.symm, hr2_r3.symm⟩
                        exact hr3 (Finset.mem_filter.mpr ⟨hr3R, φ_C_fn b, hbC, Bool.eq_true_of_not_eq_false ht⟩)
                    have hb_ne4 : b.val ≠ 4 ∨ fc = false := by
                      by_cases hr3 : r₃ ∈ R_B
                      · left; rw [hsc_pos hr3] at hsc; omega
                      · right; dsimp only [fc]; exact decide_eq_false hr3
                    rw [hva, hAf, if_neg (by omega), if_pos (by omega)]
                    rcases hb_ne4 with hb4 | hfc_f
                    · simp [ha3, hb4]
                    · simp [ha3, hfc_f]
                · rcases hC_val b with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨hb3, hvb⟩ | ⟨hr3, hb4, hvb⟩ | ⟨hsc, hmb⟩
                  · omega
                  · omega
                  · omega
                  · have hfr_t : fr = true := decide_eq_true hc3
                    have hAa : A r_spec c₃ = true := by
                      have := heB ⟨r_spec, hr_spec_mem hc3⟩ ⟨c₃, hc3⟩
                      have hv : e_B ⟨r_spec, hr_spec_mem hc3⟩ = ⟨c₃, hc3⟩ := by
                        have h1 : (⟨r_spec, hr_spec_mem hc3⟩ : {r // r ∈ R_B}) = e_B.symm ⟨c₃, hc3⟩ :=
                          Subtype.ext (by dsimp only [r_spec]; rw [dif_pos hc3])
                        rw [h1, Equiv.apply_symm_apply]
                      exact this.trans (decide_eq_true hv)
                    rw [hva, hvb, hAa, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp [ha4, hb3, hfr_t]
                  · have hAf : A r_spec c_spec = false := by
                      have heq := heB ⟨r_spec, hr_spec_mem hc3⟩ ⟨c_spec, hc_spec_mem hr3⟩
                      have hv1 : e_B ⟨r_spec, hr_spec_mem hc3⟩ = ⟨c₃, hc3⟩ := by
                        have h1 : (⟨r_spec, hr_spec_mem hc3⟩ : {r // r ∈ R_B}) = e_B.symm ⟨c₃, hc3⟩ :=
                          Subtype.ext (by dsimp only [r_spec]; rw [dif_pos hc3])
                        rw [h1, Equiv.apply_symm_apply]
                      have hne : (⟨c₃, hc3⟩ : {c // c ∈ C_B}) ≠ ⟨c_spec, hc_spec_mem hr3⟩ :=
                        fun h => hc_spec_ne3 hr3 (congrArg Subtype.val h).symm
                      rw [hv1, decide_eq_false hne] at heq; exact heq
                    rw [hva, hvb, hAf, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                    rw [hsr_pos hc3, ha4, decide_eq_false (by omega)]
                  · have ha_specB : r_spec ∈ R_B := hr_spec_mem hc3
                    have hbB : φ_C_fn b ∈ C_B := hC_tail_B _ hmb
                    have hbc3 : φ_C_fn b ≠ c₃ := (Finset.mem_filter.mp hmb).2.1
                    have hAf : A r_spec (φ_C_fn b) = false := by
                      have heq := heB ⟨r_spec, ha_specB⟩ ⟨φ_C_fn b, hbB⟩
                      have hv1 : e_B ⟨r_spec, ha_specB⟩ = ⟨c₃, hc3⟩ := by
                        have h1 : (⟨r_spec, ha_specB⟩ : {r // r ∈ R_B}) = e_B.symm ⟨c₃, hc3⟩ :=
                          Subtype.ext (by dsimp only [r_spec]; rw [dif_pos hc3])
                        rw [h1, Equiv.apply_symm_apply]
                      have hne : (⟨c₃, hc3⟩ : {c // c ∈ C_B}) ≠ ⟨φ_C_fn b, hbB⟩ :=
                        fun h => hbc3 (congrArg Subtype.val h).symm
                      rw [hv1, decide_eq_false hne] at heq; exact heq
                    rw [hva, hAf, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                    rw [hsr_pos hc3, ha4, decide_eq_false (by omega)]
                · rcases hC_val b with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨hb3, hvb⟩ | ⟨hr3, hb4, hvb⟩ | ⟨hsc, hmb⟩
                  · omega
                  · omega
                  · omega
                  · have hAf : A (φ_R_fn a) c₃ = false := by
                      by_cases hc3 : c₃ ∈ C_B
                      · have haB : φ_R_fn a ∈ R_B := hR_tail_B _ hma
                        have hne : φ_R_fn a ≠ r_spec := (Finset.mem_filter.mp hma).2.2 hc3
                        have hsub : e_B ⟨φ_R_fn a, haB⟩ ≠ ⟨c₃, hc3⟩ := fun h => by
                          apply hne
                          have h1 := congrArg (fun x => (e_B.symm x).1) h
                          rw [Equiv.symm_apply_apply] at h1
                          dsimp only [r_spec]; rw [dif_pos hc3]; exact h1
                        have := heB ⟨φ_R_fn a, haB⟩ ⟨c₃, hc3⟩
                        rw [decide_eq_false hsub] at this; exact this
                      · by_contra ht
                        have haR : φ_R_fn a ∈ R_rest := (Finset.mem_filter.mp hma).1
                        have hc3C : c₃ ∈ C_rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0_c3.symm, hv1_c3.symm, hc2_c3.symm⟩
                        exact hc3 (Finset.mem_filter.mpr ⟨hc3C, φ_R_fn a, haR, Bool.eq_true_of_not_eq_false ht⟩)
                    have ha_ne4 : a.val ≠ 4 ∨ fr = false := by
                      by_cases hc3 : c₃ ∈ C_B
                      · left; rw [hsr_pos hc3] at hsr; omega
                      · right; dsimp only [fr]; exact decide_eq_false hc3
                    rw [hvb, hAf, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                    rcases ha_ne4 with ha4 | hfr_f
                    · simp [hb3, ha4]
                    · simp [hb3, hfr_f]
                  · have haB : φ_R_fn a ∈ R_B := hR_tail_B _ hma
                    have har3 : φ_R_fn a ≠ r₃ := (Finset.mem_filter.mp hma).2.1
                    have hAf : A (φ_R_fn a) c_spec = false := by
                      have heq := heB ⟨φ_R_fn a, haB⟩ ⟨c_spec, hc_spec_mem hr3⟩
                      have hv1 : e_B ⟨φ_R_fn a, haB⟩ ≠ ⟨c_spec, hc_spec_mem hr3⟩ := by
                        intro h
                        apply har3
                        have h2 : e_B ⟨φ_R_fn a, haB⟩ = e_B ⟨r₃, hr3⟩ := by
                          rw [h]; apply Subtype.ext; dsimp only [c_spec]; rw [dif_pos hr3]
                        exact congrArg Subtype.val (e_B.injective h2)
                      rw [decide_eq_false hv1] at heq; exact heq
                    rw [hvb, hAf, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                    rw [hsc_pos hr3, hb4, decide_eq_false (by omega)]
                  · obtain ⟨ha', heR⟩ := hφR_tail_eq hsr
                    obtain ⟨hb', heC⟩ := hφC_tail_eq hsc
                    have haB : φ_R_fn a ∈ R_B := hR_tail_B _ hma
                    have hbB : φ_C_fn b ∈ C_B := hC_tail_B _ hmb
                    have hA_eq := heB ⟨φ_R_fn a, haB⟩ ⟨φ_C_fn b, hbB⟩
                    have hsubR : (⟨φ_R_fn a, haB⟩ : {r // r ∈ R_B}) =
                        ⟨(finR ⟨a.val - sr, ha'⟩).1, hR_tail_B _ (finR ⟨a.val - sr, ha'⟩).2⟩ :=
                      Subtype.ext heR
                    have hsubC : (⟨φ_C_fn b, hbB⟩ : {c // c ∈ C_B}) =
                        ⟨(finC ⟨b.val - sc, hb'⟩).1, hC_tail_B _ (finC ⟨b.val - sc, hb'⟩).2⟩ :=
                      Subtype.ext heC
                    have he_match : (e_B ⟨(finR ⟨a.val - sr, ha'⟩).1, hR_tail_B _ (finR ⟨a.val - sr, ha'⟩).2⟩ =
                        ⟨(finC ⟨b.val - sc, hb'⟩).1, hC_tail_B _ (finC ⟨b.val - sc, hb'⟩).2⟩) ↔
                        a.val - sr = b.val - sc := by
                      have he_val : e_B ⟨(finR ⟨a.val - sr, ha'⟩).1, hR_tail_B _ (finR ⟨a.val - sr, ha'⟩).2⟩ =
                          ⟨(finC ⟨a.val - sr, ha'⟩).1, hC_tail_B _ (finC ⟨a.val - sr, ha'⟩).2⟩ :=
                        Subtype.ext rfl
                      rw [he_val]
                      constructor
                      · intro h
                        have hsub : finC ⟨a.val - sr, ha'⟩ = finC ⟨b.val - sc, hb'⟩ :=
                          Subtype.ext (congrArg (Subtype.val : {c // c ∈ C_B} → Fin m) h)
                        exact congrArg Fin.val (finC.injective hsub)
                      · intro h
                        apply Subtype.ext
                        have hf : (⟨a.val - sr, ha'⟩ : Fin R_tail.card) = ⟨b.val - sc, hb'⟩ := Fin.ext h
                        rw [hf]
                    rw [hA_eq, hsubR, hsubC, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                    apply Bool.eq_iff_iff.mpr
                    simp only [decide_eq_true_eq, hsr, hsc, true_and]
                    exact he_match
  refine ⟨fr, fc, hn_bound, hm_bound, heq_len, e, f, fun i j => ?_⟩
  have hi : φ_R_fn (e i) = i := Equiv.apply_symm_apply φ_R i
  have hj : φ_C_fn (f j) = j := Equiv.apply_symm_apply φ_C j
  calc A i j = A (φ_R_fn (e i)) (φ_C_fn (f j)) := by rw [hi, hj]
    _ = _ := h_main (e i) (f j)

end PEqualNP.Outside.L_meta_29724_classif
theorem PEqualNP.Outside.L_meta_29724 :
  ∀ n m : Nat, 3 ≤ n → 3 ≤ m →
    let good := fun A : Fin n → Fin m → Bool =>
      let lr := fun i k : Fin n => ∀ j, A i j = true → A k j = true
      let lc := fun j l : Fin m => ∀ i, A i j = true → A i l = true
      Function.Injective A ∧ Function.Injective (fun j i => A i j) ∧
      (∀ i, ∃ k, ¬ (lr i k ∨ lr k i)) ∧ (∀ j, ∃ l, ¬ (lc j l ∨ lc l j)) ∧
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents A C ∧
        C.size ≤ n+m-1 ∧ ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    let iso := fun (A B : Fin n → Fin m → Bool) =>
      ∃ (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)), ∀ i j, A i j = B (e i) (f j)
    let count := if min n m < 4 then 0 else if n = m then (if n = 4 then 1 else 2)
                 else if n+1 = m ∨ m+1 = n then 1 else 0
    ∃ family : Fin count → Fin n → Fin m → Bool,
      (∀ i, good (family i)) ∧ (∀ i j, iso (family i) (family j) → i = j) ∧
      (∀ A, good A → ∃ i, iso A (family i)) := by
  intro n m hn hm good iso count
  by_cases hmin : min n m < 4
  · have hc : count = 0 := if_pos hmin
    rw [hc]
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun A hg => ?_⟩
    obtain ⟨fr, fc, hn_b, hm_b, _⟩ := PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
    cases fr <;> cases fc <;> simp at hn_b hm_b <;> omega
  · by_cases heq_nm : n = m
    · by_cases hn4 : n = 4
      · have hc : count = 1 := by
          dsimp only [count]; rw [if_neg hmin, if_pos heq_nm, if_pos hn4]
        rw [hc]
        refine ⟨fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat n m false false,
          fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat_good n m false false (by simp; omega) (by simp; omega) (by simp; omega),
          fun i j _ => Subsingleton.elim i j, fun A hg => ?_⟩
        obtain ⟨fr, fc, hn_b, hm_b, heq_b, e, f, h_eq⟩ :=
          PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
        cases fr <;> cases fc
        · exact ⟨⟨0, by omega⟩, e, f, h_eq⟩
        · simp at hm_b; omega
        · simp at hn_b; omega
        · simp at hn_b; omega
      · have hc : count = 2 := by
          dsimp only [count]; rw [if_neg hmin, if_pos heq_nm, if_neg hn4]
        rw [hc]
        refine ⟨fun i => if i.val = 0 then PEqualNP.Outside.L_meta_29724_aux.tplMat n m false false
            else PEqualNP.Outside.L_meta_29724_aux.tplMat n m true true,
          fun i => ?_, fun i j hij => ?_, fun A hg => ?_⟩
        · dsimp only
          by_cases hi : i.val = 0
          · rw [if_pos hi]
            exact PEqualNP.Outside.L_meta_29724_aux.tplMat_good n m false false (by simp; omega) (by simp; omega) (by simp; omega)
          · rw [if_neg hi]
            exact PEqualNP.Outside.L_meta_29724_aux.tplMat_good n m true true (by simp; omega) (by simp; omega) (by simp; omega)
        · subst heq_nm
          rcases hij with ⟨e, f, h⟩
          dsimp only at h
          by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
          · exact Fin.ext (by omega)
          · exfalso
            simp only [hi, hj, ↓reduceIte] at h
            exact PEqualNP.Outside.L_meta_29724_aux.tplMat_distinct n (by omega) ⟨e, f, h⟩
          · exfalso
            simp only [hi, hj, ↓reduceIte] at h
            exact PEqualNP.Outside.L_meta_29724_aux.tplMat_distinct n (by omega)
              ⟨e.symm, f.symm, fun a b => by have := (h (e.symm a) (f.symm b)).symm; simp only [Equiv.apply_symm_apply] at this; exact this⟩
          · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
        · obtain ⟨fr, fc, hn_b, hm_b, heq_b, e, f, h_eq⟩ :=
            PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
          cases fr <;> cases fc
          · refine ⟨⟨0, by omega⟩, e, f, fun i j => ?_⟩
            dsimp only; exact h_eq i j
          · simp at hn_b hm_b heq_b; omega
          · simp at hn_b hm_b heq_b; omega
          · refine ⟨⟨1, by omega⟩, e, f, fun i j => ?_⟩
            dsimp only; exact h_eq i j
    · by_cases hadj : n + 1 = m ∨ m + 1 = n
      · have hc : count = 1 := by
          dsimp only [count]; rw [if_neg hmin, if_neg heq_nm, if_pos hadj]
        rw [hc]
        rcases hadj with hnm | hmn
        · refine ⟨fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat n m false true,
            fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat_good n m false true (by simp; omega) (by simp; omega) (by simp; omega),
            fun i j _ => Subsingleton.elim i j, fun A hg => ?_⟩
          obtain ⟨fr, fc, hn_b, hm_b, heq_b, e, f, h_eq⟩ :=
            PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
          cases fr <;> cases fc
          · simp at heq_b; omega
          · exact ⟨⟨0, by omega⟩, e, f, h_eq⟩
          · simp at hn_b heq_b; omega
          · simp at hn_b hm_b heq_b; omega
        · refine ⟨fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat n m true false,
            fun _ => PEqualNP.Outside.L_meta_29724_aux.tplMat_good n m true false (by simp; omega) (by simp; omega) (by simp; omega),
            fun i j _ => Subsingleton.elim i j, fun A hg => ?_⟩
          obtain ⟨fr, fc, hn_b, hm_b, heq_b, e, f, h_eq⟩ :=
            PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
          cases fr <;> cases fc
          · simp at heq_b; omega
          · simp at hm_b heq_b; omega
          · exact ⟨⟨0, by omega⟩, e, f, h_eq⟩
          · simp at hn_b hm_b heq_b; omega
      · have hc : count = 0 := by
          dsimp only [count]; rw [if_neg hmin, if_neg heq_nm, if_neg hadj]
        rw [hc]
        refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun A hg => ?_⟩
        obtain ⟨fr, fc, hn_b, hm_b, heq_b, _⟩ :=
          PEqualNP.Outside.L_meta_29724_classif.classification_of_good hn hm hg
        cases fr <;> cases fc <;> simp at hn_b hm_b heq_b <;> omega
