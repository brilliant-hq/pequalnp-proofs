import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25540_aux

open PEqualNP.CircuitLowerBounds


def stepFn (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (gs.foldl stepFn x).getD w false

theorem eval_eq (C : Circuit) (x : List Bool) : C.eval x = V C.gates x C.output := rfl

theorem wires_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stepFn x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [stepFn, List.length_append, List.length_cons, List.length_nil]
    omega

theorem V_prefix (gs₁ gs₂ : List Gate) (x : List Bool) {w : ℕ}
    (hw : w < x.length + gs₁.length) : V (gs₁ ++ gs₂) x w = V gs₁ x w := by
  unfold V
  rw [List.foldl_append]
  have hlen : (gs₁.foldl stepFn x).length = x.length + gs₁.length := wires_len gs₁ x
  have hws : w < (gs₁.foldl stepFn x).length := by omega
  generalize gs₁.foldl stepFn x = s at hws ⊢
  induction gs₂ generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    rw [ih (stepFn s g) (by simp [stepFn]; omega)]
    exact List.getD_append _ _ _ _ hws

theorem V_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    V (gs ++ [g]) x (x.length + gs.length) = g.op.eval (g.inputs.map (V gs x)) := by
  unfold V
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen := wires_len gs x
  change ((gs.foldl stepFn x) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepFn x).getD i false)]).getD
    (x.length + gs.length) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [hlen, Nat.sub_self, List.getD_cons_zero]

theorem V_raw (gs : List Gate) (x : List Bool) {w : ℕ} (hw : w < x.length) :
    V gs x w = x.getD w false := by
  have := V_prefix [] gs x (w := w) (by simpa using hw)
  simpa [V] using this

def gateOk (N j : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
    g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < N + j

def Ok (N : ℕ) (gs : List Gate) : Prop := ∀ j (h : j < gs.length), gateOk N j (gs[j]'h)

theorem ok_nil (N : ℕ) : Ok N [] := fun j h => absurd h (by simp)

theorem ok_snoc {N : ℕ} {gs : List Gate} {g : Gate} (h : Ok N gs) (hg : gateOk N gs.length g) :
    Ok N (gs ++ [g]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · rw [List.getElem_append_left hj]; exact h j hj
  · subst hj; rw [List.getElem_append_right (le_refl _)]; simpa using hg

def notCnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => @decide (g.op = GateOp.not)
    (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op GateOp.not)).length

theorem notCnt_snoc (gs : List Gate) (g : Gate) :
    notCnt (gs ++ [g]) = notCnt gs + notCnt [g] := by
  unfold notCnt; rw [List.filter_append, List.length_append]

theorem notCnt_one_not (g : Gate) (h : g.op = GateOp.not) : notCnt [g] = 1 := by
  unfold notCnt; simp [h]

theorem notCnt_one_ne (g : Gate) (h : g.op ≠ GateOp.not) : notCnt [g] = 0 := by
  unfold notCnt; simp [h]

def cntW (gs : List Gate) (w : ℕ) : ℕ := (gs.map fun g => g.inputs.count w).sum

theorem cntW_snoc (gs : List Gate) (g : Gate) (w : ℕ) :
    cntW (gs ++ [g]) w = cntW gs w + g.inputs.count w := by
  simp [cntW, List.map_append, List.sum_append]

structure BodyExt (N : ℕ) (gs gs' : List Gate) : Prop where
  pre : ∃ more, gs' = gs ++ more
  len : gs.length ≤ gs'.length
  ok : Ok N gs → Ok N gs'
  nots : notCnt gs' = notCnt gs
  raw : ∀ w < N, cntW gs' w = cntW gs w

theorem BodyExt.refl (N : ℕ) (gs : List Gate) : BodyExt N gs gs :=
  ⟨⟨[], by simp⟩, le_refl _, id, rfl, fun _ _ => rfl⟩

theorem BodyExt.trans {N : ℕ} {a b c : List Gate} (h1 : BodyExt N a b) (h2 : BodyExt N b c) :
    BodyExt N a c := by
  obtain ⟨⟨m1, e1⟩, l1, o1, n1, r1⟩ := h1
  obtain ⟨⟨m2, e2⟩, l2, o2, n2, r2⟩ := h2
  exact ⟨⟨m1 ++ m2, by rw [e2, e1, List.append_assoc]⟩, le_trans l1 l2, o2 ∘ o1, n2.trans n1,
    fun w hw => (r2 w hw).trans (r1 w hw)⟩

theorem BodyExt.snoc {N : ℕ} {gs : List Gate} (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, N ≤ i ∧ i < N + gs.length) : BodyExt N gs (gs ++ [g]) := by
  refine ⟨⟨[g], rfl⟩, by simp, fun h => ok_snoc h ⟨Or.imp_right Or.inl hop, hl,
    fun i hi => (hin i hi).2⟩, ?_, ?_⟩
  · rw [notCnt_snoc, notCnt_one_ne g (by rcases hop with h | h <;> rw [h] <;> exact fun e => by cases e)]
    rfl
  · intro w hw; rw [cntW_snoc]
    have : g.inputs.count w = 0 := List.count_eq_zero.mpr fun hm => by
      have := (hin w hm).1; omega
    omega

theorem BodyExt.V_eq {N : ℕ} {gs gs' : List Gate} (h : BodyExt N gs gs') (x : List Bool)
    {w : ℕ} (hw : w < x.length + gs.length) : V gs' x w = V gs x w := by
  obtain ⟨more, e⟩ := h.pre; rw [e]; exact V_prefix _ _ _ hw

def orAux (N : ℕ) : List Gate → ℕ → List (ℕ × ℕ × ℕ) → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, (a, b, c) :: L =>
      orAux N (gs ++ [⟨GateOp.and, [a, b]⟩] ++ [⟨GateOp.and, [N + gs.length, c]⟩] ++
        [⟨GateOp.or, [acc, N + gs.length + 1]⟩]) (N + gs.length + 2) L

def orTerms (N : ℕ) (gs : List Gate) (L : List (ℕ × ℕ × ℕ)) : List Gate × ℕ :=
  orAux N (gs ++ [⟨GateOp.or, []⟩]) (N + gs.length) L

def TermsIn (N B : ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ t ∈ L, (N ≤ t.1 ∧ t.1 < B) ∧ (N ≤ t.2.1 ∧ t.2.1 < B) ∧ (N ≤ t.2.2 ∧ t.2.2 < B)

theorem orAux_spec (N : ℕ) (x : List Bool) (hx : x.length = N) (B : ℕ) (L : List (ℕ × ℕ × ℕ))
    (hL : TermsIn N B L) :
    ∀ gs acc, B ≤ N + gs.length → N ≤ acc → acc < N + gs.length →
      BodyExt N gs (orAux N gs acc L).1 ∧
      (orAux N gs acc L).1.length = gs.length + 3 * L.length ∧
      N ≤ (orAux N gs acc L).2 ∧ (orAux N gs acc L).2 < N + (orAux N gs acc L).1.length ∧
      (V (orAux N gs acc L).1 x (orAux N gs acc L).2 = true ↔
        (V gs x acc = true ∨ ∃ t ∈ L, V gs x t.1 = true ∧ V gs x t.2.1 = true ∧
          V gs x t.2.2 = true)) := by
  induction L with
  | nil => intro gs acc _ h1 h2; exact ⟨BodyExt.refl _ _, by simp [orAux], h1, h2, by simp [orAux]⟩
  | cons t L ih =>
    obtain ⟨a, b, c⟩ := t
    intro gs acc hB h1 h2
    have ht := hL (a, b, c) (List.mem_cons_self ..)
    have hL' : TermsIn N B L := fun t ht' => hL t (List.mem_cons_of_mem _ ht')
    simp only at ht
    set g1 : Gate := ⟨GateOp.and, [a, b]⟩
    set g2 : Gate := ⟨GateOp.and, [N + gs.length, c]⟩
    set g3 : Gate := ⟨GateOp.or, [acc, N + gs.length + 1]⟩
    have e1 : BodyExt N gs (gs ++ [g1]) :=
      BodyExt.snoc g1 (Or.inl rfl) (by simp [g1]) (by
        intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega)
    have e2 : BodyExt N (gs ++ [g1]) (gs ++ [g1] ++ [g2]) :=
      BodyExt.snoc g2 (Or.inl rfl) (by simp [g2]) (by
        intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    have e3 : BodyExt N (gs ++ [g1] ++ [g2]) (gs ++ [g1] ++ [g2] ++ [g3]) :=
      BodyExt.snoc g3 (Or.inr rfl) (by simp [g3]) (by
        intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    have e123 := (e1.trans e2).trans e3
    have hlen3 : (gs ++ [g1] ++ [g2] ++ [g3]).length = gs.length + 3 := by simp
    obtain ⟨r1, r2, r3, r4, r5⟩ := ih hL' (gs ++ [g1] ++ [g2] ++ [g3]) (N + gs.length + 2)
      (by omega) (by omega) (by omega)
    have hunf : orAux N gs acc ((a, b, c) :: L) =
        orAux N (gs ++ [g1] ++ [g2] ++ [g3]) (N + gs.length + 2) L := rfl
    rw [hunf]
    refine ⟨e123.trans r1, by rw [r2, hlen3]; simp; ring, r3, r4, ?_⟩
    rw [r5]

    have v1 : V (gs ++ [g1]) x (N + gs.length) = (V gs x a && V gs x b) := by
      rw [← hx, V_snoc]; simp [g1, GateOp.eval]
    have v2 : V (gs ++ [g1] ++ [g2]) x (N + gs.length + 1) =
        (V gs x a && V gs x b && V gs x c) := by
      have := V_snoc (gs ++ [g1]) g2 x
      have hl : x.length + (gs ++ [g1]).length = N + gs.length + 1 := by simp [hx]; omega
      rw [hl] at this
      rw [this]; simp only [g2, GateOp.eval, List.map_cons, List.map_nil]
      rw [v1, V_prefix gs [g1] x (w := c) (by omega)]
      simp [Bool.and_assoc]
    have v3 : V (gs ++ [g1] ++ [g2] ++ [g3]) x (N + gs.length + 2) =
        (V gs x acc || (V gs x a && V gs x b && V gs x c)) := by
      have := V_snoc (gs ++ [g1] ++ [g2]) g3 x
      have hl : x.length + (gs ++ [g1] ++ [g2]).length = N + gs.length + 2 := by simp [hx]; omega
      rw [hl] at this
      rw [this]; simp only [g3, GateOp.eval, List.map_cons, List.map_nil]
      rw [v2, e1.trans e2 |>.V_eq x (by omega)]
      simp
    have vs : ∀ w < B, V (gs ++ [g1] ++ [g2] ++ [g3]) x w = V gs x w :=
      fun w hw => e123.V_eq x (by omega)
    rw [v3]
    simp only [List.mem_cons, exists_eq_or_imp, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro (h | h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩)
      · obtain ⟨t, htL, h⟩ := h
        have := hL' t htL
        rw [vs _ this.1.2, vs _ this.2.1.2, vs _ this.2.2.2] at h
        exact Or.inr (Or.inr ⟨t, htL, h⟩)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
      · obtain ⟨t, htL, h⟩ := h
        have := hL' t htL
        refine Or.inr ⟨t, htL, ?_⟩
        rw [vs _ this.1.2, vs _ this.2.1.2, vs _ this.2.2.2]; exact h

theorem orTerms_spec (N : ℕ) (x : List Bool) (hx : x.length = N) (B : ℕ)
    (L : List (ℕ × ℕ × ℕ)) (hL : TermsIn N B L) (gs : List Gate) (hB : B ≤ N + gs.length) :
      BodyExt N gs (orTerms N gs L).1 ∧
      (orTerms N gs L).1.length = gs.length + 3 * L.length + 1 ∧
      N ≤ (orTerms N gs L).2 ∧ (orTerms N gs L).2 < N + (orTerms N gs L).1.length ∧
      (V (orTerms N gs L).1 x (orTerms N gs L).2 = true ↔
        ∃ t ∈ L, V gs x t.1 = true ∧ V gs x t.2.1 = true ∧ V gs x t.2.2 = true) := by
  have e0 : BodyExt N gs (gs ++ [⟨GateOp.or, []⟩]) :=
    BodyExt.snoc _ (Or.inr rfl) (by simp) (by simp)
  obtain ⟨r1, r2, r3, r4, r5⟩ := orAux_spec N x hx B L hL (gs ++ [⟨GateOp.or, []⟩])
    (N + gs.length) (by simp; omega) (by omega) (by simp)
  unfold orTerms
  refine ⟨e0.trans r1, by rw [r2]; simp; ring, r3, r4, ?_⟩
  rw [r5]
  have v0 : V (gs ++ [⟨GateOp.or, []⟩]) x (N + gs.length) = false := by
    rw [← hx, V_snoc]; simp [GateOp.eval]
  rw [v0]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨t, htL, h⟩
    have := hL t htL
    rw [e0.V_eq x (by omega), e0.V_eq x (by omega), e0.V_eq x (by omega)] at h
    exact ⟨t, htL, h⟩
  · rintro ⟨t, htL, h⟩
    have := hL t htL
    refine ⟨t, htL, ?_⟩
    rw [e0.V_eq x (by omega), e0.V_eq x (by omega), e0.V_eq x (by omega)]; exact h

theorem bdec {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  simp [h]

def pwW (n k : ℕ) : ℕ := if k = 0 then 5 * n else 5 * n + 3 * k
def twW (n k : ℕ) : ℕ := if k = 0 then 5 * n else 5 * n + 3 * k - 1
def xW (n k : ℕ) : ℕ := 5 * n + 1 + 3 * k
def swW (n s : ℕ) : ℕ := if n ≤ s then 5 * n else 8 * n + 1 + (n - 1 - s)

def scanP (n : ℕ) (q : ℕ → ℕ) (base : List Gate) : ℕ → List Gate
  | 0 => base
  | k + 1 => scanP n q base k ++ [⟨GateOp.and, [pwW n k, q k]⟩] ++
      [⟨GateOp.or, [twW n k, xW n k]⟩] ++ [⟨GateOp.or, [pwW n k, q k]⟩]

def scanS (n : ℕ) (q : ℕ → ℕ) (base : List Gate) : ℕ → List Gate
  | 0 => base
  | t + 1 => scanS n q base t ++ [⟨GateOp.or, [swW n (n - t), q (n - 1 - t)]⟩]

theorem snoc_val (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : x.length + gs.length = w) :
    V (gs ++ [g]) x w = g.op.eval (g.inputs.map (V gs x)) := by
  subst hw; exact V_snoc gs g x

theorem scanP_spec (n : ℕ) (q : ℕ → ℕ) (base : List Gate) (x : List Bool) (hx : x.length = n + n)
    (hb : base.length = 3 * n + 1) (a b : ℕ) (hF : V base x (5 * n) = false)
    (hq : ∀ k < n, n + n ≤ q k ∧ q k < 5 * n ∧ V base x (q k) = decide (k = a ∨ k = b)) :
    ∀ k ≤ n, BodyExt (n + n) base (scanP n q base k) ∧
      (scanP n q base k).length = 3 * n + 1 + 3 * k ∧
      ∀ k' ≤ k, V (scanP n q base k) x (pwW n k') = decide (a < k' ∨ b < k') ∧
        V (scanP n q base k) x (twW n k') = decide (a ≠ b ∧ a < k' ∧ b < k') := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨BodyExt.refl _ _, by simp [scanP, hb], ?_⟩
    intro k' hk'
    have : k' = 0 := by omega
    subst this
    simp only [pwW, twW, if_true, scanP, hF]
    constructor <;> symm <;> simp
  | succ k ih =>
    intro hk
    obtain ⟨e, hl, hv⟩ := ih (by omega)
    obtain ⟨hq1, hq2, hq3⟩ := hq k (by omega)
    set gs := scanP n q base k
    have hpw : pwW n k < 5 * n + 1 + 3 * k ∧ n + n ≤ pwW n k := by
      unfold pwW; split_ifs <;> omega
    have htw : twW n k < 5 * n + 1 + 3 * k ∧ n + n ≤ twW n k := by
      unfold twW; split_ifs <;> omega
    set g1 : Gate := ⟨GateOp.and, [pwW n k, q k]⟩
    set g2 : Gate := ⟨GateOp.or, [twW n k, xW n k]⟩
    set g3 : Gate := ⟨GateOp.or, [pwW n k, q k]⟩
    have e1 : BodyExt (n + n) gs (gs ++ [g1]) :=
      BodyExt.snoc g1 (Or.inl rfl) (by simp [g1]) (by
        intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega)
    have e2 : BodyExt (n + n) (gs ++ [g1]) (gs ++ [g1] ++ [g2]) :=
      BodyExt.snoc g2 (Or.inr rfl) (by simp [g2]) (by
        intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> simp [xW] <;> omega)
    have e3 : BodyExt (n + n) (gs ++ [g1] ++ [g2]) (gs ++ [g1] ++ [g2] ++ [g3]) :=
      BodyExt.snoc g3 (Or.inr rfl) (by simp [g3]) (by
        intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    have hunf : scanP n q base (k + 1) = gs ++ [g1] ++ [g2] ++ [g3] := rfl
    rw [hunf]
    refine ⟨e.trans ((e1.trans e2).trans e3), by simp [hl]; ring, ?_⟩
    have vq : V gs x (q k) = decide (k = a ∨ k = b) := by
      rw [e.V_eq x (by omega)]; exact hq3
    have vp := (hv k (le_refl _)).1
    have vt := (hv k (le_refl _)).2
    have v1 : V (gs ++ [g1]) x (xW n k) = decide ((a < k ∨ b < k) ∧ (k = a ∨ k = b)) := by
      rw [snoc_val gs g1 x _ (by rw [hx, hl]; simp [xW]; ring)]
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, vp, vq]
      simp
    have v2 : V (gs ++ [g1] ++ [g2]) x (twW n (k + 1)) =
        decide (a ≠ b ∧ a < k + 1 ∧ b < k + 1) := by
      rw [snoc_val (gs ++ [g1]) g2 x _ (by rw [hx]; simp [hl, twW]; omega)]
      simp only [g2, GateOp.eval, List.map_cons, List.map_nil, v1]
      rw [e1.V_eq x (by omega), vt]
      rw [Bool.eq_iff_iff]; simp; omega
    have v3 : V (gs ++ [g1] ++ [g2] ++ [g3]) x (pwW n (k + 1)) = decide (a < k + 1 ∨ b < k + 1) := by
      rw [snoc_val (gs ++ [g1] ++ [g2]) g3 x _ (by rw [hx]; simp [hl, pwW]; omega)]
      simp only [g3, GateOp.eval, List.map_cons, List.map_nil]
      rw [(e1.trans e2).V_eq x (w := pwW n k) (by omega), (e1.trans e2).V_eq x (w := q k) (by omega), vp, vq]
      rw [Bool.eq_iff_iff]; simp; omega
    intro k' hk'
    rcases Nat.of_le_succ hk' with hk' | rfl
    · have hvk := hv k' (by omega)
      have hpw' : pwW n k' < 5 * n + 1 + 3 * k := by unfold pwW; split_ifs <;> omega
      have htw' : twW n k' < 5 * n + 1 + 3 * k := by unfold twW; split_ifs <;> omega
      rw [((e1.trans e2).trans e3).V_eq x (by omega), ((e1.trans e2).trans e3).V_eq x (by omega)]
      exact hvk
    · refine ⟨v3, ?_⟩
      rw [e3.V_eq x (w := twW n (k + 1)) (by rw [hx]; simp [hl, twW]; omega)]; exact v2

theorem scanS_spec (n : ℕ) (q : ℕ → ℕ) (base : List Gate) (x : List Bool) (hx : x.length = n + n)
    (hb : base.length = 6 * n + 1) (a b : ℕ) (ha : a < n) (hb' : b < n)
    (hF : V base x (5 * n) = false)
    (hq : ∀ k < n, n + n ≤ q k ∧ q k < 5 * n ∧ V base x (q k) = decide (k = a ∨ k = b)) :
    ∀ t ≤ n, BodyExt (n + n) base (scanS n q base t) ∧
      (scanS n q base t).length = 6 * n + 1 + t ∧
      ∀ s, n - t ≤ s → V (scanS n q base t) x (swW n s) = decide (s ≤ a ∨ s ≤ b) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨BodyExt.refl _ _, by simp [scanS, hb], ?_⟩
    intro s hs
    simp only [swW, show n ≤ s by omega, if_true, scanS, hF]
    rw [Bool.eq_iff_iff]; simp; omega
  | succ t ih =>
    intro ht
    obtain ⟨e, hl, hv⟩ := ih (by omega)
    obtain ⟨hq1, hq2, hq3⟩ := hq (n - 1 - t) (by omega)
    set gs := scanS n q base t
    have hsw : swW n (n - t) < 8 * n + 1 + t ∧ n + n ≤ swW n (n - t) := by
      unfold swW; split_ifs <;> omega
    set g : Gate := ⟨GateOp.or, [swW n (n - t), q (n - 1 - t)]⟩
    have e1 : BodyExt (n + n) gs (gs ++ [g]) :=
      BodyExt.snoc g (Or.inr rfl) (by simp [g]) (by
        intro i hi; simp [g] at hi; rcases hi with rfl | rfl <;> omega)
    have hunf : scanS n q base (t + 1) = gs ++ [g] := rfl
    rw [hunf]
    refine ⟨e.trans e1, by simp [hl]; ring, ?_⟩
    intro s hs
    by_cases hst : n - t ≤ s
    · have : swW n s < 8 * n + 1 + t := by unfold swW; split_ifs <;> omega
      rw [e1.V_eq x (by omega)]; exact hv s hst
    · have hs' : s = n - 1 - t := by omega
      subst hs'
      rw [snoc_val gs g x _ (by rw [hx, hl]; simp [swW]; split_ifs <;> omega)]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil]
      rw [hv _ (le_refl _), e.V_eq x (by omega), hq3]
      rw [Bool.eq_iff_iff]; simp; omega

theorem V_rawgate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hraw : ∀ i ∈ (gs[j]).inputs, i < x.length) :
    V gs x (x.length + j) = (gs[j]).op.eval ((gs[j]).inputs.map fun i => x.getD i false) := by
  have e := List.take_succ_eq_append_getElem hj
  generalize gs[j] = g at hraw e ⊢
  have h1 := V_prefix (gs.take (j + 1)) (gs.drop (j + 1)) x (w := x.length + j)
    (by rw [List.length_take]; omega)
  rw [List.take_append_drop] at h1
  rw [h1, e]
  have hl : (gs.take j).length = j := by rw [List.length_take]; omega
  have h2 := V_snoc (gs.take j) g x
  rw [hl] at h2
  rw [h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact V_raw _ x (hraw i hi)

theorem V_oob (gs : List Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V; rw [List.getD_eq_default _ _ (by rw [wires_len]; exact hw)]

theorem oe_len {n : ℕ} (u v : Fin n) : (Represents.oneEach u v).length = n + n := by
  simp [Represents.oneEach]

theorem oe_left {n : ℕ} (u v : Fin n) (i : Fin n) :
    (Represents.oneEach u v).getD i.val false = decide (i = u) := by
  unfold Represents.oneEach
  rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem oe_right {n : ℕ} (u v : Fin n) (j : Fin n) :
    (Represents.oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold Represents.oneEach
  rw [List.getD_append_right _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

def pGate (n : ℕ) (mate : Equiv.Perm (Fin n)) (i : Fin n) : Gate :=
  ⟨GateOp.or, [i.val, n + (mate i).val]⟩
def rGate (n : ℕ) (rows : Finset (Fin n)) (i : Fin n) : Gate :=
  ⟨GateOp.or, if i ∈ rows then [i.val] else []⟩
def cGate (n : ℕ) (mate : Equiv.Perm (Fin n)) (cols : Finset (Fin n)) (i : Fin n) : Gate :=
  ⟨GateOp.or, if i ∈ cols then [n + (mate i).val] else []⟩

def pre (n : ℕ) (mate : Equiv.Perm (Fin n)) (rows cols : Finset (Fin n)) : List Gate :=
  List.ofFn (pGate n mate) ++ List.ofFn (rGate n rows) ++ List.ofFn (cGate n mate cols) ++
    [⟨GateOp.or, []⟩]

section pre
variable (n : ℕ) (mate : Equiv.Perm (Fin n)) (rows cols : Finset (Fin n))

theorem pre_len : (pre n mate rows cols).length = 3 * n + 1 := by simp [pre]; ring

theorem pre_getP (i : Fin n) (h : i.val < (pre n mate rows cols).length) :
    (pre n mate rows cols)[i.val]'h = pGate n mate i := by
  simp only [pre]
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega), List.getElem_append_left (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
    List.getElem_append_left (by simp)]
  simp

theorem pre_getR (i : Fin n) (h : n + i.val < (pre n mate rows cols).length) :
    (pre n mate rows cols)[n + i.val]'h = rGate n rows i := by
  simp only [pre]
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega), List.getElem_append_left (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega),
    List.getElem_append_right (by simp)]
  all_goals simp

theorem pre_getC (i : Fin n) (h : n + n + i.val < (pre n mate rows cols).length) :
    (pre n mate rows cols)[n + n + i.val]'h = cGate n mate cols i := by
  simp only [pre]
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega), List.getElem_append_right (by simp)]
  simp

theorem pre_getF (h : 3 * n < (pre n mate rows cols).length) :
    (pre n mate rows cols)[3 * n]'h = ⟨GateOp.or, []⟩ := by
  simp only [pre]
  rw [List.getElem_append_right (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)]
  simp

theorem pre_mem (g : Gate) (hg : g ∈ pre n mate rows cols) :
    g.op = GateOp.or ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < n + n := by
  simp only [pre, List.mem_append, List.mem_ofFn, List.mem_singleton] at hg
  rcases hg with ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl
  · refine ⟨rfl, by simp [pGate], ?_⟩
    intro r hr; simp [pGate] at hr; rcases hr with rfl | rfl <;> omega
  · refine ⟨rfl, by simp [rGate]; split_ifs <;> simp, ?_⟩
    intro r hr; simp [rGate] at hr; obtain ⟨-, rfl⟩ := hr; omega
  · refine ⟨rfl, by simp [cGate]; split_ifs <;> simp, ?_⟩
    intro r hr; simp [cGate] at hr; obtain ⟨-, rfl⟩ := hr; omega
  · exact ⟨rfl, by simp, by simp⟩

theorem pre_ok : Ok (n + n) (pre n mate rows cols) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := pre_mem n mate rows cols _ (List.getElem_mem hj)
  exact ⟨Or.inr (Or.inl h1), h2, fun i hi => by have := h3 i hi; omega⟩

theorem pre_nots : notCnt (pre n mate rows cols) = 0 := by
  unfold notCnt
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp [(pre_mem n mate rows cols g hg).1]

variable (u v : Fin n)

theorem pre_valP (i : Fin n) :
    V (pre n mate rows cols) (Represents.oneEach u v) (n + n + i.val) =
      decide (i = u ∨ mate i = v) := by
  have h := V_rawgate (pre n mate rows cols) (Represents.oneEach u v) i.val
    (by rw [pre_len]; omega) (fun r hr => by
      have := (pre_mem n mate rows cols _ (List.getElem_mem _)).2.2 r hr
      rw [oe_len]; exact this)
  rw [oe_len] at h; rw [h]
  simp only [pre_getP, pGate, GateOp.eval, List.map_cons, List.map_nil]
  rw [oe_left, oe_right]; simp

theorem pre_valR (i : Fin n) :
    V (pre n mate rows cols) (Represents.oneEach u v) (n + n + n + i.val) =
      decide (i = u ∧ i ∈ rows) := by
  have h := V_rawgate (pre n mate rows cols) (Represents.oneEach u v) (n + i.val)
    (by rw [pre_len]; omega) (fun r hr => by
      have := (pre_mem n mate rows cols _ (List.getElem_mem _)).2.2 r hr
      rw [oe_len]; exact this)
  rw [oe_len, ← add_assoc] at h; rw [h]
  simp only [pre_getR, rGate, GateOp.eval]
  split_ifs with hr
  · simp only [List.map_cons, List.map_nil]; rw [oe_left]; simp [hr]
  · simp [hr]

theorem pre_valC (i : Fin n) :
    V (pre n mate rows cols) (Represents.oneEach u v) (n + n + n + n + i.val) =
      decide (mate i = v ∧ i ∈ cols) := by
  have h := V_rawgate (pre n mate rows cols) (Represents.oneEach u v) (n + n + i.val)
    (by rw [pre_len]; omega) (fun r hr => by
      have := (pre_mem n mate rows cols _ (List.getElem_mem _)).2.2 r hr
      rw [oe_len]; exact this)
  rw [oe_len, ← add_assoc, ← add_assoc] at h; rw [h]
  simp only [pre_getC, cGate, GateOp.eval]
  split_ifs with hr
  · simp only [List.map_cons, List.map_nil]; rw [oe_right]; simp [hr]
  · simp [hr]

theorem pre_valF : V (pre n mate rows cols) (Represents.oneEach u v) (5 * n) = false := by
  have h := V_rawgate (pre n mate rows cols) (Represents.oneEach u v) (3 * n)
    (by rw [pre_len]; omega) (fun r hr => by
      have := (pre_mem n mate rows cols _ (List.getElem_mem _)).2.2 r hr
      rw [oe_len]; exact this)
  rw [oe_len, show n + n + 3 * n = 5 * n by ring] at h; rw [h]
  simp [pre_getF, GateOp.eval]

theorem cntW_append (a b : List Gate) (w : ℕ) : cntW (a ++ b) w = cntW a w + cntW b w := by
  simp [cntW, List.map_append, List.sum_append]

theorem cntW_ofFn {m : ℕ} (f : Fin m → Gate) (w : ℕ) :
    cntW (List.ofFn f) w = ∑ k, (f k).inputs.count w := by
  simp [cntW, List.map_ofFn, List.sum_ofFn]

theorem pre_cntL (i : Fin n) :
    cntW (pre n mate rows cols) i.val = 1 + (if i ∈ rows then 1 else 0) := by
  simp only [pre, cntW_append, cntW_ofFn]
  have h1 : ∀ k : Fin n, (pGate n mate k).inputs.count i.val = if k = i then 1 else 0 := by
    intro k; simp only [pGate, List.count_cons, List.count_nil]
    by_cases hk : k = i
    · subst hk; simp <;> omega
    · have : k.val ≠ i.val := fun h => hk (Fin.ext h)
      simp [hk, this]; omega
  have h2 : ∀ k : Fin n, (rGate n rows k).inputs.count i.val =
      if k = i then (if i ∈ rows then 1 else 0) else 0 := by
    intro k; simp only [rGate]
    by_cases hk : k = i
    · subst hk; split_ifs <;> simp_all
    · have : k.val ≠ i.val := fun h => hk (Fin.ext h)
      split_ifs <;> simp [this]
  have h3 : ∀ k : Fin n, (cGate n mate cols k).inputs.count i.val = 0 := by
    intro k; by_cases hc : k ∈ cols <;> simp [cGate, hc, List.count_cons] <;> omega
  simp only [h1, h2, h3, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  simp [cntW]

theorem pre_cntR (i : Fin n) :
    cntW (pre n mate rows cols) (n + (mate i).val) = 1 + (if i ∈ cols then 1 else 0) := by
  simp only [pre, cntW_append, cntW_ofFn]
  have h1 : ∀ k : Fin n, (pGate n mate k).inputs.count (n + (mate i).val) =
      if k = i then 1 else 0 := by
    intro k; simp only [pGate, List.count_cons, List.count_nil]
    by_cases hk : k = i
    · subst hk; simp <;> omega
    · have : (mate k).val ≠ (mate i).val := fun h => hk (mate.injective (Fin.ext h))
      simp [hk, this]; omega
  have h2 : ∀ k : Fin n, (rGate n rows k).inputs.count (n + (mate i).val) = 0 := by
    intro k; by_cases hc : k ∈ rows <;> simp [rGate, hc, List.count_cons] <;> omega
  have h3 : ∀ k : Fin n, (cGate n mate cols k).inputs.count (n + (mate i).val) =
      if k = i then (if i ∈ cols then 1 else 0) else 0 := by
    intro k; simp only [cGate]
    by_cases hk : k = i
    · subst hk; split_ifs <;> simp_all
    · have : (mate k).val ≠ (mate i).val := fun h => hk (mate.injective (Fin.ext h))
      split_ifs <;> simp [this]
  simp only [h1, h2, h3, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  simp [cntW]

end pre

noncomputable section build
variable (n : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
  (rows cols : Finset (Fin n))

def qW (k : ℕ) : ℕ := if h : k < n then n + n + (rank.symm ⟨k, h⟩).val else 5 * n

def gs0 : List Gate :=
  scanS n (qW n rank) (scanP n (qW n rank) (pre n mate rows cols) n) n

def pW (i : Fin n) : ℕ := n + n + i.val
def rW (i : Fin n) : ℕ := n + n + n + i.val
def cW (i : Fin n) : ℕ := n + n + n + n + i.val

def Eord : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ (G p.1 (mate p.2) = true ∨ G p.2 (mate p.1) = true))

def posT (p : Fin n × Fin n) : ℕ × ℕ × ℕ :=
  if G p.1 (mate p.2) = true ∧ G p.2 (mate p.1) = true then (pW n p.1, pW n p.2, pW n p.2)
  else if G p.1 (mate p.2) = true ∧ p.1 ∈ rows then (rW n p.1, pW n p.2, pW n p.2)
  else if G p.1 (mate p.2) = true ∧ p.2 ∈ cols then (pW n p.1, cW n p.2, cW n p.2)
  else (5 * n, 5 * n, 5 * n)

def negT (p : Fin n × Fin n) : ℕ × ℕ × ℕ :=
  if G p.1 (mate p.2) = true ∧ G p.2 (mate p.1) = false then
    (if p.2 ∈ rows then (rW n p.2, pW n p.1, pW n p.1)
     else if p.1 ∈ cols then (pW n p.2, cW n p.1, cW n p.1)
     else (pW n p.1, pW n p.2, pW n p.2))
  else (5 * n, 5 * n, 5 * n)

def Kset (v : Fin n) : Finset ℕ :=
  (Finset.univ.filter (fun l : Fin n => rank v < rank l ∧
    (G v (mate l) = true ∨ G l (mate v) = true))).image (fun l => (rank l).val)

def Bp (v : Fin n) : Finset (ℕ × ℕ) :=
  ((insert (rank v).val (Kset n G mate rank v)) ×ˢ (insert n (Kset n G mate rank v))).filter
    (fun ab => ab.1 < ab.2 ∧ ∀ t ∈ Kset n G mate rank v, ¬ (ab.1 < t ∧ t < ab.2))

def absL : List (ℕ × ℕ × ℕ) :=
  (List.finRange n).flatMap (fun v => (Bp n G mate rank v).toList.map
    (fun ab => (pW n v, swW n (ab.1 + 1), twW n ab.2)))

def LM1 : List (ℕ × ℕ × ℕ) := (Eord n G mate).toList.map (posT n G mate rows cols)
def LH : List (ℕ × ℕ × ℕ) := (Eord n G mate).toList.map (negT n G mate rows cols) ++ absL n G mate rank
def LM2 : List (ℕ × ℕ × ℕ) :=
  (List.finRange n).map (fun a => if G a (mate a) = true then (pW n a, pW n a, pW n a)
    else (5 * n, 5 * n, 5 * n)) ++ [(twW n n, twW n n, twW n n)]

def r1 := orTerms (n + n) (gs0 n mate rank rows cols) (LM1 n G mate rows cols)
def r2 := orTerms (n + n) (r1 n G mate rank rows cols).1 (LH n G mate rank rows cols)
def r3 := orTerms (n + n) (r2 n G mate rank rows cols).1 (LM2 n G mate)

def gsF : List Gate :=
  (r3 n G mate rank rows cols).1 ++ [⟨GateOp.not, [(r2 n G mate rank rows cols).2]⟩] ++
    [⟨GateOp.and, [(r3 n G mate rank rows cols).2, n + n + (r3 n G mate rank rows cols).1.length]⟩] ++
    [⟨GateOp.or, [(r1 n G mate rank rows cols).2, n + n + (r3 n G mate rank rows cols).1.length + 1]⟩]

def circ : Circuit :=
  ⟨gsF n G mate rank rows cols, n + n + (r3 n G mate rank rows cols).1.length + 2⟩

theorem K_mem (v : Fin n) (t : ℕ) : t ∈ Kset n G mate rank v ↔
    ∃ l : Fin n, rank v < rank l ∧ (G v (mate l) = true ∨ G l (mate v) = true) ∧
      (rank l).val = t := by
  simp [Kset, and_assoc]

theorem K_lt (v : Fin n) (t : ℕ) (ht : t ∈ Kset n G mate rank v) :
    (rank v).val < t ∧ t < n := by
  obtain ⟨l, h1, _, rfl⟩ := (K_mem n G mate rank v t).mp ht
  exact ⟨h1, (rank l).isLt⟩

theorem Bp_bounds (v : Fin n) (ab : ℕ × ℕ) (h : ab ∈ Bp n G mate rank v) :
    (rank v).val ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ n ∧
      ∀ t ∈ Kset n G mate rank v, ¬ (ab.1 < t ∧ t < ab.2) := by
  simp only [Bp, Finset.mem_filter, Finset.mem_product, Finset.mem_insert] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨?_, h3, ?_, h4⟩
  · rcases h1 with h1 | h1
    · omega
    · exact (K_lt n G mate rank v _ h1).1.le
  · rcases h2 with h2 | h2
    · omega
    · exact (K_lt n G mate rank v _ h2).2.le

theorem Bp_sound (v o : Fin n) (ab : ℕ × ℕ) (h : ab ∈ Bp n G mate rank v)
    (h1 : ab.1 < (rank o).val) (h2 : (rank o).val < ab.2)
    (hlt : rank v < rank o) (hE : G v (mate o) = true ∨ G o (mate v) = true) : False := by
  have := (Bp_bounds n G mate rank v ab h).2.2.2 (rank o).val
    ((K_mem n G mate rank v _).mpr ⟨o, hlt, hE, rfl⟩)
  exact this ⟨h1, h2⟩

theorem Bp_complete (v o : Fin n) (hlt : rank v < rank o)
    (hE : ¬ (G v (mate o) = true ∨ G o (mate v) = true)) :
    ∃ ab ∈ Bp n G mate rank v, ab.1 < (rank o).val ∧ (rank o).val < ab.2 := by
  set K := Kset n G mate rank v
  set j := (rank o).val
  have hjK : j ∉ K := by
    intro hj
    obtain ⟨l, h1, h2, h3⟩ := (K_mem n G mate rank v j).mp hj
    have : l = o := rank.injective (Fin.ext h3)
    subst this; exact hE h2
  have hlo : ((insert (rank v).val K).filter (· < j)).Nonempty :=
    ⟨(rank v).val, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hlt⟩⟩
  have hhi : ((insert n K).filter (j < ·)).Nonempty :=
    ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, (rank o).isLt⟩⟩
  set a := ((insert (rank v).val K).filter (· < j)).max' hlo
  set b := ((insert n K).filter (j < ·)).min' hhi
  have ha := Finset.max'_mem _ hlo
  have hb := Finset.min'_mem _ hhi
  rw [Finset.mem_filter] at ha hb
  refine ⟨(a, b), ?_, ha.2, hb.2⟩
  simp only [Bp, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨ha.1, hb.1⟩, by omega, ?_⟩
  intro t ht ⟨h1, h2⟩
  rcases lt_trichotomy t j with htj | htj | htj
  · have : t ≤ a := Finset.le_max' _ t (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem ht, htj⟩)
    omega
  · exact hjK (htj ▸ ht)
  · have : b ≤ t := Finset.min'_le _ t (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem ht, htj⟩)
    omega

theorem Bp_card (v : Fin n) : (Bp n G mate rank v).card ≤ (Kset n G mate rank v).card + 1 := by
  calc (Bp n G mate rank v).card ≤ (insert (rank v).val (Kset n G mate rank v)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro ab hab
          rw [Finset.mem_coe] at hab
          simp only [Bp, Finset.mem_filter, Finset.mem_product] at hab
          exact hab.1.1
        · intro ab hab ab' hab' he
          have h1 := Bp_bounds n G mate rank v ab hab
          have h2 := Bp_bounds n G mate rank v ab' hab'
          rw [Finset.mem_coe] at hab hab'
          simp only [Bp, Finset.mem_filter, Finset.mem_product, Finset.mem_insert] at hab hab'
          rcases lt_trichotomy ab.2 ab'.2 with hl | hl | hl
          · exfalso
            rcases hab.1.2 with h | h
            · omega
            · exact h2.2.2.2 _ h ⟨by rw [← he]; exact h1.2.1, hl⟩
          · exact Prod.ext he hl
          · exfalso
            rcases hab'.1.2 with h | h
            · omega
            · exact h1.2.2.2 _ h ⟨by rw [he]; exact h2.2.1, hl⟩
    _ ≤ _ := Finset.card_insert_le _ _

theorem K_card (d : ℕ) (hdeg : ∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
    rank v < rank later ∧ (G v (mate later) = true ∨ G later (mate v) = true))).card ≤ d)
    (v : Fin n) : (Kset n G mate rank v).card ≤ d :=
  Finset.card_image_le.trans (hdeg v)

end build

section sem
variable (n : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
  (rows cols : Finset (Fin n))

theorem qW_spec (u w : Fin n) : ∀ k < n, n + n ≤ qW n rank k ∧ qW n rank k < 5 * n ∧
    V (pre n mate rows cols) (Represents.oneEach u (mate w)) (qW n rank k) =
      decide (k = (rank u).val ∨ k = (rank w).val) := by
  intro k hk
  simp only [qW, dif_pos hk]
  refine ⟨by omega, by have := (rank.symm ⟨k, hk⟩).isLt; omega, ?_⟩
  rw [pre_valP]
  apply bdec
  rw [mate.injective.eq_iff, Equiv.symm_apply_eq, Equiv.symm_apply_eq, Fin.ext_iff, Fin.ext_iff]

theorem gs0_spec (u w : Fin n) :
    BodyExt (n + n) (pre n mate rows cols) (gs0 n mate rank rows cols) ∧
    (gs0 n mate rank rows cols).length = 7 * n + 1 ∧
    (∀ i, V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (pW n i) =
      decide (i = u ∨ i = w)) ∧
    (∀ i, V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (rW n i) =
      decide (i = u ∧ i ∈ rows)) ∧
    (∀ i, V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (cW n i) =
      decide (i = w ∧ i ∈ cols)) ∧
    V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (5 * n) = false ∧
    (∀ s, V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (swW n s) =
      decide (s ≤ (rank u).val ∨ s ≤ (rank w).val)) ∧
    (∀ k ≤ n, V (gs0 n mate rank rows cols) (Represents.oneEach u (mate w)) (twW n k) =
      decide ((rank u).val ≠ (rank w).val ∧ (rank u).val < k ∧ (rank w).val < k)) := by
  set x := Represents.oneEach u (mate w)
  have hx : x.length = n + n := oe_len _ _
  have hq := qW_spec n mate rank rows cols u w
  have hF := pre_valF n mate rows cols u (mate w)
  obtain ⟨eP, lP, vP⟩ := scanP_spec n (qW n rank) (pre n mate rows cols) x hx
    (pre_len n mate rows cols) _ _ hF hq n (le_refl _)
  set sp := scanP n (qW n rank) (pre n mate rows cols) n
  have hq' : ∀ k < n, n + n ≤ qW n rank k ∧ qW n rank k < 5 * n ∧
      V sp x (qW n rank k) = decide (k = (rank u).val ∨ k = (rank w).val) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hq k hk
    refine ⟨h1, h2, ?_⟩
    rw [eP.V_eq x (by rw [hx, pre_len]; omega)]; exact h3
  have hF' : V sp x (5 * n) = false := by
    rw [eP.V_eq x (by rw [hx, pre_len]; omega)]; exact hF
  obtain ⟨eS, lS, vS⟩ := scanS_spec n (qW n rank) sp x hx (by rw [lP]; ring) _ _
    (rank u).isLt (rank w).isLt hF' hq' n (le_refl _)
  have e := eP.trans eS
  have vpre : ∀ wi < 5 * n + 1, V (gs0 n mate rank rows cols) x wi = V (pre n mate rows cols) x wi :=
    fun wi hwi => e.V_eq x (by rw [hx, pre_len]; omega)
  refine ⟨e, by simp only [gs0]; rw [lS]; ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [pW, vpre _ (by omega), pre_valP]; simp [mate.injective.eq_iff]
  · intro i
    rw [rW, vpre _ (by omega), pre_valR]
  · intro i
    rw [cW, vpre _ (by omega), pre_valC]; simp [mate.injective.eq_iff]
  · rw [vpre _ (by omega)]; exact hF
  · intro s'; exact vS s' (by omega)
  · intro k hk
    have h := (vP k hk).2
    have : twW n k < n + n + sp.length := by rw [lP]; unfold twW; split_ifs <;> omega
    rw [show gs0 n mate rank rows cols = scanS n (qW n rank) sp n from rfl,
      eS.V_eq x (by rw [hx]; omega)]
    exact h

def Fi (gs : List Gate) (x : List Bool) (t : ℕ × ℕ × ℕ) : Prop :=
  V gs x t.1 = true ∧ V gs x t.2.1 = true ∧ V gs x t.2.2 = true

end sem

section logic
variable (n : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
  (rows cols : Finset (Fin n)) (gs : List Gate) (x : List Bool) (u w : Fin n)

structure Vals : Prop where
  P : ∀ i, V gs x (pW n i) = decide (i = u ∨ i = w)
  R : ∀ i, V gs x (rW n i) = decide (i = u ∧ i ∈ rows)
  C : ∀ i, V gs x (cW n i) = decide (i = w ∧ i ∈ cols)
  F : V gs x (5 * n) = false
  S : ∀ s, V gs x (swW n s) = decide (s ≤ (rank u).val ∨ s ≤ (rank w).val)
  T : ∀ k ≤ n, V gs x (twW n k) =
    decide ((rank u).val ≠ (rank w).val ∧ (rank u).val < k ∧ (rank w).val < k)

variable {n G mate rank rows cols gs x u w}

theorem rank_ne_iff : (rank u).val ≠ (rank w).val ↔ u ≠ w := by
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; exact h (rank.injective (Fin.ext e))

theorem abs_mem (t : ℕ × ℕ × ℕ) : t ∈ absL n G mate rank ↔
    ∃ v : Fin n, ∃ ab ∈ Bp n G mate rank v, t = (pW n v, swW n (ab.1 + 1), twW n ab.2) := by
  simp only [absL, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    Finset.mem_toList]
  constructor
  · rintro ⟨v, ab, hab, rfl⟩; exact ⟨v, ab, hab, rfl⟩
  · rintro ⟨v, ab, hab, rfl⟩; exact ⟨v, ab, hab, rfl⟩

theorem abs_sound (hv : Vals n rank rows cols gs x u w) :
    (∃ t ∈ absL n G mate rank, Fi gs x t) →
      u ≠ w ∧ ¬ (G u (mate w) = true ∨ G w (mate u) = true) := by
  rintro ⟨t, ht, hf⟩
  obtain ⟨z, ab, hab, rfl⟩ := (abs_mem t).mp ht
  obtain ⟨hz, hα, hβ, -⟩ := Bp_bounds n G mate rank z ab hab
  simp only [Fi, hv.P, hv.S, hv.T _ hβ, decide_eq_true_eq] at hf
  obtain ⟨hzz, h1, hne, h2, h3⟩ := hf
  have huw : u ≠ w := rank_ne_iff.mp hne
  refine ⟨huw, fun hE => ?_⟩
  rcases hzz with rfl | rfl
  · exact Bp_sound n G mate rank z w ab hab (by omega) (by omega)
      (Fin.lt_iff_val_lt_val.mpr (by omega)) hE
  · exact Bp_sound n G mate rank z u ab hab (by omega) (by omega)
      (Fin.lt_iff_val_lt_val.mpr (by omega)) hE.symm

theorem abs_complete (hv : Vals n rank rows cols gs x u w) (huw : u ≠ w)
    (hE : ¬ (G u (mate w) = true ∨ G w (mate u) = true)) :
    ∃ t ∈ absL n G mate rank, Fi gs x t := by
  have hne := (rank_ne_iff (rank := rank)).mpr huw
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨ab, hab, h1, h2⟩ := Bp_complete n G mate rank u w (Fin.lt_iff_val_lt_val.mpr hlt) hE
    obtain ⟨hz, hα, hβ, -⟩ := Bp_bounds n G mate rank u ab hab
    refine ⟨_, (abs_mem _).mpr ⟨u, ab, hab, rfl⟩, ?_⟩
    simp only [Fi, hv.P, hv.S, hv.T _ hβ, decide_eq_true_eq]
    exact ⟨by simp, by omega, hne, by omega, by omega⟩
  · obtain ⟨ab, hab, h1, h2⟩ := Bp_complete n G mate rank w u (Fin.lt_iff_val_lt_val.mpr hlt)
      (fun h => hE h.symm)
    obtain ⟨hz, hα, hβ, -⟩ := Bp_bounds n G mate rank w ab hab
    refine ⟨_, (abs_mem _).mpr ⟨w, ab, hab, rfl⟩, ?_⟩
    simp only [Fi, hv.P, hv.S, hv.T _ hβ, decide_eq_true_eq]
    exact ⟨by simp, by omega, hne, by omega, by omega⟩

theorem mem_Eord (a b : Fin n) : (a, b) ∈ Eord n G mate ↔
    a ≠ b ∧ (G a (mate b) = true ∨ G b (mate a) = true) := by
  simp [Eord]

theorem F1 (hv : Vals n rank rows cols gs x u w) :
    (∃ t ∈ LM1 n G mate rows cols, Fi gs x t) → u ≠ w ∧ G u (mate w) = true := by
  rintro ⟨t, ht, hf⟩
  simp only [LM1, List.mem_map, Finset.mem_toList] at ht
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := ht
  obtain ⟨hab, -⟩ := (mem_Eord a b).mp hp
  unfold posT at hf
  simp only at hf
  split_ifs at hf with h1 h2 h3
  · simp only [Fi, hv.P, decide_eq_true_eq] at hf
    obtain ⟨ha | ha, hb | hb, -⟩ := hf <;> subst ha <;> subst hb
    · exact absurd rfl hab
    · exact ⟨hab, h1.1⟩
    · exact ⟨hab.symm, h1.2⟩
    · exact absurd rfl hab
  · simp only [Fi, hv.P, hv.R, decide_eq_true_eq] at hf
    obtain ⟨⟨rfl, -⟩, hb | hb, -⟩ := hf
    · exact absurd hb.symm hab
    · subst hb; exact ⟨hab, h2.1⟩
  · simp only [Fi, hv.P, hv.C, decide_eq_true_eq] at hf
    obtain ⟨ha | ha, ⟨rfl, -⟩, -⟩ := hf
    · subst ha; exact ⟨hab, h3.1⟩
    · exact absurd ha hab
  · simp [Fi, hv.F] at hf

theorem F2 (hv : Vals n rank rows cols gs x u w) (huw : u ≠ w) (h : G u (mate w) = true)
    (h' : G w (mate u) = true ∨ u ∈ rows ∨ w ∈ cols) :
    ∃ t ∈ LM1 n G mate rows cols, Fi gs x t := by
  refine ⟨posT n G mate rows cols (u, w), ?_, ?_⟩
  · simp only [LM1, List.mem_map, Finset.mem_toList]
    exact ⟨(u, w), (mem_Eord u w).mpr ⟨huw, Or.inl h⟩, rfl⟩
  · unfold posT; simp only
    split_ifs with h1 h2 h3
    · simp [Fi, hv.P]
    · simp [Fi, hv.P, hv.R, h2.2]
    · simp [Fi, hv.P, hv.C, h3.2]
    · exfalso
      rcases h' with h' | h' | h'
      · exact h1 ⟨h, h'⟩
      · exact h2 ⟨h, h'⟩
      · exact h3 ⟨h, h'⟩

theorem F3b (hv : Vals n rank rows cols gs x u w) :
    (∃ t ∈ LH n G mate rank rows cols, Fi gs x t) → u ≠ w := by
  rintro ⟨t, ht, hf⟩
  simp only [LH, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [List.mem_map, Finset.mem_toList] at ht
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := ht
    obtain ⟨hab, -⟩ := (mem_Eord a b).mp hp
    unfold negT at hf
    simp only at hf
    split_ifs at hf with h1 h2 h3
    · simp only [Fi, hv.P, hv.R, decide_eq_true_eq] at hf
      obtain ⟨⟨rfl, -⟩, ha | ha, -⟩ := hf
      · exact absurd ha hab
      · subst ha; exact Ne.symm hab
    · simp only [Fi, hv.P, hv.C, decide_eq_true_eq] at hf
      obtain ⟨hb | hb, ⟨rfl, -⟩, -⟩ := hf
      · subst hb; exact Ne.symm hab
      · exact absurd hb.symm hab
    · simp only [Fi, hv.P, decide_eq_true_eq] at hf
      obtain ⟨ha | ha, hb | hb, -⟩ := hf <;> subst ha <;> subst hb
      · exact absurd rfl hab
      · exact hab
      · exact hab.symm
      · exact absurd rfl hab
    · simp [Fi, hv.F] at hf
  · exact (abs_sound hv ⟨t, ht, hf⟩).1

theorem F3c (hv : Vals n rank rows cols gs x u u) :
    (∃ t ∈ LM2 n G mate, Fi gs x t) ↔ G u (mate u) = true := by
  constructor
  · rintro ⟨t, ht, hf⟩
    simp only [LM2, List.mem_append, List.mem_map, List.mem_finRange, true_and,
      List.mem_singleton] at ht
    rcases ht with ⟨a, rfl⟩ | rfl
    · split_ifs at hf with h1
      · simp only [Fi, hv.P, decide_eq_true_eq, or_self] at hf
        rw [← hf.1]; exact h1
      · simp [Fi, hv.F] at hf
    · simp [Fi, hv.T n (le_refl _)] at hf
  · intro h
    refine ⟨(pW n u, pW n u, pW n u), ?_, by simp [Fi, hv.P]⟩
    simp only [LM2, List.mem_append, List.mem_map, List.mem_finRange, true_and]
    exact Or.inl ⟨u, by simp [h]⟩

theorem F4 (hv : Vals n rank rows cols gs x u w) (huw : u ≠ w) :
    ∃ t ∈ LM2 n G mate, Fi gs x t := by
  refine ⟨(twW n n, twW n n, twW n n), by simp [LM2], ?_⟩
  simp only [Fi, hv.T n (le_refl _), decide_eq_true_eq]
  have := (rank_ne_iff (rank := rank)).mpr huw
  have h1 := (rank u).isLt
  have h2 := (rank w).isLt
  exact ⟨⟨this, h1, h2⟩, ⟨this, h1, h2⟩, ⟨this, h1, h2⟩⟩

theorem F5 (hv : Vals n rank rows cols gs x u w) (huw : u ≠ w) (h : G u (mate w) = false) :
    ∃ t ∈ LH n G mate rank rows cols, Fi gs x t := by
  by_cases h' : G w (mate u) = true
  · refine ⟨negT n G mate rows cols (w, u), ?_, ?_⟩
    · simp only [LH, List.mem_append, List.mem_map, Finset.mem_toList]
      exact Or.inl ⟨(w, u), (mem_Eord w u).mpr ⟨Ne.symm huw, Or.inl h'⟩, rfl⟩
    · unfold negT; simp only
      rw [if_pos ⟨h', h⟩]
      split_ifs with h1 h2
      · simp [Fi, hv.P, hv.R, h1]
      · simp [Fi, hv.P, hv.C, h2]
      · simp [Fi, hv.P]
  · refine (abs_complete hv huw ?_).elim (fun t ht => ⟨t, List.mem_append_right _ ht.1, ht.2⟩)
    rintro (h1 | h1)
    · rw [h] at h1; exact absurd h1 (by simp)
    · exact h' h1

theorem F6 (hv : Vals n rank rows cols gs x u w)
    (hcov : u ∈ rows ∨ w ∈ cols ∨ w ∈ rows ∨ u ∈ cols)
    (h : G u (mate w) = true) (h' : G w (mate u) = false) (hr : u ∉ rows) (hc : w ∉ cols) :
    ¬ ∃ t ∈ LH n G mate rank rows cols, Fi gs x t := by
  rintro ⟨t, ht, hf⟩
  simp only [LH, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [List.mem_map, Finset.mem_toList] at ht
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := ht
    obtain ⟨hab, -⟩ := (mem_Eord a b).mp hp
    unfold negT at hf
    simp only at hf
    split_ifs at hf with h1 h2 h3
    · simp only [Fi, hv.P, hv.R, decide_eq_true_eq] at hf
      obtain ⟨⟨rfl, -⟩, -, -⟩ := hf
      exact hr h2
    · simp only [Fi, hv.P, hv.C, decide_eq_true_eq] at hf
      obtain ⟨-, ⟨rfl, -⟩, -⟩ := hf
      exact hc h3
    · simp only [Fi, hv.P, decide_eq_true_eq] at hf
      obtain ⟨ha | ha, hb | hb, -⟩ := hf <;> subst ha <;> subst hb
      · exact hab rfl
      · rcases hcov with hh | hh | hh | hh
        · exact hr hh
        · exact hc hh
        · exact h2 hh
        · exact h3 hh
      · rw [h'] at h1; exact absurd h1.1 (by simp)
      · exact hab rfl
    · simp [Fi, hv.F] at hf
  · exact (abs_sound hv ⟨t, ht, hf⟩).2 (Or.inl h)

end logic

theorem scanP_struct (n : ℕ) (q : ℕ → ℕ) (base : List Gate) (hb : base.length = 3 * n + 1)
    (hq : ∀ k < n, n + n ≤ q k ∧ q k < 5 * n) :
    ∀ k ≤ n, BodyExt (n + n) base (scanP n q base k) ∧
      (scanP n q base k).length = 3 * n + 1 + 3 * k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨BodyExt.refl _ _, by simp [scanP, hb]⟩
  | succ k ih =>
    intro hk
    obtain ⟨e, hl⟩ := ih (by omega)
    obtain ⟨hq1, hq2⟩ := hq k (by omega)
    set gs := scanP n q base k
    have hpw : pwW n k < 5 * n + 1 + 3 * k ∧ n + n ≤ pwW n k := by
      unfold pwW; split_ifs <;> omega
    have htw : twW n k < 5 * n + 1 + 3 * k ∧ n + n ≤ twW n k := by
      unfold twW; split_ifs <;> omega
    have e1 : BodyExt (n + n) gs (gs ++ [⟨GateOp.and, [pwW n k, q k]⟩]) :=
      BodyExt.snoc _ (Or.inl rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    have e2 : BodyExt (n + n) (gs ++ [⟨GateOp.and, [pwW n k, q k]⟩])
        (gs ++ [⟨GateOp.and, [pwW n k, q k]⟩] ++ [⟨GateOp.or, [twW n k, xW n k]⟩]) :=
      BodyExt.snoc _ (Or.inr rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [xW] <;> omega)
    have e3 : BodyExt (n + n) (gs ++ [⟨GateOp.and, [pwW n k, q k]⟩] ++
        [⟨GateOp.or, [twW n k, xW n k]⟩])
        (gs ++ [⟨GateOp.and, [pwW n k, q k]⟩] ++ [⟨GateOp.or, [twW n k, xW n k]⟩] ++
          [⟨GateOp.or, [pwW n k, q k]⟩]) :=
      BodyExt.snoc _ (Or.inr rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    exact ⟨e.trans ((e1.trans e2).trans e3), by simp [scanP, gs] at hl ⊢; rw [hl]; ring⟩

theorem scanS_struct (n : ℕ) (q : ℕ → ℕ) (base : List Gate) (hb : base.length = 6 * n + 1)
    (hq : ∀ k < n, n + n ≤ q k ∧ q k < 5 * n) :
    ∀ t ≤ n, BodyExt (n + n) base (scanS n q base t) ∧
      (scanS n q base t).length = 6 * n + 1 + t := by
  intro t
  induction t with
  | zero => intro _; exact ⟨BodyExt.refl _ _, by simp [scanS, hb]⟩
  | succ t ih =>
    intro ht
    obtain ⟨e, hl⟩ := ih (by omega)
    obtain ⟨hq1, hq2⟩ := hq (n - 1 - t) (by omega)
    have hsw : swW n (n - t) < 8 * n + 1 + t ∧ n + n ≤ swW n (n - t) := by
      unfold swW; split_ifs <;> omega
    have e1 : BodyExt (n + n) (scanS n q base t)
        (scanS n q base t ++ [⟨GateOp.or, [swW n (n - t), q (n - 1 - t)]⟩]) :=
      BodyExt.snoc _ (Or.inr rfl) (by simp) (by
        intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    exact ⟨e.trans e1, by simp [scanS, hl]; ring⟩

theorem Fi_transfer {N B : ℕ} {gs gs' : List Gate} (e : BodyExt N gs gs') (x : List Bool)
    {L : List (ℕ × ℕ × ℕ)} (hL : TermsIn N B L) (hB : B ≤ x.length + gs.length) :
    (∃ t ∈ L, Fi gs' x t) ↔ (∃ t ∈ L, Fi gs x t) := by
  constructor
  · rintro ⟨t, ht, hf⟩
    have h := hL t ht
    refine ⟨t, ht, ?_⟩
    unfold Fi at hf ⊢
    rwa [e.V_eq x (by omega), e.V_eq x (by omega), e.V_eq x (by omega)] at hf
  · rintro ⟨t, ht, hf⟩
    have h := hL t ht
    refine ⟨t, ht, ?_⟩
    unfold Fi at hf ⊢
    rwa [e.V_eq x (by omega), e.V_eq x (by omega), e.V_eq x (by omega)]

section final
variable (n : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
  (rows cols : Finset (Fin n))

theorem qW_bounds : ∀ k < n, n + n ≤ qW n rank k ∧ qW n rank k < 5 * n := by
  intro k hk
  simp only [qW, dif_pos hk]
  exact ⟨by omega, by have := (rank.symm ⟨k, hk⟩).isLt; omega⟩

theorem gs0_struct : BodyExt (n + n) (pre n mate rows cols) (gs0 n mate rank rows cols) ∧
    (gs0 n mate rank rows cols).length = 7 * n + 1 := by
  obtain ⟨eP, lP⟩ := scanP_struct n (qW n rank) (pre n mate rows cols) (pre_len n mate rows cols)
    (qW_bounds n rank) n (le_refl _)
  obtain ⟨eS, lS⟩ := scanS_struct n (qW n rank) _ (by rw [lP]; ring) (qW_bounds n rank) n
    (le_refl _)
  exact ⟨eP.trans eS, by simp only [gs0]; rw [lS]; ring⟩

theorem TI_LM1 : TermsIn (n + n) (9 * n + 1) (LM1 n G mate rows cols) := by
  intro t ht
  simp only [LM1, List.mem_map, Finset.mem_toList] at ht
  obtain ⟨⟨a, b⟩, -, rfl⟩ := ht
  have := a.isLt; have := b.isLt
  unfold posT; simp only
  split_ifs <;> simp only [pW, rW, cW] <;> omega

theorem tw_bound (k : ℕ) (hk : k ≤ n) : n + n ≤ twW n k ∧ twW n k < 9 * n + 1 := by
  unfold twW; split_ifs <;> omega

theorem sw_bound (s : ℕ) : n + n ≤ swW n s ∧ swW n s < 9 * n + 1 := by
  unfold swW; split_ifs <;> omega

theorem TI_LH : TermsIn (n + n) (9 * n + 1) (LH n G mate rank rows cols) := by
  intro t ht
  simp only [LH, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [List.mem_map, Finset.mem_toList] at ht
    obtain ⟨⟨a, b⟩, -, rfl⟩ := ht
    have := a.isLt; have := b.isLt
    unfold negT; simp only
    split_ifs <;> simp only [pW, rW, cW] <;> omega
  · obtain ⟨z, ab, hab, rfl⟩ := (abs_mem t).mp ht
    have hz := z.isLt
    obtain ⟨-, -, hβ, -⟩ := Bp_bounds n G mate rank z ab hab
    have h1 := tw_bound n ab.2 hβ
    have h2 := sw_bound n (ab.1 + 1)
    simp only [pW]
    omega

theorem TI_LM2 : TermsIn (n + n) (9 * n + 1) (LM2 n G mate) := by
  intro t ht
  simp only [LM2, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_singleton] at ht
  rcases ht with ⟨a, rfl⟩ | rfl
  · have := a.isLt
    split_ifs <;> simp only [pW] <;> omega
  · have := tw_bound n n (le_refl _)
    simp only
    omega

theorem Eord_card (d : ℕ) (hdeg : ∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
    rank v < rank later ∧ (G v (mate later) = true ∨ G later (mate v) = true))).card ≤ d) :
    (Eord n G mate).card ≤ 2 * (n * d) := by
  set Fw : Finset (Fin n × Fin n) := Finset.univ.biUnion (fun a => (Finset.univ.filter
    (fun later : Fin n => rank a < rank later ∧
      (G a (mate later) = true ∨ G later (mate a) = true))).image (fun b => (a, b)))
  have hFw : Fw.card ≤ n * d := by
    calc Fw.card ≤ ∑ a : Fin n, ((Finset.univ.filter (fun later : Fin n => rank a < rank later ∧
          (G a (mate later) = true ∨ G later (mate a) = true))).image (fun b => (a, b))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _a : Fin n, d := Finset.sum_le_sum (fun a _ => Finset.card_image_le.trans (hdeg a))
      _ = n * d := by simp
  have hsub : Eord n G mate ⊆ Fw ∪ Fw.image Prod.swap := by
    intro p hp
    obtain ⟨a, b⟩ := p
    obtain ⟨hab, hE⟩ := (mem_Eord a b).mp hp
    have hr : rank a ≠ rank b := fun h => hab (rank.injective h)
    rcases lt_or_gt_of_ne hr with h | h
    · apply Finset.mem_union_left
      simp only [Fw, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_filter, Prod.mk.injEq]
      exact ⟨a, b, ⟨h, hE⟩, rfl, rfl⟩
    · apply Finset.mem_union_right
      simp only [Fw, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_filter]
      exact ⟨(b, a), ⟨b, a, ⟨h, hE.symm⟩, rfl⟩, rfl⟩
  calc (Eord n G mate).card ≤ (Fw ∪ Fw.image Prod.swap).card := Finset.card_le_card hsub
    _ ≤ Fw.card + (Fw.image Prod.swap).card := Finset.card_union_le _ _
    _ ≤ Fw.card + Fw.card := by have := Finset.card_image_le (s := Fw) (f := Prod.swap); omega
    _ ≤ 2 * (n * d) := by omega

theorem absL_len (d : ℕ) (hdeg : ∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
    rank v < rank later ∧ (G v (mate later) = true ∨ G later (mate v) = true))).card ≤ d) :
    (absL n G mate rank).length ≤ n * (d + 1) := by
  unfold absL
  rw [List.length_flatMap]
  have h := List.sum_le_length_nsmul ((List.finRange n).map fun v =>
    ((Bp n G mate rank v).toList.map (fun ab => (pW n v, swW n (ab.1 + 1), twW n ab.2))).length)
    (d + 1) (by
      intro y hy
      simp only [List.mem_map, List.mem_finRange, true_and] at hy
      obtain ⟨v, rfl⟩ := hy
      simp only [List.length_map, Finset.length_toList]
      exact (Bp_card n G mate rank v).trans (by have := K_card n G mate rank d hdeg v; omega))
  simpa using h

end final

section assemble
variable (n : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
  (rows cols : Finset (Fin n))

theorem chain_struct :
    BodyExt (n + n) (gs0 n mate rank rows cols) (r1 n G mate rank rows cols).1 ∧
    (r1 n G mate rank rows cols).1.length =
      (gs0 n mate rank rows cols).length + 3 * (LM1 n G mate rows cols).length + 1 ∧
    n + n ≤ (r1 n G mate rank rows cols).2 ∧
    (r1 n G mate rank rows cols).2 < n + n + (r1 n G mate rank rows cols).1.length ∧
    BodyExt (n + n) (r1 n G mate rank rows cols).1 (r2 n G mate rank rows cols).1 ∧
    (r2 n G mate rank rows cols).1.length =
      (r1 n G mate rank rows cols).1.length + 3 * (LH n G mate rank rows cols).length + 1 ∧
    n + n ≤ (r2 n G mate rank rows cols).2 ∧
    (r2 n G mate rank rows cols).2 < n + n + (r2 n G mate rank rows cols).1.length ∧
    BodyExt (n + n) (r2 n G mate rank rows cols).1 (r3 n G mate rank rows cols).1 ∧
    (r3 n G mate rank rows cols).1.length =
      (r2 n G mate rank rows cols).1.length + 3 * (LM2 n G mate).length + 1 ∧
    n + n ≤ (r3 n G mate rank rows cols).2 ∧
    (r3 n G mate rank rows cols).2 < n + n + (r3 n G mate rank rows cols).1.length := by
  obtain ⟨eG, lG⟩ := gs0_struct n mate rank rows cols
  have hx0 : (List.replicate (n + n) false).length = n + n := by simp
  obtain ⟨e1, l1, a1, b1, -⟩ := orTerms_spec (n + n) _ hx0 (9 * n + 1) _
    (TI_LM1 n G mate rows cols) (gs0 n mate rank rows cols) (by rw [lG]; omega)
  obtain ⟨e2, l2, a2, b2, -⟩ := orTerms_spec (n + n) _ hx0 (9 * n + 1) _
    (TI_LH n G mate rank rows cols) (r1 n G mate rank rows cols).1
    (by have h := e1.len; rw [lG] at h
        exact le_trans (b := n + n + (7 * n + 1)) (by omega) (Nat.add_le_add_left h _))
  obtain ⟨e3, l3, a3, b3, -⟩ := orTerms_spec (n + n) _ hx0 (9 * n + 1) _
    (TI_LM2 n G mate) (r2 n G mate rank rows cols).1
    (by have h := le_trans e1.len e2.len; rw [lG] at h
        exact le_trans (b := n + n + (7 * n + 1)) (by omega) (Nat.add_le_add_left h _))
  exact ⟨e1, l1, a1, b1, e2, l2, a2, b2, e3, l3, a3, b3⟩

theorem out_correct (hcov : ∀ i j, G i (mate j) = true → G j (mate i) = false →
      i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols) (u w : Fin n) :
    (circ n G mate rank rows cols).eval (Represents.oneEach u (mate w)) = G u (mate w) := by
  set x := Represents.oneEach u (mate w)
  have hx : x.length = n + n := oe_len _ _
  obtain ⟨eG, lG, hP, hR, hC, hF, hS, hT⟩ := gs0_spec n mate rank rows cols u w
  have hv : Vals n rank rows cols (gs0 n mate rank rows cols) x u w := ⟨hP, hR, hC, hF, hS, hT⟩
  obtain ⟨e1, -, -, b1, e2, -, -, b2, e3, -, -, b3⟩ := chain_struct n G mate rank rows cols
  set R1 := r1 n G mate rank rows cols
  set R2 := r2 n G mate rank rows cols
  set R3 := r3 n G mate rank rows cols
  have M1 : V R1.1 x R1.2 = true ↔ ∃ t ∈ LM1 n G mate rows cols, Fi (gs0 n mate rank rows cols) x t :=
    (orTerms_spec (n + n) x hx (9 * n + 1) _ (TI_LM1 n G mate rows cols)
      (gs0 n mate rank rows cols) (by rw [lG]; omega)).2.2.2.2
  have H : V R2.1 x R2.2 = true ↔ ∃ t ∈ LH n G mate rank rows cols,
      Fi (gs0 n mate rank rows cols) x t :=
    (orTerms_spec (n + n) x hx (9 * n + 1) _ (TI_LH n G mate rank rows cols) R1.1
      (by have := e1.len; rw [lG] at this; omega)).2.2.2.2.trans
      (Fi_transfer e1 x (TI_LH n G mate rank rows cols) (by rw [hx, lG]; omega))
  have M2 : V R3.1 x R3.2 = true ↔ ∃ t ∈ LM2 n G mate, Fi (gs0 n mate rank rows cols) x t :=
    (orTerms_spec (n + n) x hx (9 * n + 1) _ (TI_LM2 n G mate) R2.1
      (by have := e1.len; have := e2.len; rw [lG] at *; omega)).2.2.2.2.trans
      (Fi_transfer (e1.trans e2) x (TI_LM2 n G mate) (by rw [hx, lG]; omega))
  set L := R3.1.length
  set g1 : Gate := ⟨GateOp.not, [R2.2]⟩
  set g2 : Gate := ⟨GateOp.and, [R3.2, n + n + L]⟩
  set g3 : Gate := ⟨GateOp.or, [R1.2, n + n + L + 1]⟩
  have hgs : gsF n G mate rank rows cols = R3.1 ++ [g1] ++ [g2] ++ [g3] := rfl
  have l1 := e3.len
  have l0 := e2.len
  have w1 : V (R3.1 ++ [g1]) x (n + n + L) = !V R3.1 x R2.2 := by
    rw [snoc_val _ _ x _ (by rw [hx])]; simp [g1, GateOp.eval]
  have w2 : V (R3.1 ++ [g1] ++ [g2]) x (n + n + L + 1) = (V R3.1 x R3.2 && !V R3.1 x R2.2) := by
    rw [snoc_val _ _ x _ (by rw [hx]; simp [L]; ring)]
    simp only [g2, GateOp.eval, List.map_cons, List.map_nil, w1]
    rw [V_prefix _ _ x (w := R3.2) (by rw [hx]; exact b3)]
    simp
  have w3 : V (R3.1 ++ [g1] ++ [g2] ++ [g3]) x (n + n + L + 2) =
      (V R3.1 x R1.2 || (V R3.1 x R3.2 && !V R3.1 x R2.2)) := by
    rw [snoc_val _ _ x _ (by rw [hx]; simp [L]; ring)]
    simp only [g3, GateOp.eval, List.map_cons, List.map_nil, w2]
    rw [V_prefix (R3.1 ++ [g1]) [g2] x (w := R1.2) (by rw [hx]; simp; omega),
      V_prefix R3.1 [g1] x (w := R1.2) (by rw [hx]; omega)]
    simp
  have hout : (circ n G mate rank rows cols).eval x =
      (V R1.1 x R1.2 || (V R3.1 x R3.2 && !V R2.1 x R2.2)) := by
    rw [eval_eq]
    show V (gsF n G mate rank rows cols) x (n + n + L + 2) = _
    rw [hgs, w3, (e2.trans e3).V_eq x (w := R1.2) (by rw [hx]; exact b1),
      e3.V_eq x (w := R2.2) (by rw [hx]; exact b2)]
  rw [hout]
  by_cases huw : u = w
  · subst huw
    have m1f : V R1.1 x R1.2 = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      exact (F1 hv (M1.mp h)).1 rfl
    have hf : V R2.1 x R2.2 = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      exact F3b hv (H.mp h) rfl
    rw [m1f, hf]
    simp only [Bool.false_or, Bool.not_false, Bool.and_true]
    exact Bool.eq_iff_iff.mpr (M2.trans (F3c hv))
  · have m2t : V R3.1 x R3.2 = true := M2.mpr (F4 hv huw)
    rw [m2t]
    cases hG : G u (mate w)
    · have m1f : V R1.1 x R1.2 = false := by
        by_contra h; simp only [Bool.not_eq_false] at h
        rw [(F1 hv (M1.mp h)).2] at hG; exact absurd hG (by simp)
      have ht : V R2.1 x R2.2 = true := H.mpr (F5 hv huw hG)
      rw [m1f, ht]; rfl
    · by_cases h' : G w (mate u) = true ∨ u ∈ rows ∨ w ∈ cols
      · rw [M1.mpr (F2 hv huw hG h')]; rfl
      · push Not at h'
        obtain ⟨h1, h2, h3⟩ := h'
        have h1' : G w (mate u) = false := by simpa using h1
        have hf : V R2.1 x R2.2 = false := by
          by_contra h; simp only [Bool.not_eq_false] at h
          exact F6 hv (hcov u w hG h1') hG h1' h2 h3 (H.mp h)
        rw [hf]; simp

theorem fwd_main (d : ℕ) (hdeg : ∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
      rank v < rank later ∧ (G v (mate later) = true ∨ G later (mate v) = true))).card ≤ d)
    (hcov : ∀ i j, G i (mate j) = true → G j (mate i) = false →
      i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols) :
    ∃ C : Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
      PEqualNP.Represents.Represents G C ∧
      PEqualNP.NotBracket.notCount C ≤ 1 ∧
      (∀ g ∈ C.gates, g.op = .not → g.inputs.length = 1) ∧
      2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
      C.size ≤ n + 24 * (n + 1) * (d + 1) ∧
      ∀ i : Fin n,
        (∃ g ∈ C.gates, g.op = .or ∧
          (g.inputs = [i.val, n + (mate i).val] ∨
           g.inputs = [n + (mate i).val, i.val])) ∧
        (C.gates.map (fun g => g.inputs.count i.val)).sum ≤
          1 + (if i ∈ rows then 1 else 0) ∧
        (C.gates.map (fun g => g.inputs.count (n + (mate i).val))).sum ≤
          1 + (if i ∈ cols then 1 else 0) := by
  obtain ⟨eG, lG⟩ := gs0_struct n mate rank rows cols
  obtain ⟨e1, l1, a1, b1, e2, l2, a2, b2, e3, l3, a3, b3⟩ := chain_struct n G mate rank rows cols
  set R1 := r1 n G mate rank rows cols
  set R2 := r2 n G mate rank rows cols
  set R3 := r3 n G mate rank rows cols
  have eAll := eG.trans (e1.trans (e2.trans e3))
  set L := R3.1.length
  set g1 : Gate := ⟨GateOp.not, [R2.2]⟩
  set g2 : Gate := ⟨GateOp.and, [R3.2, n + n + L]⟩
  set g3 : Gate := ⟨GateOp.or, [R1.2, n + n + L + 1]⟩
  have hgs : gsF n G mate rank rows cols = R3.1 ++ [g1] ++ [g2] ++ [g3] := rfl
  have len1 := e2.len
  have len2 := e3.len
  have hokF : Ok (n + n) (gsF n G mate rank rows cols) := by
    rw [hgs]
    refine ok_snoc (ok_snoc (ok_snoc (eAll.ok (pre_ok n mate rows cols)) ?_) ?_) ?_
    · refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), by simp [g1], ?_⟩
      intro i hi; simp only [g1, List.mem_singleton] at hi; subst hi; omega
    · refine ⟨Or.inl rfl, by simp [g2], ?_⟩
      intro i hi; simp only [g2, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hi
      simp only [List.length_append, List.length_singleton]
      rcases hi with rfl | rfl <;> omega
    · refine ⟨Or.inr (Or.inl rfl), by simp [g3], ?_⟩
      intro i hi; simp only [g3, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hi
      simp only [List.length_append, List.length_singleton]
      rcases hi with rfl | rfl <;> omega
  have hlen : (gsF n G mate rank rows cols).length = L + 3 := by rw [hgs]; simp [L]
  have hnot : notCnt (gsF n G mate rank rows cols) = 1 := by
    rw [hgs, notCnt_snoc, notCnt_snoc, notCnt_snoc, eAll.nots, pre_nots,
      notCnt_one_not g1 rfl, notCnt_one_ne g2 (fun e => by cases e),
      notCnt_one_ne g3 (fun e => by cases e)]
  have hcnt : ∀ w < n + n, cntW (gsF n G mate rank rows cols) w = cntW (pre n mate rows cols) w := by
    intro w hw
    have c1 : g1.inputs.count w = 0 := List.count_eq_zero.mpr (by simp [g1]; omega)
    have c2 : g2.inputs.count w = 0 := List.count_eq_zero.mpr (by simp [g2]; omega)
    have c3 : g3.inputs.count w = 0 := List.count_eq_zero.mpr (by simp [g3]; omega)
    rw [hgs, cntW_snoc, cntW_snoc, cntW_snoc, c1, c2, c3, eAll.raw w hw]
    simp
  have hsize : (gsF n G mate rank rows cols).length ≤ n + 24 * (n + 1) * (d + 1) := by
    rw [hlen]
    have hE := Eord_card n G mate rank d hdeg
    have hA := absL_len n G mate rank d hdeg
    have h1 : (LM1 n G mate rows cols).length = (Eord n G mate).card := by
      simp [LM1]
    have h2 : (LH n G mate rank rows cols).length =
        (Eord n G mate).card + (absL n G mate rank).length := by
      simp [LH]
    have h3 : (LM2 n G mate).length = n + 1 := by simp [LM2]
    have hx1 : 24 * (n + 1) * (d + 1) = 24 * (n * d) + 24 * n + 24 * d + 24 := by ring
    have hx2 : n * (d + 1) = n * d + n := by ring
    show L + 3 ≤ _
    rw [l3, l2, l1, lG, h1, h2, h3]
    omega
  refine ⟨circ n G mate rank rows cols, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ gsF n G mate rank rows cols at hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have h := hokF j hj
    refine ⟨?_, h.2.1⟩
    rcases h.1 with h' | h' | ⟨h', -⟩ <;> rw [h'] <;> simp
  · intro j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    have := (hokF j hj).2.2 i hi
    omega
  · intro u v
    obtain ⟨w, rfl⟩ := mate.surjective v
    exact out_correct n G mate rank rows cols hcov u w
  · change notCnt (gsF n G mate rank rows cols) ≤ 1
    omega
  · intro g hg hn
    change g ∈ gsF n G mate rank rows cols at hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    rcases (hokF j hj).1 with h' | h' | ⟨-, h'⟩
    · rw [h'] at hn; cases hn
    · rw [h'] at hn; cases hn
    · exact h'
  · show 2 * n ≤ n + n + L + 2; omega
  · show n + n + L + 2 < 2 * n + (gsF n G mate rank rows cols).length; omega
  · exact hsize
  · intro i
    have hmem : pGate n mate i ∈ pre n mate rows cols := by simp [pre]
    obtain ⟨more, hm⟩ := eAll.pre
    refine ⟨⟨pGate n mate i, ?_, rfl, Or.inl rfl⟩, ?_, ?_⟩
    · show pGate n mate i ∈ gsF n G mate rank rows cols
      rw [hgs, hm]; simp [hmem]
    · change cntW (gsF n G mate rank rows cols) i.val ≤ _
      rw [hcnt _ (by omega), pre_cntL]
    · change cntW (gsF n G mate rank rows cols) (n + (mate i).val) ≤ _
      rw [hcnt _ (by omega), pre_cntR]

end assemble

theorem elem_le_sum (f : Gate → ℕ) : ∀ (l : List Gate) (a : Gate), a ∈ l → f a ≤ (l.map f).sum
  | [], _, h => absurd h (by simp)
  | c :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := elem_le_sum f l a h; simp; omega

theorem sum_two (f : Gate → ℕ) : ∀ (l : List Gate) (a b : Gate), a ∈ l → b ∈ l → a ≠ b →
    f a + f b ≤ (l.map f).sum
  | [], _, _, h, _, _ => absurd h (by simp)
  | c :: l, a, b, ha, hb, hab => by
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · have := elem_le_sum f l b hb'; simp; omega
    · have := elem_le_sum f l a ha'; simp; omega
    · have := sum_two f l a b ha' hb' hab; simp; omega

theorem bwd (n : ℕ) (G : Fin n → Fin n → Bool) (mate : Equiv.Perm (Fin n))
    (rows cols : Finset (Fin n)) (C : Circuit) (hrep : PEqualNP.Represents.Represents G C)
    (hout : n + n ≤ C.output)
    (hpair : ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧
          (g.inputs = [i.val, n + (mate i).val] ∨
           g.inputs = [n + (mate i).val, i.val])) ∧
        (C.gates.map (fun g => g.inputs.count i.val)).sum ≤
          1 + (if i ∈ rows then 1 else 0) ∧
        (C.gates.map (fun g => g.inputs.count (n + (mate i).val))).sum ≤
          1 + (if i ∈ cols then 1 else 0)) :
    ∀ i j, G i (mate j) = true → G j (mate i) = false →
      i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols := by
  intro i j hij hji
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨hi_r, hj_c, hj_r, hi_c⟩ := hc
  have hne : i ≠ j := by rintro rfl; rw [hij] at hji; exact absurd hji (by simp)
  obtain ⟨⟨gi, hgi, hgio, hgii⟩, ci1, ci2⟩ := hpair i
  obtain ⟨⟨gj, hgj, hgjo, hgji⟩, cj1, cj2⟩ := hpair j
  simp only [hi_r, hi_c, hj_r, hj_c, ↓reduceIte] at ci1 ci2 cj1 cj2
  have uniq : ∀ (r : ℕ) (g0 : Gate), g0 ∈ C.gates → r ∈ g0.inputs →
      (C.gates.map (fun g => g.inputs.count r)).sum ≤ 1 + 0 →
      ∀ g ∈ C.gates, r ∈ g.inputs → g = g0 := by
    intro r g0 hg0 hr0 hc g hg hr
    by_contra hne'
    have := sum_two (fun g => g.inputs.count r) C.gates g g0 hg hg0 hne'
    have h1 := List.count_pos_iff.mpr hr
    have h2 := List.count_pos_iff.mpr hr0
    omega
  have hii : i.val ∈ gi.inputs ∧ n + (mate i).val ∈ gi.inputs := by
    rcases hgii with h | h <;> rw [h] <;> simp
  have hjj : j.val ∈ gj.inputs ∧ n + (mate j).val ∈ gj.inputs := by
    rcases hgji with h | h <;> rw [h] <;> simp
  let bad : ℕ → Prop := fun r =>
    r = i.val ∨ r = n + (mate i).val ∨ r = j.val ∨ r = n + (mate j).val
  have hgood : ∀ g ∈ C.gates, (∀ r ∈ g.inputs, ¬ bad r) ∨ g = gi ∨ g = gj := by
    intro g hg
    by_contra hcon
    simp only [not_or, not_forall, not_not] at hcon
    obtain ⟨⟨r, hr, hbad⟩, hgi', hgj'⟩ := hcon
    rcases hbad with rfl | rfl | rfl | rfl
    · exact hgi' (uniq _ gi hgi hii.1 ci1 g hg hr)
    · exact hgi' (uniq _ gi hgi hii.2 ci2 g hg hr)
    · exact hgj' (uniq _ gj hgj hjj.1 cj1 g hg hr)
    · exact hgj' (uniq _ gj hgj hjj.2 cj2 g hg hr)
  set x1 := PEqualNP.Represents.oneEach i (mate j)
  set x2 := PEqualNP.Represents.oneEach j (mate i)
  have hl1 : x1.length = n + n := oe_len _ _
  have hl2 : x2.length = n + n := oe_len _ _
  have raw : ∀ r < n + n, ¬ bad r → x1.getD r false = x2.getD r false := by
    intro r hr hb
    by_cases hrn : r < n
    · have h1 : (⟨r, hrn⟩ : Fin n) ≠ i := fun h => hb (Or.inl (by rw [← h]))
      have h2 : (⟨r, hrn⟩ : Fin n) ≠ j := fun h => hb (Or.inr (Or.inr (Or.inl (by rw [← h]))))
      have e1 := oe_left i (mate j) ⟨r, hrn⟩
      have e2 := oe_left j (mate i) ⟨r, hrn⟩
      simp only at e1 e2
      rw [e1, e2]; simp [h1, h2]
    · have hk : r - n < n := by omega
      have h1 : (⟨r - n, hk⟩ : Fin n) ≠ mate j := fun h =>
        hb (Or.inr (Or.inr (Or.inr (by rw [← h]; simp; omega))))
      have h2 : (⟨r - n, hk⟩ : Fin n) ≠ mate i := fun h =>
        hb (Or.inr (Or.inl (by rw [← h]; simp; omega)))
      have e1 := oe_right i (mate j) ⟨r - n, hk⟩
      have e2 := oe_right j (mate i) ⟨r - n, hk⟩
      simp only at e1 e2
      rw [show r = n + (r - n) by omega, e1, e2]; simp [h1, h2]
  have agree : ∀ gs : List Gate, (∀ g ∈ gs, (∀ r ∈ g.inputs, ¬ bad r) ∨ g = gi ∨ g = gj) →
      ∀ w, n + n ≤ w → V gs x1 w = V gs x2 w := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ w hw
      rw [V_oob [] x1 w (by rw [hl1]; simp; omega), V_oob [] x2 w (by rw [hl2]; simp; omega)]
    | append_singleton gs g ih =>
      intro hall w hw
      have ih' := ih (fun g' hg' => hall g' (List.mem_append_left _ hg'))
      rcases lt_trichotomy w (n + n + gs.length) with hlt | heq | hgt
      · rw [V_prefix gs [g] x1 (by omega), V_prefix gs [g] x2 (by omega)]; exact ih' w hw
      · subst heq
        rw [snoc_val gs g x1 _ (by rw [hl1]), snoc_val gs g x2 _ (by rw [hl2])]
        have hvals : ∀ r, ¬ bad r → V gs x1 r = V gs x2 r := by
          intro r hb
          by_cases hr : r < n + n
          · rw [V_raw gs x1 (by omega), V_raw gs x2 (by omega)]; exact raw r hr hb
          · exact ih' r (by omega)
        have v1i : V gs x1 i.val = true := by
          rw [V_raw gs x1 (by omega)]; rw [oe_left]; simp
        have v2i : V gs x2 (n + (mate i).val) = true := by
          rw [V_raw gs x2 (by omega)]; rw [oe_right]; simp
        have v1j : V gs x1 (n + (mate j).val) = true := by
          rw [V_raw gs x1 (by omega)]; rw [oe_right]; simp
        have v2j : V gs x2 j.val = true := by
          rw [V_raw gs x2 (by omega)]; rw [oe_left]; simp
        rcases hall g (List.mem_append_right _ (List.mem_singleton_self _)) with h | rfl | rfl
        · congr 1
          apply List.map_congr_left
          intro r hr; exact hvals r (h r hr)
        · rw [hgio]
          rcases hgii with h | h <;> rw [h] <;> simp [GateOp.eval, v1i, v2i]
        · rw [hgjo]
          rcases hgji with h | h <;> rw [h] <;> simp [GateOp.eval, v1j, v2j]
      · rw [V_oob _ x1 w (by rw [hl1]; simp; omega), V_oob _ x2 w (by rw [hl2]; simp; omega)]
  have h := agree C.gates hgood C.output hout
  have r1 := hrep i (mate j)
  have r2 := hrep j (mate i)
  rw [eval_eq] at r1 r2
  rw [h, r2, hji] at r1
  exact absurd r1 (by simp [hij])

end PEqualNP.Outside.L_meta_25540_aux

theorem PEqualNP.Outside.L_meta_25540 : (∀ (n d : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
    (rows cols : Finset (Fin n)),
  let A := fun (i j : Fin n) => G i (mate j)
  let cover := ∀ i j, A i j = true → A j i = false →
    i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols
  (∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
    rank v < rank later ∧ (A v later = true ∨ A later v = true))).card ≤ d) →
  (cover ↔ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
    PEqualNP.Represents.Represents G C ∧
    PEqualNP.NotBracket.notCount C ≤ 1 ∧
    (∀ g ∈ C.gates, g.op = .not → g.inputs.length = 1) ∧
    2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
    C.size ≤ n + 24 * (n + 1) * (d + 1) ∧
    ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧
        (g.inputs = [i.val, n + (mate i).val] ∨
         g.inputs = [n + (mate i).val, i.val])) ∧
      (C.gates.map (fun g => g.inputs.count i.val)).sum ≤
        1 + (if i ∈ rows then 1 else 0) ∧
      (C.gates.map (fun g => g.inputs.count (n + (mate i).val))).sum ≤
        1 + (if i ∈ cols then 1 else 0))) := by
  intro n d G mate rank rows cols A cover hdeg
  constructor
  · intro hcov
    exact PEqualNP.Outside.L_meta_25540_aux.fwd_main n G mate rank rows cols d hdeg hcov
  · rintro ⟨C, -, -, hrep, -, -, hout, -, -, hpair⟩
    exact PEqualNP.Outside.L_meta_25540_aux.bwd n G mate rows cols C hrep (by omega) hpair
