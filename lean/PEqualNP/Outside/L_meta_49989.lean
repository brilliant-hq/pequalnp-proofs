import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

/-!
Three ordered outputs 12, 14, 26 need more than 5 gates at a two-NOT limit.

Each wire is followed on the five threshold inputs at once as a five-bit number (bit `t` is the
value on input number `t`). `bad k st nots` searches every way to extend the wire list `st` by at
most `k` gates with at most `2 - nots` further NOT gates; `sound` shows that a circuit with the
three outputs makes it `true`, and the kernel evaluates it to `false`.
-/

namespace PEqualNP.Outside.L_meta_49989

open PEqualNP.CircuitLowerBounds

def colF (op : GateOp) (l : List ℕ) (st : List ℕ) : ℕ :=
  match op, l with
  | GateOp.and, [] => 31
  | GateOp.and, [i] => st.getD i 0
  | GateOp.and, [i, j] => st.getD i 0 &&& st.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => st.getD i 0
  | GateOp.or, [i, j] => st.getD i 0 ||| st.getD j 0
  | GateOp.not, [] => 31
  | GateOp.not, i :: _ => 31 ^^^ st.getD i 0
  | _, _ => 0

theorem colF_spec (op : GateOp) (l : List ℕ) (st : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : l.length ≤ 2)
    (t : ℕ) (ht : t < 5) :
    (colF op l st).testBit t = op.eval (l.map fun i => (st.getD i 0).testBit t) := by
  have h31 : (31 : ℕ).testBit t = true := by interval_cases t <;> rfl
  rcases hop with rfl | rfl | rfl
  · match l, hl with
    | [], _ => simp [colF, GateOp.eval, h31]
    | [i], _ => simp [colF, GateOp.eval]
    | [i, j], _ => simp [colF, GateOp.eval, Nat.testBit_land]
    | _ :: _ :: _ :: _, hl => simp at hl
  · match l, hl with
    | [], _ => simp [colF, GateOp.eval]
    | [i], _ => simp [colF, GateOp.eval]
    | [i, j], _ => simp [colF, GateOp.eval, Nat.testBit_lor]
    | _ :: _ :: _ :: _, hl => simp at hl
  · match l, hl with
    | [], _ => simp [colF, GateOp.eval, h31]
    | i :: _, _ => simp [colF, GateOp.eval, Nat.testBit_xor, h31]

def colOf (g : Gate) (st : List ℕ) : ℕ := colF g.op g.inputs st

def rows (st : List ℕ) (t : ℕ) : List Bool := st.map fun c => c.testBit t

theorem getD_rows (st : List ℕ) (t i : ℕ) :
    (rows st t).getD i false = (st.getD i 0).testBit t := by
  unfold rows
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[i]? <;> simp

def run (gs : List Gate) (st : List ℕ) : List ℕ :=
  gs.foldl (fun s g => s ++ [colOf g s]) st

theorem run_length (gs : List Gate) : ∀ st : List ℕ, (run gs st).length = st.length + gs.length := by
  induction gs with
  | nil => intro st; rfl
  | cons g gs ih =>
    intro st
    show (run gs (st ++ [colOf g st])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem wires_rows (t : ℕ) (ht : t < 5) (gs : List Gate)
    (hfan : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∀ st : List ℕ,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (rows st t)
      = rows (run gs st) t := by
  induction gs with
  | nil => intro st; rfl
  | cons g gs ih =>
    intro st
    have hg := hfan g (by simp)
    have step : rows st t ++ [g.op.eval (g.inputs.map fun i => (rows st t).getD i false)]
        = rows (st ++ [colOf g st]) t := by
      have e : (fun i => (rows st t).getD i false) = fun i => (st.getD i 0).testBit t := by
        funext i; exact getD_rows st t i
      rw [e]
      unfold rows colOf
      rw [List.map_append, List.map_cons, List.map_nil, colF_spec _ _ _ hg.1 hg.2 t ht]
    show gs.foldl _ (rows st t ++ [g.op.eval (g.inputs.map fun i => (rows st t).getD i false)])
      = rows (run gs (st ++ [colOf g st])) t
    rw [step]
    exact ih (fun g' hg' => hfan g' (by simp [hg'])) _

def hasT (st : List ℕ) (tg : ℕ) : Bool := st.any fun c => c % 32 == tg

def miss (st : List ℕ) : ℕ :=
  (if hasT st 12 then 0 else 1) + (if hasT st 14 then 0 else 1) + (if hasT st 26 then 0 else 1)

theorem miss_append (st : List ℕ) (c : ℕ) : miss st ≤ miss (st ++ [c]) + 1 := by
  unfold miss hasT
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  generalize c % 32 = m
  generalize (st.any fun c => c % 32 == 12) = a
  generalize (st.any fun c => c % 32 == 14) = b
  generalize (st.any fun c => c % 32 == 26) = d
  by_cases e1 : m = 12 <;> by_cases e2 : m = 14 <;> by_cases e3 : m = 26 <;>
    cases a <;> cases b <;> cases d <;> simp [e1, e2, e3]

def ins (n : ℕ) : List (List ℕ) :=
  [] :: (((List.range n).map fun i => [i]) ++
    (List.range n).flatMap fun i => (List.range n).map fun j => [i, j])

theorem mem_ins (n : ℕ) (l : List ℕ) (hl : l.length ≤ 2) (hb : ∀ i ∈ l, i < n) : l ∈ ins n := by
  unfold ins
  match l, hl, hb with
  | [], _, _ => simp
  | [a], _, hb =>
    have ha := hb a (by simp)
    simp [ha]
  | [a, b], _, hb =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    simp [ha, hb']
  | _ :: _ :: _ :: _, hl, _ => simp at hl

def isN : GateOp → ℕ
  | GateOp.not => 1
  | _ => 0

theorem isN_filter (gs : List Gate) [inst : ∀ g : Gate, Decidable (g.op = GateOp.not)] :
    (gs.filter fun g => @decide (g.op = GateOp.not) (inst g)).length = (gs.map fun g => isN g.op).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    by_cases hn : g.op = GateOp.not
    · simp [hn, isN]; omega
    · have : isN g.op = 0 := by
        cases hop : g.op <;> simp_all [isN]
      simp [hn, this]

theorem isN_le (op : GateOp) : isN op ≤ 1 := by
  cases op <;> simp [isN]

def dd : List ℕ → List ℕ
  | [] => []
  | a :: l => if l.contains a then dd l else a :: dd l

theorem mem_dd (a : ℕ) : ∀ l : List ℕ, a ∈ l → a ∈ dd l := by
  intro l
  induction l with
  | nil => intro h; exact h
  | cons b l ih =>
    intro h
    unfold dd
    by_cases hc : l.contains b = true
    · rw [if_pos hc]
      rcases List.mem_cons.mp h with rfl | h
      · exact ih (by simpa using hc)
      · exact ih h
    · rw [if_neg hc]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

def cands (st : List ℕ) : List ℕ :=
  dd ([GateOp.and, GateOp.or, GateOp.not].flatMap fun op =>
    (ins st.length).map fun l => 2 * colF op l st + isN op)

def bad : ℕ → List ℕ → ℕ → Bool
  | 0, st, _ => miss st == 0
  | k + 1, st, nots =>
    miss st == 0 || (decide (miss st ≤ k + 1) &&
      (cands st).any fun cn => decide (nots + cn % 2 ≤ 2) && bad k (st ++ [cn / 2]) (nots + cn % 2))

theorem bad_miss (k : ℕ) (st : List ℕ) (nots : ℕ) (h : bad k st nots = true) : miss st ≤ k := by
  cases k with
  | zero =>
    simp only [bad, beq_iff_eq] at h
    omega
  | succ k =>
    simp only [bad, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩ <;> omega

theorem sound : ∀ (gs : List Gate) (k : ℕ) (st : List ℕ) (nots : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < st.length + j) →
    nots + (gs.map fun g => isN g.op).sum ≤ 2 →
    gs.length ≤ k → miss (run gs st) = 0 → bad k st nots = true := by
  intro gs
  induction gs with
  | nil =>
    intro k st nots _ _ _ _ hm
    have hm' : miss st = 0 := hm
    cases k <;> simp [bad, hm']
  | cons g gs ih =>
    intro k st nots hfan hrb hnots hlen hm
    cases k with
    | zero => simp at hlen
    | succ k =>
      have hg := hfan g (by simp)
      have hgin : ∀ i ∈ g.inputs, i < st.length := by
        intro i hi
        have := hrb 0 (by simp) i (by simpa using hi)
        omega
      simp only [List.map_cons, List.sum_cons] at hnots
      have hb : bad k (st ++ [colOf g st]) (nots + isN g.op) = true := by
        apply ih
        · intro g' hg'
          exact hfan g' (by simp [hg'])
        · intro j hj i hi
          have := hrb (j + 1) (by simpa using hj) i (by simpa using hi)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · omega
        · simp only [List.length_cons] at hlen
          omega
        · exact hm
      have hmk := bad_miss _ _ _ hb
      have hma := miss_append st (colOf g st)
      have hmem : 2 * colOf g st + isN g.op ∈ cands st := by
        unfold cands
        apply mem_dd
        rw [List.mem_flatMap]
        refine ⟨g.op, ?_, ?_⟩
        · rcases hg.1 with h | h | h <;> simp [h]
        · rw [List.mem_map]
          exact ⟨g.inputs, mem_ins _ _ hg.2 hgin, rfl⟩
      have hle := isN_le g.op
      have e1 : (2 * colOf g st + isN g.op) / 2 = colOf g st := by omega
      have e2 : (2 * colOf g st + isN g.op) % 2 = isN g.op := by omega
      simp only [bad, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.any_eq_true]
      right
      refine ⟨by omega, _, hmem, ?_, ?_⟩
      · rw [e2]; omega
      · rw [e1, e2]; exact hb

theorem mod_of_bits (c tg : ℕ) (htg : tg < 32) (h : ∀ t : Fin 5, c.testBit t.val = tg.testBit t.val) :
    c % 32 = tg := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (c % 2 ^ 5).testBit i = tg.testBit i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 5
  · simp [hi, h ⟨i, hi⟩]
  · have h2 : tg < 2 ^ i :=
      lt_of_lt_of_le htg (by simpa using Nat.pow_le_pow_right (n := 2) (by omega) (Nat.le_of_not_lt hi))
    simp [hi, Nat.testBit_lt_two_pow h2]

def start : List ℕ := [30, 28, 24, 16, 0, 31]

theorem start_rows : ∀ t : Fin 5,
    (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true] = rows start t.val := by
  decide

theorem search : bad 5 start 0 = false := by decide +kernel

end PEqualNP.Outside.L_meta_49989

open PEqualNP.Outside.L_meta_49989 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_49989 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, hrb, hnc, hsz, hall⟩
  have hfan' : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hfan g hg
    refine ⟨?_, this.2⟩
    simpa [Set.mem_insert_iff] using this.1
  have hw : ∀ t : Fin 5,
      D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])
        = rows (run D.gates start) t.val := by
    intro t
    rw [start_rows t]
    exact wires_rows t.val t.isLt D.gates hfan' start
  have hlenF : (run D.gates start).length = 6 + D.size := by
    rw [run_length]; rfl
  have hcol : ∀ (o : Fin (6 + D.size)) (tg : ℕ), tg < 32 →
      (∀ t : Fin 5, (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD
        o.val false = tg.testBit t.val) → hasT (run D.gates start) tg = true := by
    intro o tg htg h
    have hm : ((run D.gates start).getD o.val 0) % 32 = tg := by
      apply mod_of_bits _ _ htg
      intro t
      rw [← getD_rows, ← hw t]
      exact h t
    have ho : o.val < (run D.gates start).length := by rw [hlenF]; exact o.isLt
    unfold hasT
    rw [List.any_eq_true]
    refine ⟨(run D.gates start)[o.val], List.getElem_mem ho, ?_⟩
    rw [List.getD_eq_getElem _ _ ho] at hm
    simp [hm]
  have h12 := hcol p 12 (by omega) (fun t => (hall t).1)
  have h14 := hcol q 14 (by omega) (fun t => (hall t).2.1)
  have h26 := hcol r 26 (by omega) (fun t => (hall t).2.2)
  have hmiss : miss (run D.gates start) = 0 := by
    unfold miss
    rw [h12, h14, h26]
    rfl
  have hb : bad 5 start 0 = true := by
    apply sound D.gates 5 start 0
    · exact hfan'
    · intro j hj i hi
      have := hrb j hj i (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hj]
        exact hi)
      simpa [start] using this
    · unfold PEqualNP.NotBracket.notCount at hnc
      rw [isN_filter] at hnc
      omega
    · exact hsz
    · exact hmiss
  rw [search] at hb
  exact Bool.false_ne_true hb
