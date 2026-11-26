import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18838

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def shiftGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + k)⟩

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_lt (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_ge (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_append_add (l₁ l₂ : List α) (d : α) (i : ℕ) :
    (l₁ ++ l₂).getD (i + l₁.length) d = l₂.getD i d := by
  rw [getD_append_ge _ _ _ (by omega), Nat.add_sub_cancel]

lemma any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma foldl_gateStep_shift (k : ℕ) (gs : List Gate) (p y : List Bool) (hp : p.length = k) :
    (gs.map (shiftGate k)).foldl gateStep (p ++ y) = p ++ gs.foldl gateStep y := by
  induction gs generalizing y with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, gateStep, shiftGate, List.map_map]
    have hcomp : (fun x => (p ++ y).getD (x + k) false) = (fun i => y.getD i false) := by
      funext i
      rw [← hp, getD_append_add]
    change (List.map (shiftGate k) gs).foldl gateStep
        ((p ++ y) ++ [g.op.eval (g.inputs.map (fun x => (p ++ y).getD (x + k) false))]) = _
    rw [hcomp, List.append_assoc]
    exact ih (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)])

lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, gateStep]
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma foldl_gateStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, gateStep]
    rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) (by simp; omega)]
    exact getD_append_lt w _ false hi

def orFoldGates (cur nextIdx : ℕ) (ws : List ℕ) : List Gate × ℕ :=
  match ws with
  | [] => ([], cur)
  | w :: rest =>
    let res := orFoldGates nextIdx (nextIdx + 1) rest
    (⟨GateOp.or, [cur, w]⟩ :: res.1, res.2)

lemma orFoldGates_length (cur nextIdx : ℕ) (ws : List ℕ) :
    (orFoldGates cur nextIdx ws).1.length = ws.length := by
  induction ws generalizing cur nextIdx with
  | nil => rfl
  | cons w rest ih => simp [orFoldGates, ih]

lemma orFoldGates_monotone2 (cur nextIdx : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orFoldGates cur nextIdx ws).1,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing cur nextIdx with
  | nil => simp [orFoldGates]
  | cons w rest ih =>
    intro g hg
    simp only [orFoldGates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨Or.inr rfl, by simp⟩
    · exact ih nextIdx (nextIdx + 1) g hg

lemma orFoldGates_eval (cur nextIdx : ℕ) (ws : List ℕ) (base : List Bool)
    (hbase : base.length = nextIdx) (hcur : cur < nextIdx)
    (hws : ∀ w ∈ ws, w < nextIdx) :
    ((orFoldGates cur nextIdx ws).1.foldl gateStep base).getD (orFoldGates cur nextIdx ws).2 false =
      (base.getD cur false || ws.any fun w => base.getD w false) ∧
    (orFoldGates cur nextIdx ws).2 < nextIdx + ws.length ∧
    ((orFoldGates cur nextIdx ws).1.foldl gateStep base).length = nextIdx + ws.length := by
  induction ws generalizing cur nextIdx base with
  | nil =>
    simp only [orFoldGates, List.foldl_nil, List.any_nil, Bool.or_false, List.length_nil, add_zero]
    exact ⟨trivial, hcur, hbase⟩
  | cons w rest ih =>
    simp only [orFoldGates, List.foldl_cons, gateStep, List.any_cons]
    let v := base.getD cur false || base.getD w false
    have hv : GateOp.eval GateOp.or ([cur, w].map fun i => base.getD i false) = v := by
      simp [GateOp.eval, v]
    rw [hv]
    let base' := base ++ [v]
    have hbase' : base'.length = nextIdx + 1 := by simp [base', hbase]
    have hrest : ∀ u ∈ rest, u < nextIdx + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    obtain ⟨heval, hlt, hlen⟩ := ih nextIdx (nextIdx + 1) base' hbase' (by omega) hrest
    refine ⟨?_, ?_, ?_⟩
    · rw [heval]
      have hget_next : base'.getD nextIdx false = v := by
        simp [base', hbase]
      have hget_rest : (rest.any fun u => base'.getD u false) = (rest.any fun u => base.getD u false) := by
        apply any_congr_mem
        intro u hu
        have hu' : u < base.length := by rw [hbase]; exact hws u (by simp [hu])
        exact getD_append_lt base [v] false hu'
      rw [hget_next, hget_rest, Bool.or_assoc]
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; exact hlen.trans (by omega)

def stage1X (n : ℕ) : List Gate :=
  (List.range n).map fun i => ⟨GateOp.or, [i, 3 * n + i]⟩

def stage1Y (n : ℕ) : List Gate :=
  (List.range n).map fun i => ⟨GateOp.or, [2 * n + i, n + i]⟩

lemma stage1X_length (n : ℕ) : (stage1X n).length = n := by
  simp [stage1X]

lemma stage1Y_length (n : ℕ) : (stage1Y n).length = n := by
  simp [stage1Y]

lemma stage1X_monotone2 (n : ℕ) :
    ∀ g ∈ stage1X n, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [stage1X, List.mem_map] at hg
  rcases hg with ⟨i, _, rfl⟩
  exact ⟨Or.inr rfl, by simp⟩

lemma stage1Y_monotone2 (n : ℕ) :
    ∀ g ∈ stage1Y n, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [stage1Y, List.mem_map] at hg
  rcases hg with ⟨i, _, rfl⟩
  exact ⟨Or.inr rfl, by simp⟩

lemma stage1X_eval (n : ℕ) (inp : List Bool) (hinp : inp.length = 4 * n) :
    (stage1X n).foldl gateStep inp =
      inp ++ List.ofFn (fun i : Fin n => inp.getD i.val false || inp.getD (3 * n + i.val) false) := by
  have haux : ∀ k, k ≤ n →
      ((List.range k).map fun i => (⟨GateOp.or, [i, 3 * n + i]⟩ : Gate)).foldl gateStep inp =
        inp ++ (List.range k).map fun i => inp.getD i false || inp.getD (3 * n + i) false := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, gateStep, List.map_cons, List.map_nil, GateOp.eval,
        List.any_cons, List.any_nil, Bool.or_false, id_eq]
      have h1 : k < inp.length := by omega
      have h2 : 3 * n + k < inp.length := by omega
      rw [getD_append_lt inp _ false h1, getD_append_lt inp _ false h2,
        List.append_assoc, List.map_append, List.map_singleton]
  rw [stage1X, haux n (le_refl n)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

lemma stage1Y_eval (n : ℕ) (inp x : List Bool) (hinp : inp.length = 4 * n) (hx : x.length = n) :
    (stage1Y n).foldl gateStep (inp ++ x) =
      (inp ++ x) ++ List.ofFn (fun i : Fin n => inp.getD (2 * n + i.val) false || inp.getD (n + i.val) false) := by
  have haux : ∀ k, k ≤ n →
      ((List.range k).map fun i => (⟨GateOp.or, [2 * n + i, n + i]⟩ : Gate)).foldl gateStep (inp ++ x) =
        (inp ++ x) ++ (List.range k).map fun i => inp.getD (2 * n + i) false || inp.getD (n + i) false := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, gateStep, List.map_cons, List.map_nil, GateOp.eval,
        List.any_cons, List.any_nil, Bool.or_false, id_eq]
      have h1 : 2 * n + k < (inp ++ x).length := by simp [hinp, hx]; omega
      have h2 : n + k < (inp ++ x).length := by simp [hinp, hx]; omega
      rw [getD_append_lt (inp ++ x) _ false h1, getD_append_lt (inp ++ x) _ false h2]
      have h1' : 2 * n + k < inp.length := by omega
      have h2' : n + k < inp.length := by omega
      rw [getD_append_lt inp x false h1', getD_append_lt inp x false h2',
        List.append_assoc, List.map_append, List.map_singleton]
  rw [stage1Y, haux n (le_refl n)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

lemma repSizeAtMost_double_transpose (n : ℕ) (hn : 1 ≤ n) (A : Fin n → Fin n → Bool) (s : ℕ)
    (hA : RepSizeAtMost A s) :
    RepSizeAtMost
      (fun u v : Fin (2 * n) =>
        if h : u.val < n ∧ v.val < n then A ⟨u.val, h.1⟩ ⟨v.val, h.2⟩
        else if h' : n ≤ u.val ∧ n ≤ v.val then A ⟨v.val - n, by omega⟩ ⟨u.val - n, by omega⟩
        else false)
      (s + 4 * n) := by
  rcases hA with ⟨C, hCm, hCs, hCrep⟩
  by_cases hout : 2 * n + C.size ≤ C.output
  · refine ⟨⟨[], 4 * n⟩, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · simp [Circuit.size]
    · intro u v
      have hAfalse : ∀ a b : Fin n, A a b = false := by
        intro a b
        have := hCrep a b
        simp only [Circuit.eval, Circuit.wires] at this
        have hlen : (C.gates.foldl gateStep (oneEach a b)).length = 2 * n + C.size := by
          rw [foldl_gateStep_length]
          simp only [oneEach, List.length_append, List.length_ofFn, Circuit.size]
          omega
        have hout' : (C.gates.foldl gateStep (oneEach a b)).length ≤ C.output := by omega
        have hget : (C.gates.foldl gateStep (oneEach a b)).getD C.output false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout']
        change (C.gates.foldl gateStep (oneEach a b)).getD C.output false = A a b at this
        rw [hget] at this
        exact this.symm
      have hC' : (⟨[], 4 * n⟩ : Circuit).eval (oneEach u v) = false := by
        have hlen : (oneEach u v).length = 4 * n := by
          simp [oneEach, List.length_append, List.length_ofFn]; omega
        simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (oneEach u v).length ≤ 4 * n)]
      rw [hC']
      by_cases h1 : u.val < n ∧ v.val < n
      · simp [h1, hAfalse]
      · by_cases h2 : n ≤ u.val ∧ n ≤ v.val
        · simp [h1, h2, hAfalse]
        · simp [h1, h2]
  · have hout : C.output < 2 * n + C.size := Nat.lt_of_not_le hout
    let xRange := (List.range (n - 1)).map fun i => 4 * n + (i + 1)
    let resX := orFoldGates (4 * n) (6 * n + C.size) xRange
    let wX := resX.2
    let nextAfterX := 6 * n + C.size + (n - 1)
    let yRange := (List.range (n - 1)).map fun i => 5 * n + (i + 1)
    let resY := orFoldGates (5 * n) nextAfterX yRange
    let wY := resY.2
    let wXY := nextAfterX + (n - 1)
    let wOut := wXY + 1
    let C' : Circuit :=
      { gates := stage1X n ++ stage1Y n ++ C.gates.map (shiftGate (4 * n)) ++
          resX.1 ++ resY.1 ++ [⟨GateOp.and, [wX, wY]⟩, ⟨GateOp.and, [4 * n + C.output, wXY]⟩]
        output := wOut }
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ((((hg | hg) | ⟨g0, hg0, rfl⟩) | hg) | hg) | (rfl | rfl)
      · exact stage1X_monotone2 n g hg
      · exact stage1Y_monotone2 n g hg
      · simpa [shiftGate] using hCm g0 hg0
      · exact orFoldGates_monotone2 (4 * n) (6 * n + C.size) xRange g hg
      · exact orFoldGates_monotone2 (5 * n) nextAfterX yRange g hg
      · exact ⟨Or.inl rfl, by simp⟩
      · exact ⟨Or.inl rfl, by simp⟩
    · simp only [Circuit.size, C', List.length_append, stage1X_length, stage1Y_length,
        List.length_map, List.length_cons, List.length_nil]
      have hxlen : xRange.length = n - 1 := by simp [xRange]
      have hylen : yRange.length = n - 1 := by simp [yRange]
      rw [orFoldGates_length, orFoldGates_length, hxlen, hylen]
      simp only [Circuit.size] at hCs
      omega
    · intro u v
      let inp := oneEach u v
      have hinp : inp.length = 4 * n := by
        simp [inp, oneEach, List.length_append, List.length_ofFn]; omega
      let x := List.ofFn (fun i : Fin n => inp.getD i.val false || inp.getD (3 * n + i.val) false)
      let y := List.ofFn (fun i : Fin n => inp.getD (2 * n + i.val) false || inp.getD (n + i.val) false)
      have hxlen : x.length = n := by simp [x]
      have hylen : y.length = n := by simp [y]
      have hS1 : (stage1X n ++ stage1Y n).foldl gateStep inp = inp ++ (x ++ y) := by
        rw [List.foldl_append, stage1X_eval n inp hinp, stage1Y_eval n inp x hinp hxlen, List.append_assoc]
      have hS2 : (stage1X n ++ stage1Y n ++ C.gates.map (shiftGate (4 * n))).foldl gateStep inp =
          inp ++ C.gates.foldl gateStep (x ++ y) := by
        rw [List.foldl_append, hS1]
        exact foldl_gateStep_shift (4 * n) C.gates inp (x ++ y) hinp
      let w2 := inp ++ C.gates.foldl gateStep (x ++ y)
      have hw2_len : w2.length = 6 * n + C.size := by
        have hlen1 := foldl_gateStep_length C.gates (x ++ y)
        simp only [List.length_append, hxlen, hylen] at hlen1
        simp only [w2, List.length_append, hinp, hlen1, Circuit.size]
        omega
      have hxRange_lt : ∀ w ∈ xRange, w < 6 * n + C.size := by
        intro w hw
        simp only [xRange, List.mem_map, List.mem_range] at hw
        rcases hw with ⟨i, hi, rfl⟩
        omega
      obtain ⟨hX_eval, hX_lt, hX_len⟩ :=
        orFoldGates_eval (4 * n) (6 * n + C.size) xRange w2 hw2_len (by omega) hxRange_lt
      let w3 := resX.1.foldl gateStep w2
      have hxlen_r : xRange.length = n - 1 := by simp [xRange]
      have hX_lt' : wX < nextAfterX := by
        change resX.2 < nextAfterX
        dsimp only [nextAfterX]
        rw [← hxlen_r]
        exact hX_lt
      have hX_len' : w3.length = nextAfterX := by
        change (resX.1.foldl gateStep w2).length = nextAfterX
        rw [hX_len, hxlen_r]
      have hyRange_lt : ∀ w ∈ yRange, w < nextAfterX := by
        intro w hw
        simp only [yRange, List.mem_map, List.mem_range] at hw
        rcases hw with ⟨i, hi, rfl⟩
        simp only [nextAfterX]; omega
      obtain ⟨hY_eval, hY_lt, hY_len⟩ :=
        orFoldGates_eval (5 * n) nextAfterX yRange w3 hX_len' (by simp [nextAfterX]; omega) hyRange_lt
      let w4 := resY.1.foldl gateStep w3
      have hylen_r : yRange.length = n - 1 := by simp [yRange]
      have hY_lt' : wY < wXY := by
        change resY.2 < wXY
        dsimp only [wXY]
        rw [← hylen_r]
        exact hY_lt
      have hY_len' : w4.length = wXY := by
        change (resY.1.foldl gateStep w3).length = wXY
        rw [hY_len, hylen_r]
      have hget_C : w4.getD (4 * n + C.output) false = C.eval (x ++ y) := by
        have hlt2 : 4 * n + C.output < w2.length := by omega
        have hlt3 : 4 * n + C.output < w3.length := by
          rw [hX_len']; simp only [nextAfterX]; omega
        rw [foldl_gateStep_getD_lt resY.1 w3 (4 * n + C.output) hlt3]
        rw [foldl_gateStep_getD_lt resX.1 w2 (4 * n + C.output) hlt2]
        simp only [w2]
        rw [getD_append_ge _ _ _ (by omega), hinp]
        have : 4 * n + C.output - 4 * n = C.output := by omega
        rw [this]
        rfl
      have hget_wX : w4.getD wX false = w3.getD wX false := by
        apply foldl_gateStep_getD_lt
        rw [hX_len']
        exact hX_lt'
      have hget_wY : w4.getD wY false =
          (w3.getD (5 * n) false || yRange.any fun w => w3.getD w false) := hY_eval
      have hw3_5n : w3.getD (5 * n) false = w2.getD (5 * n) false :=
        foldl_gateStep_getD_lt resX.1 w2 (5 * n) (by omega)
      have hw3_yRange : (yRange.any fun w => w3.getD w false) = (yRange.any fun w => w2.getD w false) := by
        apply any_congr_mem
        intro w hw
        have : w < 6 * n + C.size := by
          simp only [yRange, List.mem_map, List.mem_range] at hw
          rcases hw with ⟨i, hi, rfl⟩; omega
        exact foldl_gateStep_getD_lt resX.1 w2 w (by omega)
      have hC'_eval : C'.eval inp = (C.eval (x ++ y) && (w4.getD wX false && w4.getD wY false)) := by
        change (C'.gates.foldl gateStep inp).getD wOut false = _
        dsimp only [C']
        rw [List.foldl_append, List.foldl_append, List.foldl_append, hS2]
        change (([⟨GateOp.and, [wX, wY]⟩, ⟨GateOp.and, [4 * n + C.output, wXY]⟩] : List Gate).foldl
          gateStep w4).getD wOut false = _
        simp only [List.foldl_cons, List.foldl_nil, gateStep, List.map_cons, List.map_nil, GateOp.eval,
          List.all_cons, List.all_nil, Bool.and_true, id_eq]
        have hlt_C : 4 * n + C.output < w4.length := by
          rw [hY_len']; simp only [wXY, nextAfterX]; omega
        have hget_C' : (w4 ++ [w4.getD wX false && w4.getD wY false]).getD (4 * n + C.output) false =
            w4.getD (4 * n + C.output) false := getD_append_lt w4 _ false hlt_C
        have hget_XY : (w4 ++ [w4.getD wX false && w4.getD wY false]).getD wXY false =
            (w4.getD wX false && w4.getD wY false) := by
          rw [getD_append_ge w4 _ false (by rw [hY_len']), hY_len', Nat.sub_self]
          rfl
        have hget_out : ((w4 ++ [w4.getD wX false && w4.getD wY false]) ++
            [(w4 ++ [w4.getD wX false && w4.getD wY false]).getD (4 * n + C.output) false &&
              (w4 ++ [w4.getD wX false && w4.getD wY false]).getD wXY false]).getD wOut false =
            ((w4 ++ [w4.getD wX false && w4.getD wY false]).getD (4 * n + C.output) false &&
              (w4 ++ [w4.getD wX false && w4.getD wY false]).getD wXY false) := by
          have hlen_out : (w4 ++ [w4.getD wX false && w4.getD wY false]).length = wOut := by
            simp [hY_len', wOut]
          rw [getD_append_ge _ _ false (by omega), hlen_out, Nat.sub_self]
          rfl
        rw [hget_out, hget_C', hget_XY, hget_C]
      rw [hC'_eval]
      have hx_get : ∀ i : Fin n, w2.getD (4 * n + i.val) false = x.getD i.val false := by
        intro i
        simp only [w2]
        rw [getD_append_ge _ _ false (by omega), hinp, Nat.add_sub_cancel_left]
        rw [foldl_gateStep_getD_lt C.gates (x ++ y) i.val (by simp [hxlen, hylen]; omega)]
        exact getD_append_lt x y false (by omega)
      have hy_get : ∀ i : Fin n, w2.getD (5 * n + i.val) false = y.getD i.val false := by
        intro i
        simp only [w2]
        rw [getD_append_ge _ _ false (by omega), hinp]
        have hsub : 5 * n + i.val - 4 * n = n + i.val := by omega
        rw [hsub]
        rw [foldl_gateStep_getD_lt C.gates (x ++ y) (n + i.val) (by simp [hxlen, hylen])]
        rw [getD_append_ge x y false (by omega), hxlen, Nat.add_sub_cancel_left]
      have hX_iff : w4.getD wX false = true ↔ ∃ i : Fin n, x.getD i.val false = true := by
        rw [hget_wX, hX_eval, Bool.or_eq_true]
        constructor
        · rintro (h | h)
          · refine ⟨⟨0, by omega⟩, ?_⟩
            have h0 := hx_get ⟨0, by omega⟩; simp only [add_zero] at h0; rw [← h0]; exact h
          · simp only [List.any_eq_true, xRange, List.mem_map, List.mem_range] at h
            rcases h with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
            refine ⟨⟨i + 1, by omega⟩, ?_⟩
            rw [← hx_get ⟨i + 1, by omega⟩]; exact htrue
        · rintro ⟨⟨i, hi⟩, htrue⟩
          rcases i with _ | i
          · left; have h0 := hx_get ⟨0, hi⟩; simp only [add_zero] at h0; rw [h0]; exact htrue
          · right
            simp only [List.any_eq_true, xRange, List.mem_map, List.mem_range]
            refine ⟨4 * n + (i + 1), ⟨i, by omega, rfl⟩, ?_⟩
            rw [hx_get ⟨i + 1, hi⟩]; exact htrue
      have hY_iff : w4.getD wY false = true ↔ ∃ i : Fin n, y.getD i.val false = true := by
        rw [hget_wY, hw3_5n, hw3_yRange, Bool.or_eq_true]
        constructor
        · rintro (h | h)
          · refine ⟨⟨0, by omega⟩, ?_⟩
            have h0 := hy_get ⟨0, by omega⟩; simp only [add_zero] at h0; rw [← h0]; exact h
          · simp only [List.any_eq_true, yRange, List.mem_map, List.mem_range] at h
            rcases h with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
            refine ⟨⟨i + 1, by omega⟩, ?_⟩
            rw [← hy_get ⟨i + 1, by omega⟩]; exact htrue
        · rintro ⟨⟨i, hi⟩, htrue⟩
          rcases i with _ | i
          · left; have h0 := hy_get ⟨0, hi⟩; simp only [add_zero] at h0; rw [h0]; exact htrue
          · right
            simp only [List.any_eq_true, yRange, List.mem_map, List.mem_range]
            refine ⟨5 * n + (i + 1), ⟨i, by omega, rfl⟩, ?_⟩
            rw [hy_get ⟨i + 1, hi⟩]; exact htrue
      have hinp_get : ∀ k : Fin (4 * n), inp.getD k.val false =
          if k.val < 2 * n then decide (k.val = u.val) else decide (k.val - 2 * n = v.val) := by
        intro k
        simp only [inp, oneEach]
        have hlen1 : (List.ofFn (fun i : Fin (2 * n) => decide (i = u))).length = 2 * n := List.length_ofFn
        by_cases hk : k.val < 2 * n
        · rw [getD_append_lt _ _ false (by omega)]
          simp [List.getD_eq_getElem?_getD, hk, Fin.ext_iff]
        · rw [getD_append_ge _ _ false (by omega), hlen1]
          simp [List.getD_eq_getElem?_getD, hk, Fin.ext_iff, show k.val - 2 * n < 2 * n by omega]
      have hx_val : ∀ i : Fin n, x.getD i.val false =
          (decide (i.val = u.val) || decide (n + i.val = v.val)) := by
        intro i
        rw [List.getD_eq_getElem?_getD]
        simp only [x, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
        rw [hinp_get ⟨i.val, by omega⟩, hinp_get ⟨3 * n + i.val, by omega⟩]
        simp only [show i.val < 2 * n by omega, ↓reduceIte,
          show ¬(3 * n + i.val < 2 * n) by omega,
          show 3 * n + i.val - 2 * n = n + i.val by omega]
      have hy_val : ∀ i : Fin n, y.getD i.val false =
          (decide (i.val = v.val) || decide (n + i.val = u.val)) := by
        intro i
        rw [List.getD_eq_getElem?_getD]
        simp only [y, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
        rw [hinp_get ⟨2 * n + i.val, by omega⟩, hinp_get ⟨n + i.val, by omega⟩]
        simp only [show ¬(2 * n + i.val < 2 * n) by omega, ↓reduceIte,
          show 2 * n + i.val - 2 * n = i.val by omega,
          show n + i.val < 2 * n by omega]
      by_cases h1 : u.val < n ∧ v.val < n
      · simp only [h1]
        have hx_eq : x = List.ofFn (fun i : Fin n => decide (i = (⟨u.val, h1.1⟩ : Fin n))) := by
          apply List.ext_getElem (by simp [hxlen])
          intro i hi1 hi2
          have hi : i < n := by simpa [hxlen] using hi1
          have := hx_val ⟨i, hi⟩
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at this
          rw [this, List.getElem_ofFn]
          simp [Fin.ext_iff, show n + i ≠ v.val by omega]
        have hy_eq : y = List.ofFn (fun j : Fin n => decide (j = (⟨v.val, h1.2⟩ : Fin n))) := by
          apply List.ext_getElem (by simp [hylen])
          intro i hi1 hi2
          have hi : i < n := by simpa [hylen] using hi1
          have := hy_val ⟨i, hi⟩
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at this
          rw [this, List.getElem_ofFn]
          simp [Fin.ext_iff, show n + i ≠ u.val by omega]
        have hxy_eq : x ++ y = oneEach (⟨u.val, h1.1⟩ : Fin n) (⟨v.val, h1.2⟩ : Fin n) := by
          rw [hx_eq, hy_eq]; rfl
        have hX_true : w4.getD wX false = true := by
          rw [hX_iff]
          refine ⟨⟨u.val, h1.1⟩, ?_⟩
          rw [hx_val ⟨u.val, h1.1⟩]
          simp
        have hY_true : w4.getD wY false = true := by
          rw [hY_iff]
          refine ⟨⟨v.val, h1.2⟩, ?_⟩
          rw [hy_val ⟨v.val, h1.2⟩]
          simp
        rw [hX_true, hY_true, hxy_eq]
        simpa using hCrep ⟨u.val, h1.1⟩ ⟨v.val, h1.2⟩
      · by_cases h2 : n ≤ u.val ∧ n ≤ v.val
        · simp only [h1, ↓reduceDIte, h2]
          have hx_eq : x = List.ofFn (fun i : Fin n => decide (i = (⟨v.val - n, by omega⟩ : Fin n))) := by
            apply List.ext_getElem (by simp [hxlen])
            intro i hi1 hi2
            have hi : i < n := by simpa [hxlen] using hi1
            have := hx_val ⟨i, hi⟩
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at this
            rw [this, List.getElem_ofFn]
            have hne : i ≠ u.val := by omega
            simp [hne, Fin.ext_iff]; omega
          have hy_eq : y = List.ofFn (fun j : Fin n => decide (j = (⟨u.val - n, by omega⟩ : Fin n))) := by
            apply List.ext_getElem (by simp [hylen])
            intro i hi1 hi2
            have hi : i < n := by simpa [hylen] using hi1
            have := hy_val ⟨i, hi⟩
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some] at this
            rw [this, List.getElem_ofFn]
            have hne : i ≠ v.val := by omega
            simp [hne, Fin.ext_iff]; omega
          have hxy_eq : x ++ y = oneEach (⟨v.val - n, by omega⟩ : Fin n) (⟨u.val - n, by omega⟩ : Fin n) := by
            rw [hx_eq, hy_eq]; rfl
          have hX_true : w4.getD wX false = true := by
            rw [hX_iff]
            refine ⟨⟨v.val - n, by omega⟩, ?_⟩
            rw [hx_val ⟨v.val - n, by omega⟩]
            simp [show n + (v.val - n) = v.val by omega]
          have hY_true : w4.getD wY false = true := by
            rw [hY_iff]
            refine ⟨⟨u.val - n, by omega⟩, ?_⟩
            rw [hy_val ⟨u.val - n, by omega⟩]
            simp [show n + (u.val - n) = u.val by omega]
          rw [hX_true, hY_true, hxy_eq]
          simpa using hCrep ⟨v.val - n, by omega⟩ ⟨u.val - n, by omega⟩
        · simp only [h1, ↓reduceDIte, h2]
          have hzero : w4.getD wX false = false ∨ w4.getD wY false = false := by
            by_cases hu : u.val < n
            · right
              have hv : n ≤ v.val := by omega
              by_contra hYt
              have hYt' : w4.getD wY false = true := Bool.eq_true_of_not_eq_false hYt
              rw [hY_iff] at hYt'
              rcases hYt' with ⟨i, hi⟩
              rw [hy_val i] at hi
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
              omega
            · left
              have hv : v.val < n := by omega
              by_contra hXt
              have hXt' : w4.getD wX false = true := Bool.eq_true_of_not_eq_false hXt
              rw [hX_iff] at hXt'
              rcases hXt' with ⟨i, hi⟩
              rw [hx_val i] at hi
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
              omega
          rcases hzero with hX0 | hY0
          · rw [List.getD_eq_getElem?_getD] at hX0; simp [hX0]
          · rw [List.getD_eq_getElem?_getD] at hY0; simp [hY0]

lemma digits_two_pow_add_sum (j b : ℕ) (hb : b < 2 ^ j) :
    (Nat.digits 2 (2 ^ j + b)).sum = (Nat.digits 2 b).sum + 1 := by
  induction j generalizing b with
  | zero =>
    have hb0 : b = 0 := by omega
    subst hb0
    decide
  | succ j ih =>
    by_cases hb0 : b = 0
    · subst hb0
      have hpos : 2 ^ (j + 1) ≠ 0 := by positivity
      rw [Nat.add_zero, Nat.digits_def' (by decide) (Nat.pos_of_ne_zero hpos)]
      simp only [List.sum_cons, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_mod_right,
        Nat.mul_div_right _ (by decide : 0 < 2), Nat.zero_add]
      have := ih 0 (by positivity)
      simpa using this
    · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
      have hsum_pos : 0 < 2 ^ (j + 1) + b := by positivity
      rw [Nat.digits_def' (by decide) hsum_pos, Nat.digits_def' (by decide) hb_pos]
      have hmod : (2 ^ (j + 1) + b) % 2 = b % 2 := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_add_mod]
      have hdiv : (2 ^ (j + 1) + b) / 2 = 2 ^ j + b / 2 := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_add_div (by decide : 0 < 2)]
      rw [hmod, hdiv]
      simp only [List.sum_cons]
      rw [ih (b / 2) (by omega)]
      omega

end PEqualNP.Outside.L_meta_18838

theorem PEqualNP.Outside.L_meta_18838 : ∀ (n j : ℕ), 1 ≤ n → ∀ (G : ℕ → ℕ → Bool) (s : ℕ),
  PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => G u.val v.val) s →
  PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin (2 ^ j * n) => decide (u.val / n = v.val / n ∧
      (((Nat.digits 2 (u.val / n)).sum % 2 = 0 ∧ G (u.val % n) (v.val % n) = true) ∨
       ((Nat.digits 2 (u.val / n)).sum % 2 = 1 ∧ G (v.val % n) (u.val % n) = true))))
    (s + 4 * n * (2 ^ j - 1)) := by
  intro n j hn G s hG
  induction j with
  | zero =>
    simp only [pow_zero, Nat.sub_self, mul_zero, add_zero]
    rcases hG with ⟨C, hCm, hCs, hCrep⟩
    refine ⟨C, hCm, hCs, ?_⟩
    intro u v
    let u0 : Fin n := ⟨u.val, by simpa using u.isLt⟩
    let v0 : Fin n := ⟨v.val, by simpa using v.isLt⟩
    have hone : PEqualNP.Represents.oneEach u v = PEqualNP.Represents.oneEach u0 v0 := by
      simp only [PEqualNP.Represents.oneEach]
      congr 1
      · apply List.ext_getElem (by simp)
        intro i hi1 hi2
        simp [u0, Fin.ext_iff]
      · apply List.ext_getElem (by simp)
        intro i hi1 hi2
        simp [v0, Fin.ext_iff]
    rw [hone, hCrep u0 v0]
    have hu0 : u.val / n = 0 := Nat.div_eq_of_lt (by simpa using u.isLt)
    have hv0 : v.val / n = 0 := Nat.div_eq_of_lt (by simpa using v.isLt)
    have hu_mod : u.val % n = u.val := Nat.mod_eq_of_lt (by simpa using u.isLt)
    have hv_mod : v.val % n = v.val := Nat.mod_eq_of_lt (by simpa using v.isLt)
    simp [u0, v0, hu0, hv0, hu_mod, hv_mod]
  | succ j ih =>
    let N := 2 ^ j * n
    have hN : 1 ≤ N := by
      have : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      dsimp only [N]
      nlinarith
    let A : Fin N → Fin N → Bool := fun u v =>
      decide (u.val / n = v.val / n ∧
        (((Nat.digits 2 (u.val / n)).sum % 2 = 0 ∧ G (u.val % n) (v.val % n) = true) ∨
         ((Nat.digits 2 (u.val / n)).sum % 2 = 1 ∧ G (v.val % n) (u.val % n) = true)))
    have hstep := PEqualNP.Outside.L_meta_18838.repSizeAtMost_double_transpose N hN A (s + 4 * n * (2 ^ j - 1)) ih
    have hpow : 2 ^ (j + 1) * n = 2 * N := by
      simp only [N, pow_succ]; ring
    have hbound : s + 4 * n * (2 ^ j - 1) + 4 * N = s + 4 * n * (2 ^ (j + 1) - 1) := by
      have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      have h2 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by decide)
      dsimp only [N]
      zify [h1, h2]
      rw [pow_succ]
      ring
    rw [hbound] at hstep
    rcases hstep with ⟨C, hCm, hCs, hCrep⟩
    refine ⟨C, hCm, hCs, ?_⟩
    intro u v
    let u' : Fin (2 * N) := ⟨u.val, by rw [← hpow]; exact u.isLt⟩
    let v' : Fin (2 * N) := ⟨v.val, by rw [← hpow]; exact v.isLt⟩
    have hone : PEqualNP.Represents.oneEach u v = PEqualNP.Represents.oneEach u' v' := by
      simp only [PEqualNP.Represents.oneEach]
      congr 1
      · apply List.ext_getElem (by simp [hpow])
        intro i hi1 hi2
        simp [u', Fin.ext_iff]
      · apply List.ext_getElem (by simp [hpow])
        intro i hi1 hi2
        simp [v', Fin.ext_iff]
    rw [hone, hCrep u' v']
    dsimp only [u', v', A]
    split_ifs with h1 h2
    · rfl
    · have hu_lt : u.val - N < N := by rw [← hpow] at *; omega
      have hv_lt : v.val - N < N := by rw [← hpow] at *; omega
      have hN_eq : N = n * 2 ^ j := by simp [N, Nat.mul_comm]
      have hu_eq : u.val = n * 2 ^ j + (u.val - N) := by omega
      have hv_eq : v.val = n * 2 ^ j + (v.val - N) := by omega
      have hu_div : u.val / n = 2 ^ j + (u.val - N) / n := by
        conv_lhs => rw [hu_eq]
        rw [Nat.mul_add_div hn, add_comm]
      have hv_div : v.val / n = 2 ^ j + (v.val - N) / n := by
        conv_lhs => rw [hv_eq]
        rw [Nat.mul_add_div hn, add_comm]
      have hu_mod : u.val % n = (u.val - N) % n := by
        conv_lhs => rw [hu_eq]
        rw [Nat.mul_add_mod]
      have hv_mod : v.val % n = (v.val - N) % n := by
        conv_lhs => rw [hv_eq]
        rw [Nat.mul_add_mod]
      have hdiv_lt : (u.val - N) / n < 2 ^ j := by
        rw [Nat.div_lt_iff_lt_mul hn]
        simpa [N, Nat.mul_comm] using hu_lt
      have hdig := PEqualNP.Outside.L_meta_18838.digits_two_pow_add_sum j ((u.val - N) / n) hdiv_lt
      rw [hu_div, hv_div, hu_mod, hv_mod, hdig]
      have hpar : ∀ k : ℕ, (k + 1) % 2 = 0 ↔ k % 2 = 1 := fun k => by omega
      have hpar2 : ∀ k : ℕ, (k + 1) % 2 = 1 ↔ k % 2 = 0 := fun k => by omega
      simp only [decide_eq_decide]
      constructor
      · rintro ⟨heq, hdisj⟩
        refine ⟨by omega, ?_⟩
        rw [heq] at hdisj
        rcases hdisj with ⟨hp, hg⟩ | ⟨hp, hg⟩
        · right; exact ⟨by omega, hg⟩
        · left; exact ⟨by omega, hg⟩
      · rintro ⟨heq, hdisj⟩
        have hdiv_eq : (u.val - N) / n = (v.val - N) / n := by omega
        refine ⟨hdiv_eq.symm, ?_⟩
        rw [hdiv_eq] at hdisj
        rcases hdisj with ⟨hp, hg⟩ | ⟨hp, hg⟩
        · right; exact ⟨by omega, hg⟩
        · left; exact ⟨by omega, hg⟩
    · have hne : u.val / n ≠ v.val / n := by
        rcases lt_or_ge u.val N with hu | hu
        · have hv : N ≤ v.val := by omega
          have h1' : u.val / n < 2 ^ j := by rw [Nat.div_lt_iff_lt_mul hn]; simpa [N, Nat.mul_comm] using hu
          have h2' : 2 ^ j ≤ v.val / n := by rw [Nat.le_div_iff_mul_le hn]; simpa [N, Nat.mul_comm] using hv
          omega
        · have hv : v.val < N := by omega
          have h1' : 2 ^ j ≤ u.val / n := by rw [Nat.le_div_iff_mul_le hn]; simpa [N, Nat.mul_comm] using hu
          have h2' : v.val / n < 2 ^ j := by rw [Nat.div_lt_iff_lt_mul hn]; simpa [N, Nat.mul_comm] using hv
          omega
      simp [hne]
