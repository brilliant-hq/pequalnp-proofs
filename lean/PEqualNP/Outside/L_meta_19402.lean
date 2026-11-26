import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19402

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def orChain (prev baseWire : ℕ) : List ℕ → List Gate
  | [] => []
  | a :: rest => ⟨GateOp.or, [prev, a]⟩ :: orChain baseWire (baseWire + 1) rest

def chainOut (prev baseWire : ℕ) (items : List ℕ) : ℕ :=
  if items.isEmpty then prev else baseWire + items.length - 1

theorem orChain_len (prev baseWire : ℕ) (items : List ℕ) :
    (orChain prev baseWire items).length = items.length := by
  induction items generalizing prev baseWire with
  | nil => rfl
  | cons a rest ih => simp [orChain, ih]

theorem orChain_mono (prev baseWire : ℕ) (items : List ℕ) :
    ∀ g ∈ orChain prev baseWire items, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction items generalizing prev baseWire with
  | nil => intro g hg; cases hg
  | cons a rest ih =>
    intro g hg
    simp only [orChain, List.mem_cons] at hg
    rcases hg with rfl | hrest
    · simp
    · exact ih baseWire (baseWire + 1) g hrest

theorem foldl_orChain (prev baseWire : ℕ) (items : List ℕ) :
    ∀ w : List Bool, w.length = baseWire → prev < baseWire → (∀ a ∈ items, a < baseWire) →
      let w' := (orChain prev baseWire items).foldl stepWire w
      w'.length = baseWire + items.length ∧
      (∀ i < baseWire, w'.getD i false = w.getD i false) ∧
      w'.getD (chainOut prev baseWire items) false = (w.getD prev false || items.any (fun a => w.getD a false)) := by
  induction items generalizing prev baseWire with
  | nil =>
    intro w hw _ _
    simp [orChain, chainOut, hw]
  | cons a rest ih =>
    intro w hw hprev hlt
    have ha_lt : a < baseWire := hlt a List.mem_cons_self
    have hrest_lt : ∀ b ∈ rest, b < baseWire + 1 := fun b hb => by
      have := hlt b (List.mem_cons_of_mem _ hb); omega
    let v : Bool := w.getD prev false || w.getD a false
    let w1 : List Bool := w ++ [v]
    have hw1_step : stepWire w ⟨GateOp.or, [prev, a]⟩ = w1 := by
      simp [stepWire, w1, v, GateOp.eval]
    have hw1_len : w1.length = baseWire + 1 := by simp [w1, hw]
    have hrec := ih baseWire (baseWire + 1) w1 hw1_len (by omega) hrest_lt
    have hfold : (orChain prev baseWire (a :: rest)).foldl stepWire w =
        (orChain baseWire (baseWire + 1) rest).foldl stepWire w1 := by
      simp only [orChain, List.foldl_cons, hw1_step]
    dsimp only at hrec ⊢
    rw [hfold]
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_, ?_⟩
    · rw [hrec.2.1 i (by omega)]
      exact List.getD_append w [v] false i (by omega)
    · have hout : chainOut prev baseWire (a :: rest) = chainOut baseWire (baseWire + 1) rest := by
        cases rest with
        | nil => simp [chainOut]
        | cons b bs => simp [chainOut]; omega
      rw [hout, hrec.2.2]
      have hw1_base : w1.getD baseWire false = v := by
        dsimp [w1]; rw [← hw]; simp
      have hany : rest.any (fun b => w1.getD b false) = rest.any (fun b => w.getD b false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨b, hb, hbw⟩
          have hblt : b < baseWire := hlt b (List.mem_cons_of_mem _ hb)
          rw [List.getD_append w [v] false b (by omega)] at hbw
          exact ⟨b, hb, hbw⟩
        · rintro ⟨b, hb, hbw⟩
          have hblt : b < baseWire := hlt b (List.mem_cons_of_mem _ hb)
          exact ⟨b, hb, by rw [List.getD_append w [v] false b (by omega)]; exact hbw⟩
      rw [hw1_base, hany]
      simp only [v, List.any_cons, Bool.or_assoc]

theorem oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < 2 * n) :
    (oneEach u v).getD i false = if i < n then decide (i = u.val) else decide (i - n = v.val) := by
  by_cases hn : i < n
  · simp only [hn, ↓reduceIte, oneEach, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp; omega : i < (List.ofFn (fun a : Fin n => decide (a = u))).length),
      List.getElem?_ofFn, ↓reduceDIte, Option.getD_some]
    simp [Fin.ext_iff]
  · have hlen : (List.ofFn (fun a : Fin n => decide (a = u))).length = n := by simp
    have hlt : i - n < n := by omega
    simp only [hn, ↓reduceIte, oneEach, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : (List.ofFn (fun a : Fin n => decide (a = u))).length ≤ i),
      hlen, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
    simp [Fin.ext_iff]

def rowItems (n : ℕ) : List ℕ :=
  (List.range (n - 3)).map (· + 3)

def colItems (n : ℕ) : List ℕ :=
  (List.range (n - 3)).map (· + (n + 3))

def famCircuit (n : ℕ) : Circuit :=
  let rLen := n - 3
  let b1 := orChain 2 (2 * n) (rowItems n)
  let b2 := orChain n (2 * n + rLen) (colItems n)
  let wR := 2 * n + rLen - 1
  let wC1 := 2 * n + 2 * rLen - 1
  let base := 2 * n + 2 * rLen
  let b3 : List Gate :=
    [⟨GateOp.or, [n + 1, n + 2]⟩,
     ⟨GateOp.or, [n, base]⟩,
     ⟨GateOp.and, [0, base]⟩,
     ⟨GateOp.and, [1, wC1]⟩,
     ⟨GateOp.and, [wR, base + 1]⟩,
     ⟨GateOp.or, [base + 2, base + 3]⟩,
     ⟨GateOp.or, [base + 5, base + 4]⟩]
  ⟨b1 ++ b2 ++ b3, base + 6⟩

theorem famCircuit_mono (n : ℕ) : Monotone2 (famCircuit n) := by
  intro g hg
  unfold famCircuit at hg
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact orChain_mono _ _ _ g hg
  · exact orChain_mono _ _ _ g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem famCircuit_size (n : ℕ) (hn : 4 ≤ n) : (famCircuit n).size ≤ 2 * n + 1 := by
  unfold famCircuit Circuit.size
  simp only [List.length_append, orChain_len, rowItems, colItems, List.length_map, List.length_range,
    List.length_cons, List.length_nil]
  omega

theorem famCircuit_rep (n : ℕ) (hn : 4 ≤ n) :
    Represents (fun (u : Fin n) (v : Fin n) =>
      decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨
              (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨
              (2 ≤ u.val ∧ v.val ≤ 2))) (famCircuit n) := by
  intro u v
  unfold Circuit.eval Circuit.wires famCircuit
  dsimp only
  change (((orChain 2 (2 * n) (rowItems n) ++ orChain n (2 * n + (n - 3)) (colItems n) ++
    ([⟨GateOp.or, [n + 1, n + 2]⟩,
      ⟨GateOp.or, [n, 2 * n + 2 * (n - 3)]⟩,
      ⟨GateOp.and, [0, 2 * n + 2 * (n - 3)]⟩,
      ⟨GateOp.and, [1, 2 * n + 2 * (n - 3) - 1]⟩,
      ⟨GateOp.and, [2 * n + (n - 3) - 1, 2 * n + 2 * (n - 3) + 1]⟩,
      ⟨GateOp.or, [2 * n + 2 * (n - 3) + 2, 2 * n + 2 * (n - 3) + 3]⟩,
      ⟨GateOp.or, [2 * n + 2 * (n - 3) + 5, 2 * n + 2 * (n - 3) + 4]⟩] : List Gate)).foldl stepWire (oneEach u v)).getD (2 * n + 2 * (n - 3) + 6) false) = _
  rw [List.foldl_append, List.foldl_append]
  set x := oneEach u v
  have hxlen : x.length = 2 * n := oneEach_len u v
  have hrow_lt : ∀ a ∈ rowItems n, a < 2 * n := by
    intro a ha; simp only [rowItems, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨k, hk, rfl⟩; omega
  have hb1 := foldl_orChain 2 (2 * n) (rowItems n) x hxlen (by omega) hrow_lt
  set w1 := (orChain 2 (2 * n) (rowItems n)).foldl stepWire x
  have hw1_len : w1.length = 2 * n + (n - 3) := by
    have := hb1.1; simp only [rowItems, List.length_map, List.length_range] at this; exact this
  have hcol_lt : ∀ a ∈ colItems n, a < 2 * n + (n - 3) := by
    intro a ha; simp only [colItems, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨k, hk, rfl⟩; omega
  have hb2 := foldl_orChain n (2 * n + (n - 3)) (colItems n) w1 hw1_len (by omega) hcol_lt
  set w2 := (orChain n (2 * n + (n - 3)) (colItems n)).foldl stepWire w1
  set rLen := n - 3
  set wR := 2 * n + rLen - 1
  set wC1 := 2 * n + 2 * rLen - 1
  set base := 2 * n + 2 * rLen
  have hw2_len : w2.length = base := by
    have := hb2.1; simp only [colItems, List.length_map, List.length_range] at this; dsimp [base, rLen]; omega
  have hw2_x : ∀ i < 2 * n, w2.getD i false = x.getD i false := fun i hi => by
    rw [hb2.2.1 i (by omega), hb1.2.1 i hi]
  have hw2_R : w2.getD wR false = decide (2 ≤ u.val) := by
    rw [hb2.2.1 wR (by dsimp [wR, rLen]; omega)]
    have hout1 : chainOut 2 (2 * n) (rowItems n) = wR := by
      have hlen : (rowItems n).length = n - 3 := by simp [rowItems]
      have hne : (rowItems n).isEmpty = false := by
        cases h : rowItems n with
        | nil => rw [h] at hlen; simp at hlen; omega
        | cons _ _ => rfl
      simp only [chainOut, hne, Bool.false_eq_true, ↓reduceIte, hlen, wR, rLen]
    rw [← hout1, hb1.2.2]
    rw [oneEach_getD u v 2 (by omega)]
    simp only [show (2 : ℕ) < n by omega, ↓reduceIte]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, rowItems, List.mem_map, List.mem_range]
    constructor
    · rintro (h2 | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · omega
      · rw [oneEach_getD u v (k + 3) (by omega)] at hx
        simp only [show k + 3 < n by omega, ↓reduceIte, decide_eq_true_eq] at hx
        omega
    · intro hge
      by_cases h2 : u.val = 2
      · left; omega
      · right; refine ⟨u.val, ⟨u.val - 3, by omega, by omega⟩, ?_⟩
        rw [oneEach_getD u v u.val (by omega)]
        simp only [u.isLt, ↓reduceIte, decide_eq_true_eq]
  have hw2_C1 : w2.getD wC1 false = decide (¬ (v.val = 1 ∨ v.val = 2)) := by
    have hout2 : chainOut n (2 * n + rLen) (colItems n) = wC1 := by
      have hlen : (colItems n).length = n - 3 := by simp [colItems]
      have hne : (colItems n).isEmpty = false := by
        cases h : colItems n with
        | nil => rw [h] at hlen; simp at hlen; omega
        | cons _ _ => rfl
      simp only [chainOut, hne, Bool.false_eq_true, ↓reduceIte, hlen, wC1, rLen]; omega
    rw [← hout2, hb2.2.2]
    rw [hb1.2.1 n (by omega), oneEach_getD u v n (by omega)]
    simp only [Nat.lt_irrefl, ↓reduceIte]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, colItems, List.mem_map, List.mem_range]
    constructor
    · rintro (h0 | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · omega
      · rw [hb1.2.1 (k + (n + 3)) (by omega), oneEach_getD u v (k + (n + 3)) (by omega)] at hx
        simp only [show ¬ (k + (n + 3) < n) by omega, ↓reduceIte, decide_eq_true_eq] at hx
        omega
    · intro hne
      by_cases h0 : v.val = 0
      · left; omega
      · right; refine ⟨n + v.val, ⟨v.val - 3, by omega, by omega⟩, ?_⟩
        rw [hb1.2.1 (n + v.val) (by omega), oneEach_getD u v (n + v.val) (by omega)]
        simp only [show ¬ (n + v.val < n) by omega, ↓reduceIte, decide_eq_true_eq]
        omega
  have hw2_0 : w2.getD 0 false = decide (u.val = 0) := by
    rw [hw2_x 0 (by omega), oneEach_getD u v 0 (by omega)]
    simp [show (0 : ℕ) < n by omega, eq_comm]
  have hw2_1 : w2.getD 1 false = decide (u.val = 1) := by
    rw [hw2_x 1 (by omega), oneEach_getD u v 1 (by omega)]
    simp [show (1 : ℕ) < n by omega, eq_comm]
  have hw2_n : w2.getD n false = decide (v.val = 0) := by
    rw [hw2_x n (by omega), oneEach_getD u v n (by omega)]
    simp [eq_comm]
  have hw2_n1 : w2.getD (n + 1) false = decide (v.val = 1) := by
    rw [hw2_x (n + 1) (by omega), oneEach_getD u v (n + 1) (by omega)]
    simp [show ¬ (n + 1 < n) by omega, eq_comm]
  have hw2_n2 : w2.getD (n + 2) false = decide (v.val = 2) := by
    rw [hw2_x (n + 2) (by omega), oneEach_getD u v (n + 2) (by omega)]
    simp [show ¬ (n + 2 < n) by omega, eq_comm]
  have hget_lt : ∀ (extra : List Bool) (i : ℕ), i < base → (w2 ++ extra).getD i false = w2.getD i false :=
    fun extra i hi => List.getD_append w2 extra false i (by omega)
  have hget_base : ∀ (extra : List Bool), (w2 ++ extra).getD base false = extra.getD 0 false := by
    intro extra
    rw [List.getD_append_right w2 extra false base (by omega), hw2_len]
    simp
  have hget_ge : ∀ (extra : List Bool) (k : ℕ), (w2 ++ extra).getD (base + k) false = extra.getD k false := by
    intro extra k
    rw [List.getD_append_right w2 extra false (base + k) (by omega), hw2_len]
    simp
  let g0 : Bool := w2.getD (n + 1) false || w2.getD (n + 2) false
  let g1 : Bool := w2.getD n false || g0
  let g2 : Bool := w2.getD 0 false && g0
  let g3 : Bool := w2.getD 1 false && w2.getD wC1 false
  let g4 : Bool := w2.getD wR false && g1
  let g5 : Bool := g2 || g3
  let g6 : Bool := g5 || g4
  have hs0 : stepWire w2 ⟨GateOp.or, [n + 1, n + 2]⟩ = w2 ++ [g0] := by
    simp [stepWire, GateOp.eval, g0]
  have hs1 : stepWire (w2 ++ [g0]) ⟨GateOp.or, [n, base]⟩ = w2 ++ [g0, g1] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_lt [g0] n (by dsimp [base, rLen]; omega), hget_base [g0]]
    rfl
  have hs2 : stepWire (w2 ++ [g0, g1]) ⟨GateOp.and, [0, base]⟩ = w2 ++ [g0, g1, g2] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_lt [g0, g1] 0 (by dsimp [base, rLen]; omega), hget_base [g0, g1]]
    rfl
  have hs3 : stepWire (w2 ++ [g0, g1, g2]) ⟨GateOp.and, [1, wC1]⟩ = w2 ++ [g0, g1, g2, g3] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_lt [g0, g1, g2] 1 (by dsimp [base, rLen]; omega),
        hget_lt [g0, g1, g2] wC1 (by dsimp [wC1, base, rLen]; omega)]
  have hs4 : stepWire (w2 ++ [g0, g1, g2, g3]) ⟨GateOp.and, [wR, base + 1]⟩ = w2 ++ [g0, g1, g2, g3, g4] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_lt [g0, g1, g2, g3] wR (by dsimp [wR, base, rLen]; omega),
        hget_ge [g0, g1, g2, g3] 1]
    rfl
  have hs5 : stepWire (w2 ++ [g0, g1, g2, g3, g4]) ⟨GateOp.or, [base + 2, base + 3]⟩ = w2 ++ [g0, g1, g2, g3, g4, g5] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_ge [g0, g1, g2, g3, g4] 2, hget_ge [g0, g1, g2, g3, g4] 3]
    rfl
  have hs6 : stepWire (w2 ++ [g0, g1, g2, g3, g4, g5]) ⟨GateOp.or, [base + 5, base + 4]⟩ = w2 ++ [g0, g1, g2, g3, g4, g5, g6] := by
    simp only [stepWire, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, List.append_assoc, List.cons_append, List.nil_append]
    rw [hget_ge [g0, g1, g2, g3, g4, g5] 5, hget_ge [g0, g1, g2, g3, g4, g5] 4]
    rfl
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hget_ge [g0, g1, g2, g3, g4, g5, g6] 6]
  simp only [List.getD_cons_zero, List.getD_cons_succ, g6, g5, g4, g3, g2, g1, g0]
  rw [hw2_n1, hw2_n2, hw2_n, hw2_0, hw2_1, hw2_C1, hw2_R]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

end PEqualNP.Outside.L_meta_19402

theorem PEqualNP.Outside.L_meta_19402 : (∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) (2 * n + 1)) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_19402.famCircuit n,
    PEqualNP.Outside.L_meta_19402.famCircuit_mono n,
    PEqualNP.Outside.L_meta_19402.famCircuit_size n hn,
    PEqualNP.Outside.L_meta_19402.famCircuit_rep n hn⟩
