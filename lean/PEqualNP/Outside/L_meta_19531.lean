import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19531

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def val (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [val w g]

theorem get_map_range (m i : ℕ) (f : ℕ → Bool) (h : i < m) :
    ((List.range m).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem get_left (A B : List Bool) (i : ℕ) (h : i < A.length) :
    (A ++ B).getD i false = A.getD i false := by
  rw [List.getD_append _ _ _ _ h]

theorem get_right (A B : List Bool) (i j : ℕ) (h : i = A.length + j) :
    (A ++ B).getD i false = B.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

def cGate (L base j : ℕ) : Gate :=
  ⟨GateOp.or, [if j = 0 then base else L + j - 1, base + j + 1]⟩

def outIdx (L base k : ℕ) : ℕ :=
  if k = 0 then base else L + k - 1

theorem outIdx_lt (L base k : ℕ) (hk : base + k < L) :
    outIdx L base k < L + k := by
  unfold outIdx
  split_ifs <;> omega

theorem chain (L base : ℕ) (W : List Bool) (hW : W.length = L) (m : ℕ)
    (hm : base + m < L) :
    ((List.range m).map (cGate L base)).foldl step W =
      W ++ (List.range m).map
        (fun j => (List.range (j + 2)).any fun i => W.getD (base + i) false) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega), List.map_append,
      ← List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    congr 1
    congr 1
    set E := (List.range m).map
      (fun j => (List.range (j + 2)).any fun i => W.getD (base + i) false) with hE
    have hE_len : E.length = m := by simp [hE]
    have h2 : (W ++ E).getD (base + m + 1) false = W.getD (base + (m + 1)) false := by
      rw [get_left W E _ (by omega)]
      rfl
    have h1 : (W ++ E).getD (if m = 0 then base else L + m - 1) false =
        (List.range (m + 1)).any fun i => W.getD (base + i) false := by
      by_cases h0 : m = 0
      · subst h0
        change (W ++ E).getD base false = _
        rw [get_left W E _ (by omega)]
        simp
      · have hif : (if m = 0 then base else L + m - 1) = L + m - 1 := by simp [h0]
        rw [hif, get_right W E _ (m - 1) (by omega), hE,
          get_map_range m (m - 1) _ (by omega)]
        have e : m - 1 + 2 = m + 1 := by omega
        rw [e]
    have h3 : ((List.range (m + 2)).any fun i => W.getD (base + i) false) =
        (((List.range (m + 1)).any fun i => W.getD (base + i) false) ||
          W.getD (base + (m + 1)) false) := by
      rw [List.range_succ, List.any_append]
      simp
    unfold val cGate
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, h1, h2, h3]

theorem chain_out (L base : ℕ) (W : List Bool) (hW : W.length = L) (k : ℕ)
    (hk : base + k < L) :
    (((List.range k).map (cGate L base)).foldl step W).getD (outIdx L base k) false =
      (List.range (k + 1)).any fun i => W.getD (base + i) false := by
  rw [chain L base W hW k hk]
  set E := (List.range k).map
    (fun j => (List.range (j + 2)).any fun i => W.getD (base + i) false) with hE
  unfold outIdx
  by_cases h0 : k = 0
  · subst h0
    simp [hE]
  · have hif : (if k = 0 then base else L + k - 1) = L + k - 1 := by simp [h0]
    rw [hif, get_right W E _ (k - 1) (by omega), hE,
      get_map_range k (k - 1) _ (by omega)]
    have e : k - 1 + 2 = k + 1 := by omega
    rw [e]

theorem tail3 (W : List Bool) (top wL wR z0 zn : ℕ)
    (hW : W.length = top) (h0 : z0 < top) (hn : zn < top) :
    ([⟨GateOp.and, [wL, wR]⟩, ⟨GateOp.or, [z0, zn]⟩,
      ⟨GateOp.or, [top + 1, top]⟩].foldl step W).getD (top + 2) false =
      ((W.getD z0 false || W.getD zn false) || (W.getD wL false && W.getD wR false)) := by
  simp only [List.foldl_cons, List.foldl_nil]
  set g1 : Gate := ⟨GateOp.and, [wL, wR]⟩
  set g2 : Gate := ⟨GateOp.or, [z0, zn]⟩
  set g3 : Gate := ⟨GateOp.or, [top + 1, top]⟩
  set W1 := step W g1 with hW1_def
  set W2 := step W1 g2 with hW2_def
  set W3 := step W2 g3 with hW3_def
  have hlen1 : W1.length = top + 1 := by simp [hW1_def, step, hW]
  have hlen2 : W2.length = top + 2 := by simp [hW2_def, step, hlen1]
  have hv1 : val W g1 = (W.getD wL false && W.getD wR false) := by
    simp [val, g1, GateOp.eval]
  have hv2 : val W1 g2 = (W.getD z0 false || W.getD zn false) := by
    simp only [val, g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hW1_def, step]
    rw [get_left W _ z0 (by omega), get_left W _ zn (by omega)]
  have hw2_top1 : W2.getD (top + 1) false = val W1 g2 := by
    rw [hW2_def, step, get_right W1 [val W1 g2] (top + 1) 0 (by omega)]
    simp
  have hw2_top : W2.getD top false = val W g1 := by
    rw [hW2_def, step, get_left W1 [val W1 g2] top (by omega),
      hW1_def, step, get_right W [val W g1] top 0 (by omega)]
    simp
  have hv3 : val W2 g3 = (val W1 g2 || val W g1) := by
    simp only [val, g3, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hw2_top1, hw2_top]
  rw [hW3_def, step, get_right W2 [val W2 g3] (top + 2) 0 (by omega)]
  simp [hv3, hv2, hv1]

def circ (n : ℕ) : Circuit :=
  let k := n - 3
  let wL := outIdx (2 * n) 1 k
  let wR := outIdx (2 * n + k) (n + 1) k
  let top := 2 * n + 2 * k
  ⟨(List.range k).map (cGate (2 * n) 1) ++
    (List.range k).map (cGate (2 * n + k) (n + 1)) ++
    [⟨GateOp.and, [wL, wR]⟩, ⟨GateOp.or, [0, n]⟩, ⟨GateOp.or, [top + 1, top]⟩],
   top + 2⟩

theorem eval_circ (n : ℕ) (hn : 3 ≤ n) (X : List Bool) (hX : X.length = 2 * n) :
    (circ n).eval X =
      ((X.getD 0 false || X.getD n false) ||
        (((List.range (n - 2)).any fun i => X.getD (1 + i) false) &&
         ((List.range (n - 2)).any fun i => X.getD (n + 1 + i) false))) := by
  set k := n - 3 with hk_def
  have hk1 : k + 1 = n - 2 := by omega
  have hw : (circ n).wires X = (circ n).gates.foldl step X := rfl
  unfold Circuit.eval
  rw [hw]
  dsimp only [circ]
  rw [ ← hk_def ]
  simp only [List.foldl_append]
  set W1 := ((List.range k).map (cGate (2 * n) 1)).foldl step X with hW1_def
  have hW1_eq := chain (2 * n) 1 X hX k (by omega)
  have hW1_len : W1.length = 2 * n + k := by
    rw [hW1_def, hW1_eq]
    simp [hX]
  have hW1_lt : ∀ j, j < 2 * n → W1.getD j false = X.getD j false := by
    intro j hj
    rw [hW1_def, hW1_eq, get_left X _ j (by omega)]
  have hwL1 : W1.getD (outIdx (2 * n) 1 k) false =
      (List.range (n - 2)).any fun i => X.getD (1 + i) false := by
    rw [← hk1, hW1_def]
    exact chain_out (2 * n) 1 X hX k (by omega)
  set W2 := ((List.range k).map (cGate (2 * n + k) (n + 1))).foldl step W1 with hW2_def
  have hW2_eq := chain (2 * n + k) (n + 1) W1 hW1_len k (by omega)
  have hW2_len : W2.length = 2 * n + 2 * k := by
    rw [hW2_def, hW2_eq]
    simp [hW1_len]
    omega
  have hW2_lt : ∀ j, j < 2 * n + k → W2.getD j false = W1.getD j false := by
    intro j hj
    rw [hW2_def, hW2_eq, get_left W1 _ j (by omega)]
  have hwL_lt1 : outIdx (2 * n) 1 k < 2 * n + k := outIdx_lt (2 * n) 1 k (by omega)
  rw [tail3 W2 (2 * n + 2 * k) (outIdx (2 * n) 1 k) (outIdx (2 * n + k) (n + 1) k) 0 n
    hW2_len (by omega) (by omega)]
  have h0_eq : W2.getD 0 false = X.getD 0 false := by
    rw [hW2_lt 0 (by omega), hW1_lt 0 (by omega)]
  have hn_eq : W2.getD n false = X.getD n false := by
    rw [hW2_lt n (by omega), hW1_lt n (by omega)]
  have hwL_eq : W2.getD (outIdx (2 * n) 1 k) false =
      (List.range (n - 2)).any fun i => X.getD (1 + i) false := by
    rw [hW2_lt _ hwL_lt1, hwL1]
  have hwR_eq : W2.getD (outIdx (2 * n + k) (n + 1) k) false =
      (List.range (n - 2)).any fun i => X.getD (n + 1 + i) false := by
    have hc := chain_out (2 * n + k) (n + 1) W1 hW1_len k (by omega)
    rw [hW2_def, hc, hk1]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rw [List.mem_range] at hi
      rwa [hW1_lt (n + 1 + i) (by omega)] at h
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rw [List.mem_range] at hi
      rwa [hW1_lt (n + 1 + i) (by omega)]
  rw [h0_eq, hn_eq, hwL_eq, hwR_eq]

theorem oneEach_left {n : ℕ} (u v : Fin n) (a : ℕ) (ha : a < n) :
    (oneEach u v).getD a false = decide (a = (u : ℕ)) := by
  unfold oneEach
  rw [get_left _ _ a (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha, Fin.ext_iff]

theorem oneEach_right {n : ℕ} (u v : Fin n) (b : ℕ) (hb : b < n) :
    (oneEach u v).getD (n + b) false = decide (b = (v : ℕ)) := by
  unfold oneEach
  rw [get_right _ _ (n + b) b (by simp)]
  simp [List.getD_eq_getElem?_getD, hb, Fin.ext_iff]

theorem circ_mono (n : ℕ) : Monotone2 (circ n) := by
  intro g hg
  simp only [circ, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) | (rfl | rfl | rfl) <;> simp [cGate]

theorem circ_size (n : ℕ) (hn : 3 ≤ n) : (circ n).size ≤ 2 * n - 3 := by
  show (circ n).gates.length ≤ 2 * n - 3
  simp [circ]
  omega

theorem circ_rep (n : ℕ) (hn : 3 ≤ n) :
    Represents
      (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1)))
      (circ n) := by
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  rw [eval_circ n hn (oneEach u v) (by simp [oneEach]; omega), Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  have hz0 : (oneEach u v).getD 0 false = true ↔ (u : ℕ) = 0 := by
    rw [oneEach_left u v 0 (by omega), decide_eq_true_iff, eq_comm]
  have hzn : (oneEach u v).getD n false = true ↔ (v : ℕ) = 0 := by
    have hr : (oneEach u v).getD n false = decide (0 = (v : ℕ)) := oneEach_right u v 0 (by omega)
    rw [hr, decide_eq_true_iff, eq_comm]
  have hmL : ((List.range (n - 2)).any fun i => (oneEach u v).getD (1 + i) false) = true ↔
      (1 ≤ (u : ℕ) ∧ (u : ℕ) ≠ n - 1) := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [List.mem_range] at hi
      rw [oneEach_left u v (1 + i) (by omega), decide_eq_true_iff] at h
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨(u : ℕ) - 1, List.mem_range.mpr (by omega), ?_⟩
      rw [oneEach_left u v (1 + ((u : ℕ) - 1)) (by omega), decide_eq_true_iff]
      omega
  have hmR : ((List.range (n - 2)).any fun i => (oneEach u v).getD (n + 1 + i) false) = true ↔
      (1 ≤ (v : ℕ) ∧ (v : ℕ) ≠ n - 1) := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      rw [List.mem_range] at hi
      have idx_eq : n + 1 + i = n + (1 + i) := by omega
      rw [idx_eq, oneEach_right u v (1 + i) (by omega), decide_eq_true_iff] at h
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨(v : ℕ) - 1, List.mem_range.mpr (by omega), ?_⟩
      have idx_eq : n + 1 + ((v : ℕ) - 1) = n + (1 + ((v : ℕ) - 1)) := by omega
      rw [idx_eq, oneEach_right u v (1 + ((v : ℕ) - 1)) (by omega), decide_eq_true_iff]
      omega
  rw [hz0, hzn, hmL, hmR]
  omega

end PEqualNP.Outside.L_meta_19531

theorem PEqualNP.Outside.L_meta_19531 : (∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) (2 * n - 3)) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_19531.circ n,
    PEqualNP.Outside.L_meta_19531.circ_mono n,
    PEqualNP.Outside.L_meta_19531.circ_size n hn,
    PEqualNP.Outside.L_meta_19531.circ_rep n hn⟩
