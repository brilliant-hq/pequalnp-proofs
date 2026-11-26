import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def val (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [val w g]

theorem block (gs : List Gate) : ∀ pre ext : List Bool,
    (∀ g ∈ gs, ∀ j ∈ g.inputs, j < pre.length) →
    gs.foldl step (pre ++ ext) = pre ++ ext ++ gs.map (val pre) := by
  induction gs with
  | nil => intro pre ext _; simp
  | cons g t ih =>
    intro pre ext h
    have hv : val (pre ++ ext) g = val pre g := by
      unfold val
      congr 1
      apply List.map_congr_left
      intro j hj
      exact List.getD_append _ _ _ _ (h g (List.mem_cons_self ..) j hj)
    have hs : step (pre ++ ext) g = pre ++ (ext ++ [val pre g]) := by
      unfold step
      rw [hv, List.append_assoc]
    rw [List.foldl_cons, hs, ih pre _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    simp

theorem get_map_range (m i : ℕ) (f : ℕ → Bool) (h : i < m) :
    ((List.range m).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem get_right (A B : List Bool) (i j : ℕ) (h : i = A.length + j) :
    (A ++ B).getD i false = B.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

def cG (b N j : ℕ) : Gate :=
  ⟨.or, [if j = 0 then b else N + j - 1, b + j + 1]⟩

theorem chain (b N : ℕ) (W : List Bool) (hW : W.length = N) (m : ℕ) (hm : b + m + 1 ≤ N) :
    ((List.range m).map (cG b N)).foldl step W =
      W ++ (List.range m).map
        (fun j => (List.range (j + 2)).any fun i => W.getD (b + i) false) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega), List.map_append,
      ← List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    congr 1
    congr 1
    set L := (List.range m).map
      (fun j => (List.range (j + 2)).any fun i => W.getD (b + i) false) with hL
    have h2 : (W ++ L).getD (b + m + 1) false = W.getD (b + (m + 1)) false := by
      rw [List.getD_append _ _ _ _ (by omega)]
      rfl
    have h1 : (W ++ L).getD (if m = 0 then b else N + m - 1) false =
        (List.range (m + 1)).any fun i => W.getD (b + i) false := by
      by_cases h0 : m = 0
      · subst h0
        rw [if_pos rfl, List.getD_append _ _ _ _ (by omega)]
        simp
      · rw [if_neg h0, get_right W L _ (m - 1) (by omega), hL,
          get_map_range m (m - 1) _ (by omega)]
        have e : m - 1 + 2 = m + 1 := by omega
        rw [e]
    have h3 : ((List.range (m + 2)).any fun i => W.getD (b + i) false) =
        (((List.range (m + 1)).any fun i => W.getD (b + i) false) ||
          W.getD (b + (m + 1)) false) := by
      rw [List.range_succ, List.any_append]
      simp
    unfold val cG
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, h1, h2, h3]

def rW (n : ℕ) : ℕ := if n = 4 then 1 else 3 * n - 5

def cW (n : ℕ) : ℕ := if n = 4 then n + 3 else 4 * n - 9

def tail (n : ℕ) : List Gate :=
  [⟨.or, [n - 2, n - 1]⟩, ⟨.or, [0, 4 * n - 8]⟩, ⟨.or, [n, n + 1]⟩, ⟨.or, [4 * n - 8 + 2, cW n]⟩,
    ⟨.and, [n + 2, 4 * n - 8 + 1]⟩, ⟨.and, [rW n, 4 * n - 8 + 3]⟩, ⟨.and, [4 * n - 8, 4 * n - 8 + 2]⟩,
    ⟨.or, [4 * n - 8 + 4, 4 * n - 8 + 5]⟩, ⟨.or, [4 * n - 8 + 7, 4 * n - 8 + 6]⟩]

def circ (n : ℕ) : Circuit :=
  ⟨(List.range (n - 4)).map (cG 1 (2 * n)) ++ (List.range (n - 4)).map (cG (n + 3) (3 * n - 4)) ++
    tail n, 4 * n - 8 + 8⟩

def anyB (X : List Bool) (b k : ℕ) : Bool := (List.range k).any fun i => X.getD (b + i) false

theorem eval_circ (n : ℕ) (hn : 4 ≤ n) (X : List Bool) (hX : X.length = 2 * n) :
    (circ n).eval X =
      (((X.getD (n + 2) false && (X.getD 0 false || (X.getD (n - 2) false || X.getD (n - 1) false))) ||
        (anyB X 1 (n - 3) && ((X.getD n false || X.getD (n + 1) false) || anyB X (n + 3) (n - 3)))) ||
        ((X.getD (n - 2) false || X.getD (n - 1) false) && (X.getD n false || X.getD (n + 1) false))) := by
  have e1 := chain 1 (2 * n) X hX (n - 4) (by omega)
  set W1 := X ++ (List.range (n - 4)).map
      (fun j => (List.range (j + 2)).any fun i => X.getD (1 + i) false) with hW1
  have l1 : W1.length = 3 * n - 4 := by simp [hW1, hX]; omega
  have e2 := chain (n + 3) (3 * n - 4) W1 l1 (n - 4) (by omega)
  set W2 := W1 ++ (List.range (n - 4)).map
      (fun j => (List.range (j + 2)).any fun i => W1.getD (n + 3 + i) false) with hW2
  have l2 : W2.length = 4 * n - 8 := by simp [hW2, l1]; omega
  have x2 : ∀ i, i < 2 * n → W2.getD i false = X.getD i false := by
    intro i hi
    rw [hW2, List.getD_append _ _ _ _ (by omega), hW1, List.getD_append _ _ _ _ (by omega)]
  have rA : W2.getD (rW n) false = anyB X 1 (n - 3) := by
    unfold rW
    by_cases h4 : n = 4
    · subst h4
      rw [if_pos rfl, x2 1 (by omega)]
      simp [anyB]
    rw [if_neg h4, hW2, List.getD_append _ _ _ _ (by omega), hW1,
      get_right _ _ _ (n - 5) (by omega), get_map_range (n - 4) (n - 5) _ (by omega)]
    have e : n - 5 + 2 = n - 3 := by omega
    rw [e]; rfl
  have cA : W2.getD (cW n) false = anyB X (n + 3) (n - 3) := by
    unfold cW
    by_cases h4 : n = 4
    · subst h4
      rw [if_pos rfl, x2 7 (by omega)]
      simp [anyB]
    rw [if_neg h4, hW2, get_right _ _ _ (n - 5) (by omega),
      get_map_range (n - 4) (n - 5) _ (by omega)]
    have e : n - 5 + 2 = n - 3 := by omega
    rw [e]
    unfold anyB
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      have hi' := List.mem_range.1 hi
      exact ⟨i, hi, by rwa [hW1, List.getD_append _ _ _ _ (by simp [hX]; omega)] at h⟩
    · rintro ⟨i, hi, h⟩
      have hi' := List.mem_range.1 hi
      exact ⟨i, hi, by rwa [hW1, List.getD_append _ _ _ _ (by simp [hX]; omega)]⟩
  have hw : (circ n).wires X = (tail n).foldl step W2 := by
    have : (circ n).wires X = (circ n).gates.foldl step X := rfl
    rw [this]
    unfold circ
    simp only [List.foldl_append]
    rw [e1, e2]
  unfold Circuit.eval
  rw [hw, show (circ n).output = 4 * n - 8 + 8 from rfl]
  have g0 := x2 0 (by omega)
  have ga := x2 (n - 2) (by omega)
  have gb := x2 (n - 1) (by omega)
  have gn := x2 n (by omega)
  have gn1 := x2 (n + 1) (by omega)
  have gn2 := x2 (n + 2) (by omega)
  have gl : ∀ (l : List Bool) (i : ℕ), i < 4 * n - 8 → (W2 ++ l).getD i false = W2.getD i false :=
    fun l i h => List.getD_append _ _ _ _ (by omega)
  have gr : ∀ (l : List Bool) (k : ℕ), (W2 ++ l).getD (4 * n - 8 + k) false = l.getD k false := by
    intro l k
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega
  have gz : ∀ (l : List Bool), (W2 ++ l).getD (4 * n - 8) false = l.getD 0 false := by
    intro l; have := gr l 0; simpa using this
  simp only [tail, step, val, List.foldl_cons, List.foldl_nil, List.append_assoc, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil]
  have gR : ∀ (l : List Bool), (W2 ++ l).getD (rW n) false = W2.getD (rW n) false :=
    fun l => List.getD_append _ _ _ _ (by rw [l2]; unfold rW; split <;> omega)
  have gC : ∀ (l : List Bool), (W2 ++ l).getD (cW n) false = W2.getD (cW n) false :=
    fun l => List.getD_append _ _ _ _ (by rw [l2]; unfold cW; split <;> omega)
  simp only [gR, gC]
  simp (disch := omega) only [gl]
  simp only [gr, gz, List.getD_cons_zero, List.getD_cons_succ, g0, ga, gb, gn, gn1, gn2, rA, cA,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
    Bool.or_false]

theorem gx (n : ℕ) (u v : Fin n) (a : ℕ) (ha : a < n) :
    (oneEach u v).getD a false = decide (a = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha, Fin.ext_iff]

theorem gy (n : ℕ) (u v : Fin n) (b : ℕ) (hb : b < n) :
    (oneEach u v).getD (n + b) false = decide (b = v.val) := by
  unfold oneEach
  rw [get_right _ _ _ b (by simp)]
  simp [List.getD_eq_getElem?_getD, hb, Fin.ext_iff]

theorem anyB_eq_x (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k + 1 ≤ n) :
    anyB (oneEach u v) 1 k = decide (1 ≤ u.val ∧ u.val < k + 1) := by
  unfold anyB
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have := List.mem_range.1 hi
    rw [gx n u v (1 + i) (by omega), decide_eq_true_iff] at h
    omega
  · intro h
    exact ⟨u.val - 1, List.mem_range.2 (by omega), by rw [gx n u v _ (by omega)]; simp; omega⟩

theorem anyB_eq_y (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k + 3 ≤ n) :
    anyB (oneEach u v) (n + 3) k = decide (3 ≤ v.val ∧ v.val < k + 3) := by
  unfold anyB
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have := List.mem_range.1 hi
    rw [Nat.add_assoc, gy n u v (3 + i) (by omega), decide_eq_true_iff] at h
    omega
  · intro h
    exact ⟨v.val - 3, List.mem_range.2 (by omega), by rw [Nat.add_assoc, gy n u v _ (by omega)]; simp; omega⟩

end PEqualNP.Outside.L_meta_20577

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_20577 : (∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) (2 * n + 1)) := by
  intro n h4
  try simp only [PEqualNP.Represents.RepSizeAtMost]
  refine ⟨PEqualNP.Outside.L_meta_20577.circ n, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20577.circ, PEqualNP.Outside.L_meta_20577.tail,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [PEqualNP.Outside.L_meta_20577.cG]
  · show (PEqualNP.Outside.L_meta_20577.circ n).gates.length ≤ _
    simp [PEqualNP.Outside.L_meta_20577.circ, PEqualNP.Outside.L_meta_20577.tail]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    rw [PEqualNP.Outside.L_meta_20577.eval_circ n h4 _ (by simp [PEqualNP.Represents.oneEach]; omega),
      PEqualNP.Outside.L_meta_20577.gx n u v 0 (by omega),
      PEqualNP.Outside.L_meta_20577.gx n u v (n - 2) (by omega),
      PEqualNP.Outside.L_meta_20577.gx n u v (n - 1) (by omega),
      PEqualNP.Outside.L_meta_20577.gy n u v 1 (by omega),
      PEqualNP.Outside.L_meta_20577.gy n u v 2 (by omega),
      PEqualNP.Outside.L_meta_20577.anyB_eq_x n u v _ (by omega),
      PEqualNP.Outside.L_meta_20577.anyB_eq_y n u v _ (by omega)]
    have g0 : (PEqualNP.Represents.oneEach u v).getD n false = decide (0 = v.val) := by
      have := PEqualNP.Outside.L_meta_20577.gy n u v 0 (by omega); simpa using this
    rw [g0, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    try simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true]
    first
      | omega
      | (constructor <;> intro h <;> omega)
      | (split_ifs <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, not_not] <;> omega)
