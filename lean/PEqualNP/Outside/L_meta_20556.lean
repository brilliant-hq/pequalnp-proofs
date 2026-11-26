import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20556

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

def rW (n : ℕ) : ℕ := if n = 3 then 2 else 3 * n - 4

def cW (n : ℕ) : ℕ := if n = 3 then n + 2 else 4 * n - 7

def tail (n : ℕ) : List Gate :=
  [⟨.or, [rW n, cW n]⟩, ⟨.and, [0, n + 1]⟩, ⟨.and, [1, n]⟩, ⟨.or, [4 * n - 6, 4 * n - 6 + 1]⟩,
    ⟨.or, [4 * n - 6 + 3, 4 * n - 6 + 2]⟩]

def circ (n : ℕ) : Circuit :=
  ⟨(List.range (n - 3)).map (cG 2 (2 * n)) ++ (List.range (n - 3)).map (cG (n + 2) (3 * n - 3)) ++
    tail n, 4 * n - 6 + 4⟩

def c2 : Circuit := ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩

def anyB (X : List Bool) (b k : ℕ) : Bool := (List.range k).any fun i => X.getD (b + i) false

theorem eval_circ (n : ℕ) (hn : 3 ≤ n) (X : List Bool) (hX : X.length = 2 * n) :
    (circ n).eval X =
      (((anyB X 2 (n - 2) || anyB X (n + 2) (n - 2)) || (X.getD 0 false && X.getD (n + 1) false)) ||
        (X.getD 1 false && X.getD n false)) := by
  have e1 := chain 2 (2 * n) X hX (n - 3) (by omega)
  set W1 := X ++ (List.range (n - 3)).map
      (fun j => (List.range (j + 2)).any fun i => X.getD (2 + i) false) with hW1
  have l1 : W1.length = 3 * n - 3 := by simp [hW1, hX]; omega
  have e2 := chain (n + 2) (3 * n - 3) W1 l1 (n - 3) (by omega)
  set W2 := W1 ++ (List.range (n - 3)).map
      (fun j => (List.range (j + 2)).any fun i => W1.getD (n + 2 + i) false) with hW2
  have l2 : W2.length = 4 * n - 6 := by simp [hW2, l1]; omega
  have x2 : ∀ i, i < 2 * n → W2.getD i false = X.getD i false := by
    intro i hi
    rw [hW2, List.getD_append _ _ _ _ (by omega), hW1, List.getD_append _ _ _ _ (by omega)]
  have rA : W2.getD (rW n) false = anyB X 2 (n - 2) := by
    unfold rW
    by_cases h3 : n = 3
    · subst h3
      rw [if_pos rfl, x2 2 (by omega)]
      simp [anyB]
    rw [if_neg h3, hW2, List.getD_append _ _ _ _ (by omega), hW1,
      get_right _ _ _ (n - 4) (by omega), get_map_range (n - 3) (n - 4) _ (by omega)]
    have e : n - 4 + 2 = n - 2 := by omega
    rw [e]; rfl
  have cA : W2.getD (cW n) false = anyB X (n + 2) (n - 2) := by
    unfold cW
    by_cases h3 : n = 3
    · subst h3
      rw [if_pos rfl, x2 5 (by omega)]
      simp [anyB]
    rw [if_neg h3, hW2, get_right _ _ _ (n - 4) (by omega),
      get_map_range (n - 3) (n - 4) _ (by omega)]
    have e : n - 4 + 2 = n - 2 := by omega
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
  rw [hw, show (circ n).output = 4 * n - 6 + 4 from rfl]
  have g0 := x2 0 (by omega)
  have g1 := x2 1 (by omega)
  have gn := x2 n (by omega)
  have gn1 := x2 (n + 1) (by omega)
  have gl : ∀ (l : List Bool) (i : ℕ), i < 4 * n - 6 → (W2 ++ l).getD i false = W2.getD i false :=
    fun l i h => List.getD_append _ _ _ _ (by omega)
  have gr : ∀ (l : List Bool) (k : ℕ), (W2 ++ l).getD (4 * n - 6 + k) false = l.getD k false := by
    intro l k
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega
  have gz : ∀ (l : List Bool), (W2 ++ l).getD (4 * n - 6) false = l.getD 0 false := by
    intro l; have := gr l 0; simpa using this
  simp only [tail, step, val, List.foldl_cons, List.foldl_nil, List.append_assoc, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil]
  simp (disch := omega) only [gl]
  simp only [gr, gz, List.getD_cons_zero, List.getD_cons_succ, g0, g1, gn, gn1, rA, cA,
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

theorem anyB_eq_x (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k + 2 ≤ n) :
    anyB (oneEach u v) 2 k = decide (2 ≤ u.val ∧ u.val < k + 2) := by
  unfold anyB
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have := List.mem_range.1 hi
    rw [gx n u v (2 + i) (by omega), decide_eq_true_iff] at h
    omega
  · intro h
    exact ⟨u.val - 2, List.mem_range.2 (by omega), by rw [gx n u v _ (by omega)]; simp; omega⟩

theorem anyB_eq_y (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k + 2 ≤ n) :
    anyB (oneEach u v) (n + 2) k = decide (2 ≤ v.val ∧ v.val < k + 2) := by
  unfold anyB
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    have := List.mem_range.1 hi
    rw [Nat.add_assoc, gy n u v (2 + i) (by omega), decide_eq_true_iff] at h
    omega
  · intro h
    exact ⟨v.val - 2, List.mem_range.2 (by omega), by rw [Nat.add_assoc, gy n u v _ (by omega)]; simp; omega⟩

end PEqualNP.Outside.L_meta_20556

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_20556 : (∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) (2 * n - 1)) := by
  intro n h2
  try simp only [PEqualNP.Represents.RepSizeAtMost]
  rcases Nat.lt_or_ge n 3 with hlt | h3
  · obtain rfl : n = 2 := by omega
    refine ⟨PEqualNP.Outside.L_meta_20556.c2, ?_, by decide, by decide⟩
    intro g hg
    simp only [PEqualNP.Outside.L_meta_20556.c2, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  refine ⟨PEqualNP.Outside.L_meta_20556.circ n, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20556.circ, PEqualNP.Outside.L_meta_20556.tail,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) | rfl | rfl | rfl | rfl | rfl <;>
      simp [PEqualNP.Outside.L_meta_20556.cG]
  · show (PEqualNP.Outside.L_meta_20556.circ n).gates.length ≤ _
    simp [PEqualNP.Outside.L_meta_20556.circ, PEqualNP.Outside.L_meta_20556.tail]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    rw [PEqualNP.Outside.L_meta_20556.eval_circ n h3 _ (by simp [PEqualNP.Represents.oneEach]; omega),
      PEqualNP.Outside.L_meta_20556.gx n u v 0 (by omega),
      PEqualNP.Outside.L_meta_20556.gx n u v 1 (by omega),
      PEqualNP.Outside.L_meta_20556.gy n u v 1 (by omega),
      PEqualNP.Outside.L_meta_20556.anyB_eq_x n u v _ (by omega),
      PEqualNP.Outside.L_meta_20556.anyB_eq_y n u v _ (by omega)]
    have g0 : (PEqualNP.Represents.oneEach u v).getD n false = decide (0 = v.val) := by
      have := PEqualNP.Outside.L_meta_20556.gy n u v 0 (by omega); simpa using this
    rw [g0, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    try simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true]
    first
      | omega
      | (constructor <;> intro h <;> omega)
      | (split_ifs <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, not_not] <;> omega)
