import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20574

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dg : Gate := ⟨GateOp.or, []⟩

lemma fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl wstep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

lemma getD_app_left (x : List Bool) (v : Bool) (i : ℕ) (hi : i < x.length) :
    (x ++ [v]).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wstep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep x g) (by simp [wstep]; omega)]
    exact getD_app_left x _ i hi

lemma fold_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j) :
    (gs.foldl wstep x).getD (x.length + j) false =
      (gs.getD j dg).op.eval ((gs.getD j dg).inputs.map fun i => (gs.foldl wstep x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have hg : (g :: gs).getD 0 dg = g := rfl
      rw [hg] at hin ⊢
      rw [Nat.add_zero, fold_low gs (wstep x g) x.length (by simp [wstep])]
      have h1 : (wstep x g).getD x.length false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [wstep, List.getD_eq_getElem?_getD]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_low gs (wstep x g) i (by simp [wstep]; omega)]
      exact (getD_app_left x _ i (by omega)).symm
    | succ j =>
      have hg : (g :: gs).getD (j + 1) dg = gs.getD j dg := rfl
      rw [hg] at hin ⊢
      have hl : (wstep x g).length = x.length + 1 := by simp [wstep]
      have := ih (wstep x g) j (by simpa using hj) (by intro i hi; have := hin i hi; omega)
      rw [hl] at this
      rw [show x.length + (j + 1) = x.length + 1 + j by omega]
      exact this

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

lemma val_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    val C x w = x.getD w false :=
  fold_low C.gates x w hw

lemma val_and {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.and) :
    val C x (N + j) = (val C x p && val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.and := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma val_or {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.or) :
    val C x (N + j) = (val C x p || val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.or := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_get {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  unfold oneEach
  by_cases hw : w < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
    simp [hw, Fin.ext_iff]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hw)]
    by_cases hw2 : w - n < m
    · simp [hw2, Fin.ext_iff]
      omega
    · simp [hw2]
      omega


def G (n j : ℕ) : Gate :=
  if j < n - 2 then ⟨GateOp.or, [if j = 0 then 1 else 2 * n + j - 1, j + 2]⟩
  else if j < 2 * (n - 2) then
    ⟨GateOp.or, [if j = n - 2 then n + 1 else 2 * n + j - 1, n + (j - (n - 2)) + 2]⟩
  else if j = 2 * (n - 2) then ⟨GateOp.and, [0, n]⟩
  else if j = 2 * (n - 2) + 1 then
    ⟨GateOp.and, [if n = 2 then 1 else 3 * n - 3, if n = 2 then 3 else 4 * n - 5]⟩
  else ⟨GateOp.or, [4 * n - 4, 4 * n - 3]⟩

def Cn (n : ℕ) : Circuit :=
  { gates := List.ofFn (fun j : Fin (2 * n - 1) => G n j.val), output := 4 * n - 2 }

lemma gate_eq (n j : ℕ) (hj : j < 2 * n - 1) : gateAt (Cn n) j = G n j := by
  unfold gateAt Cn
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

lemma len_eq (n : ℕ) : (Cn n).gates.length = 2 * n - 1 := by simp [Cn]

lemma G_ok (n j : ℕ) : (G n j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (G n j).inputs.length ≤ 2 := by
  unfold G
  (repeat' split) <;> simp

lemma mono (n : ℕ) : Monotone2 (Cn n) := by
  intro g hg
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  exact G_ok n j.val

section
variable {n : ℕ} (u v : Fin n)

lemma inr (w : ℕ) (hw : w < n) : val (Cn n) (oneEach u v) w = decide (w = u.val) := by
  rw [val_input _ _ w (by rw [oneEach_len]; omega), Bool.eq_iff_iff, oneEach_get]
  simp
  omega

lemma inc (w : ℕ) (hw : w < n) : val (Cn n) (oneEach u v) (n + w) = decide (w = v.val) := by
  rw [val_input _ _ (n + w) (by rw [oneEach_len]; omega), Bool.eq_iff_iff, oneEach_get]
  simp
  omega

lemma rchain (j : ℕ) (hj : j < n - 2) :
    val (Cn n) (oneEach u v) (n + n + j) = decide (1 ≤ u.val ∧ u.val ≤ j + 2) := by
  induction j with
  | zero =>
    have hg : (gateAt (Cn n) 0) = ⟨GateOp.or, [1, 2]⟩ := by
      rw [gate_eq n 0 (by omega)]; simp [G, hj]
    rw [val_or (N := n + n) _ (oneEach_len u v) 0 (by rw [len_eq]; omega) 1 2 (by rw [hg]) (by omega) (by omega)
      (by rw [hg]), inr u v 1 (by omega), inr u v 2 (by omega), Bool.eq_iff_iff]
    simp
    omega
  | succ j ih =>
    have hg : (gateAt (Cn n) (j + 1)) = ⟨GateOp.or, [n + n + j, j + 3]⟩ := by
      rw [gate_eq n (j + 1) (by omega)]
      simp only [G, hj, ite_true]
      simp
      omega
    rw [val_or (N := n + n) _ (oneEach_len u v) (j + 1) (by rw [len_eq]; omega) (n + n + j) (j + 3) (by rw [hg])
      (by omega) (by omega) (by rw [hg]), ih (by omega), inr u v (j + 3) (by omega), Bool.eq_iff_iff]
    simp
    omega

lemma kchain (i : ℕ) (hi : i < n - 2) :
    val (Cn n) (oneEach u v) (n + n + (n - 2 + i)) = decide (1 ≤ v.val ∧ v.val ≤ i + 2) := by
  induction i with
  | zero =>
    have hg : (gateAt (Cn n) (n - 2 + 0)) = ⟨GateOp.or, [n + 1, n + 2]⟩ := by
      rw [gate_eq n (n - 2 + 0) (by omega)]
      have h1 : ¬ (n - 2 + 0 < n - 2) := by omega
      have h2 : n - 2 + 0 < 2 * (n - 2) := by omega
      simp only [G, h1, h2, ite_true, ite_false]
      simp
    rw [val_or (N := n + n) _ (oneEach_len u v) (n - 2 + 0) (by rw [len_eq]; omega) (n + 1) (n + 2) (by rw [hg])
      (by omega) (by omega) (by rw [hg]), inc u v 1 (by omega), inc u v 2 (by omega), Bool.eq_iff_iff]
    simp
    omega
  | succ i ih =>
    have hg : (gateAt (Cn n) (n - 2 + (i + 1))) = ⟨GateOp.or, [n + n + (n - 2 + i), n + (i + 3)]⟩ := by
      rw [gate_eq n (n - 2 + (i + 1)) (by omega)]
      have h1 : ¬ (n - 2 + (i + 1) < n - 2) := by omega
      have h2 : n - 2 + (i + 1) < 2 * (n - 2) := by omega
      have h3 : ¬ (n - 2 + (i + 1) = n - 2) := by omega
      simp only [G, h1, h2, h3, ite_true, ite_false]
      simp
      omega
    rw [val_or (N := n + n) _ (oneEach_len u v) (n - 2 + (i + 1)) (by rw [len_eq]; omega) (n + n + (n - 2 + i))
      (n + (i + 3)) (by rw [hg]) (by omega) (by omega) (by rw [hg]), ih (by omega), inc u v (i + 3) (by omega),
      Bool.eq_iff_iff]
    simp
    omega

lemma rep (hn : 2 ≤ n) : (Cn n).eval (oneEach u v) = decide ((u.val = 0 ∧ v.val = 0) ∨ (u.val ≠ 0 ∧ v.val ≠ 0)) := by
  have hlen := len_eq n
  have hx := oneEach_len u v
  have hr : val (Cn n) (oneEach u v) (if n = 2 then 1 else 3 * n - 3) = decide (1 ≤ u.val) := by
    by_cases h2 : n = 2
    · rw [if_pos h2, inr u v 1 (by omega), Bool.eq_iff_iff]
      simp
      omega
    · rw [if_neg h2, show 3 * n - 3 = n + n + (n - 3) by omega, rchain u v (n - 3) (by omega), Bool.eq_iff_iff]
      simp
      omega
  have hk : val (Cn n) (oneEach u v) (if n = 2 then 3 else 4 * n - 5) = decide (1 ≤ v.val) := by
    by_cases h2 : n = 2
    · have := inc u v 1 (by omega)
      rw [if_pos h2, show (3 : ℕ) = n + 1 by omega, this, Bool.eq_iff_iff]
      simp
      omega
    · rw [if_neg h2, show 4 * n - 5 = n + n + (n - 2 + (n - 3)) by omega, kchain u v (n - 3) (by omega),
        Bool.eq_iff_iff]
      simp
      omega
  have ga : gateAt (Cn n) (2 * (n - 2)) = ⟨GateOp.and, [0, n]⟩ := by
    rw [gate_eq n _ (by omega)]
    unfold G
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have gb : gateAt (Cn n) (2 * (n - 2) + 1) =
      ⟨GateOp.and, [if n = 2 then 1 else 3 * n - 3, if n = 2 then 3 else 4 * n - 5]⟩ := by
    rw [gate_eq n _ (by omega)]
    unfold G
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have gc : gateAt (Cn n) (2 * (n - 2) + 2) = ⟨GateOp.or, [4 * n - 4, 4 * n - 3]⟩ := by
    rw [gate_eq n _ (by omega)]
    unfold G
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have h0 := inc u v 0 (by omega)
  rw [Nat.add_zero] at h0
  have ha : val (Cn n) (oneEach u v) (n + n + 2 * (n - 2)) = (decide (0 = u.val) && decide (0 = v.val)) := by
    rw [val_and (N := n + n) _ hx (2 * (n - 2)) (by omega) 0 n (by rw [ga]) (by omega) (by omega) (by rw [ga]),
      inr u v 0 (by omega), h0]
  have hb : val (Cn n) (oneEach u v) (n + n + (2 * (n - 2) + 1)) = (decide (1 ≤ u.val) && decide (1 ≤ v.val)) := by
    rw [val_and (N := n + n) _ hx (2 * (n - 2) + 1) (by omega) _ _ (by rw [gb])
      (by split_ifs <;> omega) (by split_ifs <;> omega) (by rw [gb]), hr, hk]
  have hc : val (Cn n) (oneEach u v) (n + n + (2 * (n - 2) + 2)) =
      ((decide (0 = u.val) && decide (0 = v.val)) || (decide (1 ≤ u.val) && decide (1 ≤ v.val))) := by
    rw [val_or (N := n + n) _ hx (2 * (n - 2) + 2) (by omega) (4 * n - 4) (4 * n - 3) (by rw [gc]) (by omega)
      (by omega) (by rw [gc]), show 4 * n - 4 = n + n + 2 * (n - 2) by omega,
      show 4 * n - 3 = n + n + (2 * (n - 2) + 1) by omega, ha, hb]
  have he : (Cn n).eval (oneEach u v) = val (Cn n) (oneEach u v) (n + n + (2 * (n - 2) + 2)) := by
    show ((Cn n).wires (oneEach u v)).getD (4 * n - 2) false = _
    rw [show 4 * n - 2 = n + n + (2 * (n - 2) + 2) by omega]
    rfl
  rw [he, hc, Bool.eq_iff_iff]
  simp
  omega

end

end PEqualNP.Outside.L_meta_20574

theorem PEqualNP.Outside.L_meta_20574 : ∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 0) ∨ (u.val ≠ 0 ∧ v.val ≠ 0))) (2 * n - 1) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_20574.Cn n, PEqualNP.Outside.L_meta_20574.mono n,
    by simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_20574.Cn],
    fun u v => PEqualNP.Outside.L_meta_20574.rep u v hn⟩
