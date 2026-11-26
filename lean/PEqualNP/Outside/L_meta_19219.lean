import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19219_aux

def termGate (n k : ℕ) : Gate := ⟨.and, [k, n+k]⟩

def gates (n : ℕ) : ℕ → List Gate
  | 0 => [termGate n 0]
  | k+1 => gates n k ++ [termGate n (k+1), ⟨.or, [2*n+2*k, 2*n+2*k+1]⟩]

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem sizeG (n k : ℕ) : (gates n k).length = 2*k+1 := by
  induction k with
  | zero => simp [gates]
  | succ k ih => simp [gates, ih]; omega

theorem monoG (n k : ℕ) : ∀ g ∈ gates n k,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [gates, termGate]
  | succ k ih =>
    intro g hg
    simp only [gates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp [termGate]
    · simp

theorem snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem preservesInput (gs : List Gate) (x : List Bool) :
    ∃ ys, gs.foldl step x = x ++ ys ∧ ys.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], by simp, rfl⟩
  | append_singleton gs g ih =>
    obtain ⟨ys, h, hl⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, h]
    exact ⟨_, List.append_assoc .., by simp [hl]⟩

theorem bit {n : ℕ} (u v : Fin n) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem value {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    ((gates n k).foldl step (oneEach u v)).getD (2*n+2*k) false = true ↔
      u.val = v.val ∧ u.val ≤ k := by
  have hx : (oneEach u v).length = 2*n := by simp [oneEach]; omega
  induction k with
  | zero =>
    change ((oneEach u v) ++ [_]).getD _ false = true ↔ _
    rw [snoc, hx]
    simp only [Nat.mul_zero, Nat.add_zero, lt_irrefl, if_false, ↓reduceIte]
    change ((oneEach u v).getD 0 false && ((oneEach u v).getD (n+0) false && true)) = true ↔ _
    simp only [Bool.and_true, Bool.and_eq_true, bit, Nat.add_zero]
    omega
  | succ k ih =>
    let w := (gates n k).foldl step (oneEach u v)
    obtain ⟨ys, hy, hl⟩ := preservesInput (gates n k) (oneEach u v)
    have hw : w.length = 2*n+2*k+1 := by simp [w, hy, hx, hl, sizeG, Nat.add_assoc]
    have hi (j : ℕ) (hj : j < 2*n) : w.getD j false = (oneEach u v).getD j false := by
      simp only [w, hy, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega : j < (oneEach u v).length)]
    have ih' := ih (by omega : k < n)
    change w.getD (2*n+2*k) false = true ↔ _ at ih'
    let b := w.getD (k+1) false && w.getD (n+(k+1)) false
    have hb : b = true ↔ u.val = k+1 ∧ v.val = k+1 := by
      simp only [b, Bool.and_eq_true, hi _ (by omega : k+1 < 2*n),
        hi _ (by omega : n+(k+1) < 2*n), bit]
      omega
    simp only [gates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have firstStep : step w (termGate n (k+1)) = w ++ [b] := by
      simp [step, termGate, GateOp.eval, b]
    change (step (step w (termGate n (k+1))) _).getD _ false = true ↔ _
    rw [firstStep]
    change ((w ++ [b]) ++ [_]).getD _ false = true ↔ _
    rw [snoc]
    simp only [List.length_append, List.length_singleton, hw]
    have he : 2*n+2*(k+1) = 2*n+2*k+1+1 := by omega
    simp only [he, lt_irrefl, if_false, ↓reduceIte]
    change ((w ++ [b]).getD (2*n+2*k) false || ((w ++ [b]).getD (2*n+2*k+1) false || false)) = true ↔ _
    simp only [snoc, hw, Nat.lt_succ_self, if_true, lt_irrefl, if_false, ↓reduceIte,
      Bool.or_false, Bool.or_eq_true, ih', hb]
    omega

end PEqualNP.Outside.L_meta_19219_aux

open PEqualNP.Outside.L_meta_19219_aux

theorem PEqualNP.Outside.L_meta_19219 : (∀ (n : ℕ), 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u.val = v.val ∧ u.val + 1 < n)) (2 * n - 3)) := by
  intro n hn
  let k := n-2
  refine ⟨⟨gates n k, 2*n+2*k⟩, monoG n k, ?_, ?_⟩
  · change (gates n k).length ≤ _
    rw [sizeG]; dsimp [k]; omega
  · intro u v
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact (value u v k (by dsimp [k]; omega)).trans (by dsimp [k]; omega)
