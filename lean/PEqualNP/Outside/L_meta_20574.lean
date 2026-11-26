import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20574_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def tl (n u v : ℕ) : ℕ → Bool
  | 0 => decide (u = 0 ∧ v = 0)
  | 1 => decide (1 ≤ u ∧ 1 ≤ v)
  | 2 => decide ((u = 0 ∧ v = 0) ∨ (u ≠ 0 ∧ v ≠ 0))
  | _ => false

def val (n u v k : ℕ) : Bool :=
  if k < n - 2 then decide (1 ≤ u ∧ u ≤ k + 2)
  else if k < 2 * (n - 2) then decide (1 ≤ v ∧ v ≤ k - (n - 2) + 2)
  else tl n u v (k - 2 * (n - 2))

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w) else if w < 2 * n then decide (v + n = w) else val n u v (w - 2 * n)

def xa (n k : ℕ) : ℕ := if k = 0 then 1 else 2 * n + k - 1
def ya (n k : ℕ) : ℕ := if k = n - 2 then n + 1 else 2 * n + k - 1

def gate (n k : ℕ) : Gate :=
  if k < n - 2 then ⟨GateOp.or, [xa n k, k + 2]⟩
  else if k < 2 * (n - 2) then ⟨GateOp.or, [ya n k, n + (k - (n - 2)) + 2]⟩
  else if k = 2 * (n - 2) then ⟨GateOp.and, [0, n]⟩
  else if k = 2 * (n - 2) + 1 then ⟨GateOp.and, [xa n (n - 2), ya n (2 * (n - 2))]⟩
  else ⟨GateOp.or, [2 * n + 2 * (n - 2), 2 * n + (2 * (n - 2) + 1)]⟩

theorem fX (n u v w : ℕ) (h : w < n) : f n u v w = decide (u = w) := by simp [f, h]

theorem fY (n u v w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) : f n u v w = decide (v + n = w) := by
  simp [f, h2, show ¬ w < n by omega]

theorem fG (n u v k : ℕ) : f n u v (2 * n + k) = val n u v k := by
  simp [f, show ¬ 2 * n + k < n by omega]

theorem vC (n u v k : ℕ) (h : k < n - 2) : val n u v k = decide (1 ≤ u ∧ u ≤ k + 2) := by simp [val, h]

theorem vR (n u v k : ℕ) (h1 : n - 2 ≤ k) (h2 : k < 2 * (n - 2)) :
    val n u v k = decide (1 ≤ v ∧ v ≤ k - (n - 2) + 2) := by
  simp [val, h2, show ¬ k < n - 2 by omega]

theorem vT (n u v k j : ℕ) (h : k = 2 * (n - 2) + j) : val n u v k = tl n u v j := by
  subst h; rw [val, ite_cond_eq_false _ _ (eq_false (by omega)), ite_cond_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]

theorem fA (n u v k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n - 2) : f n u v (xa n k) = decide (1 ≤ u ∧ u ≤ k + 1) := by
  unfold xa
  split_ifs with h
  · subst h; rw [fX n u v 1 (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vC n u v _ (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem fB (n u v k : ℕ) (hn : 2 ≤ n) (h1 : n - 2 ≤ k) (h2 : k ≤ 2 * (n - 2)) :
    f n u v (ya n k) = decide (1 ≤ v ∧ v ≤ k - (n - 2) + 1) := by
  unfold ya
  split_ifs with h
  · rw [fY n u v (n + 1) (by omega) (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vR n u v _ (by omega) (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem gate_ok (n u v k : ℕ) (hn : 2 ≤ n) (hu : u < n) (hv : v < n) (hk : k < 2 * n - 1) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u v)) = f n u v (2 * n + k) := by
  unfold gate
  split_ifs with h1 h2 h3 h4 <;> refine ⟨fun i hi => ?_, ?_⟩
  all_goals first
    | (simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
       rcases hi with rfl | rfl <;> (try simp only [xa, ya]) <;> (try split_ifs) <;> omega)
    | skip
  all_goals simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, fG]
  · rw [fA n u v k hn (by omega), fX n u v _ (by omega), vC n u v k h1]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fB n u v k hn (by omega) (by omega), fY n u v _ (by omega) (by omega), vR n u v k (by omega) h2]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fX n u v 0 (by omega), fY n u v n (by omega) (by omega), vT n u v k 0 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fA n u v _ hn le_rfl, fB n u v _ hn (by omega) le_rfl, vT n u v k 1 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [vT n u v _ 0 (by omega), vT n u v _ 1 rfl, vT n u v k 2 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega

end PEqualNP.Outside.L_meta_20574_aux

open PEqualNP.Outside.L_meta_20574_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20574 : ∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 0) ∨ (u.val ≠ 0 ∧ v.val ≠ 0))) (2 * n - 1) := by
  intro n hn
  refine ⟨⟨(List.range (2 * n - 1)).map (gate n), 2 * n + (2 * (n - 2) + 2)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
      simp [PEqualNP.Represents.oneEach]; omega
    have hx : ∀ i < (PEqualNP.Represents.oneEach u v).length,
        (PEqualNP.Represents.oneEach u v).getD i false = f n u v i := by
      intro i hi
      rw [hl] at hi
      apply Bool.eq_iff_iff.2
      simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, List.getElem?_ofFn, f]
      split_ifs <;> simp [Fin.ext_iff] <;> omega
    show (List.foldl stp (PEqualNP.Represents.oneEach u v) ((List.range (2 * n - 1)).map (gate n))).getD (2 * n + (2 * (n - 2) + 2)) false = _
    rw [spec (f n u v) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v k hn u.2 v.2 hk) _ (by simp [hl]; omega), fG, vT n u v _ 2 rfl]
    simp only [tl]
