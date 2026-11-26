import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20556_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem spec : ∀ (gs : List Gate) (x : List Bool) (val : ℕ → Bool),
    (∀ i, i < x.length → x.getD i false = val i) →
    (∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < x.length + j) →
    (∀ j (hj : j < gs.length), (gs[j]).op.eval ((gs[j]).inputs.map val) = val (x.length + j)) →
    ∀ i, i < x.length + gs.length → (gs.foldl step x).getD i false = val i := by
  intro gs
  induction gs with
  | nil => intro x val hx _ _ i hi; simpa using hx i (by simpa using hi)
  | cons g gs ih =>
    intro x val hx hr hv i hi
    simp only [List.foldl_cons]
    have hlen : (step x g).length = x.length + 1 := by simp [step]
    apply ih (step x g) val
    · intro i hi'
      rw [hlen] at hi'
      simp only [step, getD_snoc]
      split_ifs with h
      · subst h
        have h0 := hv 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        rw [← h0]
        congr 1
        apply List.map_congr_left
        intro k hk
        have := hr 0 (by simp) k (by simpa using hk)
        exact hx k (by simpa using this)
      · exact hx i (by omega)
    · intro j hj k hk
      have := hr (j + 1) (by simp; omega) k (by simpa using hk)
      rw [hlen]
      omega
    · intro j hj
      have := hv (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this, hlen]
      congr 1
      omega
    · rw [hlen]; simp at hi; omega

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def val (n u v i : ℕ) : Bool :=
  if i < 2 * n then decide (i = u ∨ i = n + v)
  else if i = 2 * n then decide (u = 0 ∧ v = 1)
  else if i = 2 * n + 1 then decide (u = 1 ∧ v = 0)
  else decide ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ u + 2 * n < i) ∨
    (2 ≤ v ∧ n + v + 2 * n < i + 2))

def gt (n j : ℕ) : Gate :=
  if j = 0 then ⟨GateOp.and, [0, n + 1]⟩
  else if j = 1 then ⟨GateOp.and, [1, n]⟩
  else if j = 2 then ⟨GateOp.or, [2 * n, 2 * n + 1]⟩
  else ⟨GateOp.or, [2 * n + j - 1, if j < n + 1 then j - 1 else j + 1]⟩

theorem gate_ok (n u v j : ℕ) (hn : 2 ≤ n) (hu : u < n) (hv : v < n) :
    (gt n j).op.eval ((gt n j).inputs.map (val n u v)) = val n u v (2 * n + j) := by
  rw [Bool.eq_iff_iff]
  unfold gt
  split_ifs <;> simp [GateOp.eval, val] <;> split_ifs <;> omega

end PEqualNP.Outside.L_meta_20556_aux

open PEqualNP.Outside.L_meta_20556_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_20556 : ∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) (2 * n - 1) := by
  intro n hn
  refine ⟨⟨(List.range (2 * n - 1)).map (gt n), 4 * n - 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨j, _, rfl⟩ := hg
    unfold gt
    split_ifs <;> simp
  · simp [Circuit.size]
  · intro u v
    have hx : (oneEach u v).length = 2 * n := by
      simp only [oneEach, List.length_append, List.length_ofFn]; omega
    have key := spec ((List.range (2 * n - 1)).map (gt n)) (oneEach u v) (val n u.val v.val) ?_ ?_ ?_
      (4 * n - 2) (by simp only [List.length_map, List.length_range]; omega)
    · simp only [Circuit.eval]
      change (List.foldl step _ _).getD _ _ = _
      rw [key]
      have := u.isLt; have := v.isLt
      rw [Bool.eq_iff_iff]
      simp [val, Fin.ext_iff]
      split_ifs <;> omega
    · intro i hi
      rw [hx] at hi
      rw [Bool.eq_iff_iff, oe]
      simp [val, hi]
    · intro j hj i hi
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range] at hi
      rw [hx]
      unfold gt at hi
      split_ifs at hi <;> simp at hi <;> omega
    · intro j hj
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range]
      rw [hx]
      exact gate_ok n u.val v.val j hn u.isLt v.isLt
