import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18526

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  rcases Nat.lt_or_ge i w.length with h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; simp [List.getD_eq_getElem?_getD]
    · have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      simp only [h1, h2, if_false]
      rw [List.getD_eq_default]
      simp; omega

def rm {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (p ⟨i, h⟩ : ℕ) else i

theorem rm_lt {n : ℕ} (p : Fin n → Fin n) (i : ℕ) (h : i < n) : rm p i < n := by
  simp [rm, h]

theorem rm_ge {n : ℕ} (p : Fin n → Fin n) (i : ℕ) (h : ¬ i < n) : rm p i = i := by
  simp [rm, h]

theorem inv {n : ℕ} (p : Fin n → Fin n) : ∀ (gs : List Gate) (A B : List Bool), A.length = B.length → n ≤ B.length →
    (∀ i, B.getD (rm p i) false = A.getD i false) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A).length =
      ((gs.map (fun g => (⟨g.op, g.inputs.map (rm p)⟩ : Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) B).length ∧
    ∀ i, ((gs.map (fun g => (⟨g.op, g.inputs.map (rm p)⟩ : Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) B).getD (rm p i) false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A).getD i false
  | [], A, B, hl, hn, h => ⟨hl, h⟩
  | g :: gs, A, B, hl, hn, h => by
    simp only [List.foldl_cons, List.map_cons]
    have hv : g.op.eval ((g.inputs.map (rm p)).map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
      rw [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => h i)
    apply inv p gs
    · simp [hl]
    · simp; omega
    · intro i
      rw [hv, getD_snoc, getD_snoc]
      by_cases hi : i < n
      · have e := rm_lt p i hi
        rw [if_pos (by omega : rm p i < B.length), if_pos (by omega : i < A.length)]
        exact h i
      · have e := rm_ge p i hi
        rw [e]
        by_cases h1 : i < A.length
        · rw [if_pos (by omega), if_pos h1]; have := h i; rw [e] at this; exact this
        · by_cases h2 : i = A.length
          · rw [if_neg (by omega), if_pos (by omega), if_neg h1, if_pos h2]
          · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_18526

theorem PEqualNP.Outside.L_meta_18526 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool), x5.eval (List.ofFn x6) = x3.eval (List.ofFn (x6 ∘ x2)) := by
  intro x1 x2 x3 hf
  refine ⟨⟨x3.gates.map (fun g => ⟨g.op, g.inputs.map (L_meta_18526.rm x2)⟩), L_meta_18526.rm x2 x3.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hf g0 hg0).1, by simpa using (hf g0 hg0).2⟩
  · intro x6
    have h0 : ∀ i, (List.ofFn x6).getD (L_meta_18526.rm x2 i) false = (List.ofFn (x6 ∘ x2)).getD i false := by
      intro i
      by_cases hi : i < x1
      · have e := L_meta_18526.rm_lt x2 i hi
        rw [List.getD_eq_getElem _ _ (by simpa using e), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp [L_meta_18526.rm, hi]
      · rw [L_meta_18526.rm_ge x2 i hi]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact (L_meta_18526.inv x2 x3.gates (List.ofFn (x6 ∘ x2)) (List.ofFn x6) (by simp) (by simp) h0).2 x3.output
