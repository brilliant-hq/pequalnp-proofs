import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19156_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem len (n : ℕ) (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

theorem left (n : ℕ) (u v i : Fin n) : (oneEach u v).getD i.val false = decide (i = u) := by
  have h : i.val < (List.ofFn (fun k : Fin n => decide (k = u))).length := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  simp

theorem right (n : ℕ) (u v j : Fin n) : (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  have h : (List.ofFn (fun k : Fin n => decide (k = u))).length ≤ n + j.val := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right h]
  simp

theorem snoc (l : List Bool) (a : Bool) (k : ℕ) (h : l.length = k) : (l ++ [a]).getD k false = a := by
  subst h
  simp

/-- NOT (x_i OR y_j): the OR is wire 2n, the NOT is wire 2n + 1. -/
theorem main (n : ℕ) (i j : Fin n) : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 2 ∧
    Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) C := by
  refine ⟨⟨[⟨.or, [i.val, n + j.val]⟩, ⟨.not, [2 * n]⟩], 2 * n + 1⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · simp [Circuit.size]
  · intro u v
    have hl := len n u v
    have hl1 : ∀ a : Bool, (oneEach u v ++ [a]).length = 2 * n + 1 := by
      intro a
      simp [hl]
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons,
      List.map_nil, GateOp.eval, List.any_cons, List.any_nil, List.headD_cons, id_eq, Bool.or_false]
    rw [snoc _ _ (2 * n + 1) (hl1 _), snoc _ _ (2 * n) hl, left, right]
    by_cases h1 : i = u <;> by_cases h2 : j = v <;> simp [h1, h2, Ne.symm (a := i), Ne.symm (a := j)]

end PEqualNP.Outside.L_meta_19156_aux

theorem PEqualNP.Outside.L_meta_19156 : ∀ (n : ℕ) (i j : Fin n), ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) C :=
  PEqualNP.Outside.L_meta_19156_aux.main
