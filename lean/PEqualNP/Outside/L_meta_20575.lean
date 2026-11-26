import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20575

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ (n : ℕ) : Circuit :=
  ⟨[⟨.or, [n - 2, n - 1]⟩, ⟨.or, [0, n + n]⟩, ⟨.and, [n + n + 1, n + 2]⟩, ⟨.or, [n, n + 1]⟩, ⟨.or, [n + 2, n + n + 1]⟩, ⟨.not, [n + n + 4]⟩, ⟨.and, [n + n + 3, n + n]⟩, ⟨.or, [n + n + 6, n + n + 2]⟩, ⟨.or, [n + n + 7, n + n + 5]⟩], n + n + 8⟩

theorem rep (n : ℕ) (hn : 4 ≤ n) (u v : Fin n) :
    (circ n).eval (oneEach u v) = (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) u v := by
  have hu := u.isLt
  have hv := v.isLt
  have X : ∀ i, i < n → (oneEach u v).getD i false = decide (i = u.val) := by
    intro a ha
    unfold oneEach
    rw [List.getD_append _ _ _ _ (by simpa using ha)]
    simp [List.getD_eq_getElem?_getD, ha, Fin.ext_iff]
  have Y : ∀ b, b < n → (oneEach u v).getD (n + b) false = decide (b = v.val) := by
    intro b hb
    unfold oneEach
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, hb, Fin.ext_iff]
  have X0 := X (0) (by omega)
  have X1 := X (n - 2) (by omega)
  have X2 := X (n - 1) (by omega)
  have Y0 : (oneEach u v).getD n false = decide (0 = v.val) := by
    have := Y 0 (by omega); simpa using this
  have Y1 := Y (1) (by omega)
  have Y2 := Y (2) (by omega)
  have gl : ∀ (l : List Bool) (i : ℕ), i < n + n →
      (oneEach u v ++ l).getD i false = (oneEach u v).getD i false :=
    fun l i h => List.getD_append _ _ _ _ (by simp [oneEach]; omega)
  have gr : ∀ (l : List Bool) (k : ℕ), (oneEach u v ++ l).getD (n + n + k) false = l.getD k false := by
    intro l k
    rw [List.getD_append_right _ _ _ _ (by simp [oneEach])]
    congr 1
    simp [oneEach]
  have g0 : ∀ (l : List Bool), (oneEach u v ++ l).getD (n + n) false = l.getD 0 false := fun l => gr l 0
  simp only [Circuit.eval, Circuit.wires, circ, List.foldl_cons, List.foldl_nil, List.append_assoc,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  simp (disch := omega) only [gl]
  simp only [gr, g0, X0, X1, X2, Y0, Y1, Y2, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.all_cons,
    List.all_nil, List.any_cons, List.any_nil, List.headD_cons, id_eq, Bool.and_true, Bool.or_false]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  try simp only [Bool.not_eq_eq_eq_not, Bool.not_false, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  all_goals first
    | omega
    | (constructor <;> intro h <;> omega)
    | (split_ifs <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, not_not] <;> omega)

end PEqualNP.Outside.L_meta_20575

theorem PEqualNP.Outside.L_meta_20575 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨PEqualNP.Outside.L_meta_20575.circ n, ?_, by simp [PEqualNP.Outside.L_meta_20575.circ, PEqualNP.CircuitLowerBounds.Circuit.size], fun u v => PEqualNP.Outside.L_meta_20575.rep n hn u v⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_20575.circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
