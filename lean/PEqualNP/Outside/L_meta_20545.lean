import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20545_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_20545_aux

open PEqualNP.Outside.L_meta_20545_aux in
theorem PEqualNP.Outside.L_meta_20545 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) C := by
  intro n hn
  refine ⟨⟨[⟨.and, [0, n]⟩, ⟨.and, [1, n + 1]⟩, ⟨.or, [n + n, n + n + 1]⟩,
    ⟨.not, [n + n + 2]⟩], n + n + 3⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using gL u ⟨0, by omega⟩ v
    have h1 : (PEqualNP.Represents.oneEach u v).getD 1 false = decide (u.val = 1) := by
      simpa [Fin.ext_iff] using gL u ⟨1, by omega⟩ v
    have h2 : (PEqualNP.Represents.oneEach u v).getD n false = decide (v.val = 0) := by
      simpa [Fin.ext_iff] using gR u v ⟨0, by omega⟩
    have h3 : (PEqualNP.Represents.oneEach u v).getD (n + 1) false = decide (v.val = 1) := by
      simpa [Fin.ext_iff] using gR u v ⟨1, by omega⟩
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 h1 h2 h3
    have i0 : 0 < l.length := by omega
    have i1 : 1 < l.length := by omega
    have i2 : n < l.length := by omega
    have i3 : n + 1 < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append,
      List.nil_append, List.getElem?_append_left i0, List.getElem?_append_left i1,
      List.getElem?_append_left i2, List.getElem?_append_left i3, h0, h1, h2, h3,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    by_cases a : u.val = 0 <;> by_cases b : u.val = 1 <;> by_cases c : v.val = 0 <;>
      by_cases d : v.val = 1 <;> simp [a, b, c, d, Fin.ext_iff] <;> omega
