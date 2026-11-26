import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25235_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem rowVal {n : ℕ} (u i v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem colVal {n : ℕ} (u v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_25235_aux

open PEqualNP.Outside.L_meta_25235_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25235 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val ≤ 1))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [n, 1]⟩, ⟨.or, [n + 1, 0]⟩, ⟨.or, [n + n + 1, n]⟩,
    ⟨.and, [n + n + 1, n + n]⟩, ⟨.not, [n + n + 3]⟩,
    ⟨.and, [n + n + 4, n + n + 2]⟩], n + n + 5⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have hr₀ : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using rowVal u ⟨0, by omega⟩ v
    have hr₁ : (PEqualNP.Represents.oneEach u v).getD 1 false = decide (u.val = 1) := by
      simpa [Fin.ext_iff] using rowVal u ⟨1, by omega⟩ v
    have hc₀ : (PEqualNP.Represents.oneEach u v).getD n false = decide (v.val = 0) := by
      simpa [Fin.ext_iff] using colVal u v ⟨0, by omega⟩
    have hc₁ : (PEqualNP.Represents.oneEach u v).getD (n + 1) false = decide (v.val = 1) := by
      simpa [Fin.ext_iff] using colVal u v ⟨1, by omega⟩
    generalize PEqualNP.Represents.oneEach u v = l at hl hr₀ hr₁ hc₀ hc₁
    have i₀ : 0 < l.length := by omega
    have i₁ : 1 < l.length := by omega
    have i₂ : n < l.length := by omega
    have i₃ : n + 1 < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at hr₀ hr₁ hc₀ hc₁
    rw [show n + n = l.length from hl.symm]
    simp only [Circuit.eval, Circuit.wires, List.foldl, List.map, List.getD_eq_getElem?_getD,
      List.append_assoc, List.cons_append, List.nil_append, List.getElem?_append_left i₀,
      List.getElem?_append_left i₁, List.getElem?_append_left i₂, List.getElem?_append_left i₃,
      hr₀, hr₁, hc₀, hc₁, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, GateOp.eval]
    simp
    by_cases a : u.val = 0 <;> by_cases b : u.val = 1 <;> by_cases c : v.val = 0 <;>
      by_cases d : v.val = 1 <;> simp [a, b, c, d] <;> omega
