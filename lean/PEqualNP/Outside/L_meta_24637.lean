import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24637_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844477 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24637_aux

theorem PEqualNP.Outside.L_meta_24637 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844477 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24637_aux.main
