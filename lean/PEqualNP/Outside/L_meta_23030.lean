import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23030

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

private theorem fit : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23030

open PEqualNP.Outside.L_meta_23030 in
theorem PEqualNP.Outside.L_meta_23030 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
