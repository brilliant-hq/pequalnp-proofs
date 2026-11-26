import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24153
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [7, 5]⟩,
    ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_24153

open PEqualNP.Outside.L_meta_24153 in
theorem PEqualNP.Outside.L_meta_24153 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12633 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
