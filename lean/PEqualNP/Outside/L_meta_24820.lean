import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
private def circuit24820 : Circuit where
  gates := [
    ⟨.not, [4]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [12, 13]⟩
  ]
  output := 14

theorem PEqualNP.Outside.L_meta_24820 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148143 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit24820, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit24820, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
