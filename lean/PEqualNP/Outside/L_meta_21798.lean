import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21798 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266836 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [0, 6]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 1]⟩,
    ⟨.not, [10]⟩, ⟨.and, [4, 11]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [7, 9]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩,
    ⟨.not, [16]⟩
  ], 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
