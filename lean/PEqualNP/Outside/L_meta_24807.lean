import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_24807 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147375 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo]
  · decide +kernel
