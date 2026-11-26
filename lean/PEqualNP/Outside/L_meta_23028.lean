import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_23028 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36150 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 8]⟩,
    ⟨.and, [7, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [11, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
