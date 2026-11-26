import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23951 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4958 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩,
       ⟨.and, [0, 5]⟩, ⟨.and, [2, 7]⟩, ⟨.not, [9]⟩,
       ⟨.and, [6, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
