import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19109 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15838 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
