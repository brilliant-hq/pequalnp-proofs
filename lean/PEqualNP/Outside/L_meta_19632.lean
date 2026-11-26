import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19632 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247802 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 8]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 5]⟩,
      ⟨.or, [6, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [13, 14]⟩,
      ⟨.or, [11, 12]⟩, ⟨.not, [15]⟩, ⟨.and, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
  · decide +kernel
