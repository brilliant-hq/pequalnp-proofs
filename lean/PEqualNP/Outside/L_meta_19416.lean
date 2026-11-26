import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19416 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 3, 3, 2] u)) 6 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 7]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h <;> subst h <;> exact ⟨by simp, by decide⟩
  · decide
  · decide
