import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20846 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (33554431 : ℕ).testBit (5 * u.val + v.val)) 4 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 2]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> subst h <;> exact ⟨by simp, by decide⟩
  · decide
  · decide
