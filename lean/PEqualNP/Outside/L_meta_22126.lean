import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22126 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837108 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide⟩
  · intro g hg
    simp only [PEqualNP.MetaComplexity.Monotone2, List.mem_cons, List.not_mem_nil,
      or_false] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
