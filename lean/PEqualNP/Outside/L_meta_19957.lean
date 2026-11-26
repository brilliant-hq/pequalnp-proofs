import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19957 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
