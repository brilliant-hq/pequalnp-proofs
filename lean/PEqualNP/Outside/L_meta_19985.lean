import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19985 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [36, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [39, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 39]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
