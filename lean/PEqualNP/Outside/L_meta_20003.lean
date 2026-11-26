import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20003 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [37, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩], 42⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
