import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_19877 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6455152135695128040 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨(⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 20]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 20]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 22]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 23]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 32]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 25]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 26]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 27]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 28]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 29]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 30]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩], 45⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro gate hgate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
