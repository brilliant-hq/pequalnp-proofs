import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_19908 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17022383772369540555 : ℕ).testBit (8 * u.val + v.val)) 35) := by
  refine ⟨(⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 20]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 23]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 24]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 26]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 27]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 29]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 31]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 33]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 46]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 34]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 48]⟩], 49⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro gate hgate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
