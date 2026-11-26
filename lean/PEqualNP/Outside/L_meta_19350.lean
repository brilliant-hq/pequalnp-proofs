import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19350 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7571262 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

