import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26275 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 3, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
