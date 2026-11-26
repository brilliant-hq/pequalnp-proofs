import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19090 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
