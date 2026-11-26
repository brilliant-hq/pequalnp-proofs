import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19614 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3574717 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 16] }], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
