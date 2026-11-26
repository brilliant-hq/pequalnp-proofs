import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19069 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (382 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 12] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
