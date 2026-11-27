import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25941 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i < 4 + 4, g.inputs = [i]) ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 2, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_, by decide +kernel⟩
  all_goals
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
