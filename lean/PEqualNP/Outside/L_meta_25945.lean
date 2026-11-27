import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25945 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
