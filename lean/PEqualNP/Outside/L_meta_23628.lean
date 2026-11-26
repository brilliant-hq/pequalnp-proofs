import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23628 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274873 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 19]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
