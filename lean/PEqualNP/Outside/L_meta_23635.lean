import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23635 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275253 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 19]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
