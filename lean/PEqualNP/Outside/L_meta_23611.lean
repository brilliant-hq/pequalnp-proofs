import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23611 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272173 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
