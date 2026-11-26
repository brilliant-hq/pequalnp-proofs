import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23604 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271222 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
