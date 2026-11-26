import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21389 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (111286 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
