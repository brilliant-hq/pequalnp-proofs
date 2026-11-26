import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21422 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112380 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 20]⟩], 21⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
