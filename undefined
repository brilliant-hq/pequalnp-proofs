import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22185 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841532 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 19]⟩], 21⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
