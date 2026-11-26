import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20421 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (863 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
