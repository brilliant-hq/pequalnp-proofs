import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
