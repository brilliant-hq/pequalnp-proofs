import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20786 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 16 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
