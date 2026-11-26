import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22189.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [0, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22189.Helpers

theorem PEqualNP.Outside.L_meta_22189 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841663 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22189.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22189.Helpers.witness]
