import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22678.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [1, 15]⟩, ⟨GateOp.or, [6, 16]⟩, ⟨GateOp.or, [7, 17]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.and, [14, 18]⟩, ⟨GateOp.or, [0, 20]⟩, ⟨GateOp.or, [4, 21]⟩, ⟨GateOp.and, [19, 22]⟩], 23⟩

end PEqualNP.Outside.L_meta_22678.Helpers

theorem PEqualNP.Outside.L_meta_22678 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842998 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22678.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22678.Helpers.witness]
