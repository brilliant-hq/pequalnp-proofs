import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23162.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [2, 16]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [12, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_23162.Helpers

theorem PEqualNP.Outside.L_meta_23162 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (13182 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23162.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23162.Helpers.witness]
