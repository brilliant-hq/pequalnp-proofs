import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23104.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_23104.Helpers

theorem PEqualNP.Outside.L_meta_23104 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6127 : ℕ).testBit (6 * u.val + v.val)) 8 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23104.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23104.Helpers.witness]
