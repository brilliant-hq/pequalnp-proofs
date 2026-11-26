import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23852.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [10, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_23852.Helpers

theorem PEqualNP.Outside.L_meta_23852 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881579 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23852.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23852.Helpers.witness]
