import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20426.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 6-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..6 the right vertex;
gate `j` writes wire `7 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [7, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_20426.Helpers

theorem PEqualNP.Outside.L_meta_20426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20426.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20426.Helpers.witness]
