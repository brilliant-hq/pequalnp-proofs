import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20408.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 4-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..6 the right vertex;
gate `j` writes wire `7 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [3, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_20408.Helpers

theorem PEqualNP.Outside.L_meta_20408 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (319 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20408.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20408.Helpers.witness]
