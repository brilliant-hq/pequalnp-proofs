import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20424.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 5-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..6 the right vertex;
gate `j` writes wire `7 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [7, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_20424.Helpers

theorem PEqualNP.Outside.L_meta_20424 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (895 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20424.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20424.Helpers.witness]
