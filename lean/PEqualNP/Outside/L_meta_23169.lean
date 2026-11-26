import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23169.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [15, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_23169.Helpers

theorem PEqualNP.Outside.L_meta_23169 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32378 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23169.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23169.Helpers.witness]
