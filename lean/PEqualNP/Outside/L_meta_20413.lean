import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20413.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 6-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..6 the right vertex;
gate `j` writes wire `7 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_20413.Helpers

theorem PEqualNP.Outside.L_meta_20413 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_20413.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20413.Helpers.witness]
