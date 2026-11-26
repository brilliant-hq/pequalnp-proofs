import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22224.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.or, [5, 18]⟩, ⟨GateOp.or, [13, 19]⟩, ⟨GateOp.and, [17, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22224.Helpers

theorem PEqualNP.Outside.L_meta_22224 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849711 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22224.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22224.Helpers.witness]
