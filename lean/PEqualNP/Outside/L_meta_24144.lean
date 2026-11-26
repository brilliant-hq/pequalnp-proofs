import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24144.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24144.Helpers

theorem PEqualNP.Outside.L_meta_24144 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283358 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24144.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24144.Helpers.witness]
