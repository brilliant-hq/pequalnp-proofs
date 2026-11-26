import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24101.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24101.Helpers

theorem PEqualNP.Outside.L_meta_24101 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4371 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24101.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24101.Helpers.witness]
