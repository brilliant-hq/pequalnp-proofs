import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24146.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24146.Helpers

theorem PEqualNP.Outside.L_meta_24146 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283550 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24146.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24146.Helpers.witness]
