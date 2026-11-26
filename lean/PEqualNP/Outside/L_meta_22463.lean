import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22463.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [1, 16]⟩, ⟨GateOp.not, [17]⟩, ⟨GateOp.and, [15, 18]⟩, ⟨GateOp.and, [14, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22463.Helpers

theorem PEqualNP.Outside.L_meta_22463 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18089 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22463.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22463.Helpers.witness]
