import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22458.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [9, 17]⟩, ⟨GateOp.and, [0, 18]⟩, ⟨GateOp.or, [15, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22458.Helpers

theorem PEqualNP.Outside.L_meta_22458 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16574 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22458.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22458.Helpers.witness]
