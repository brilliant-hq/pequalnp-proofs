import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24155.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [10, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_24155.Helpers

theorem PEqualNP.Outside.L_meta_24155 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12889 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24155.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24155.Helpers.witness]
