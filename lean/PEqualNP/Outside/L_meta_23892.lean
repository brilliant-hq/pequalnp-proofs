import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23892.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 7-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [6, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_23892.Helpers

theorem PEqualNP.Outside.L_meta_23892 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25374 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23892.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_23892.Helpers.witness]
