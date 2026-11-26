import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22013.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_22013.Helpers

theorem PEqualNP.Outside.L_meta_22013 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18220 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22013.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22013.Helpers.witness]
