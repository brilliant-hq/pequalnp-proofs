import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21739.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.and, [7, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_21739.Helpers

theorem PEqualNP.Outside.L_meta_21739 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266462 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21739.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21739.Helpers.witness]
