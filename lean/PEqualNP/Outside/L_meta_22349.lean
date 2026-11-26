import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22349.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.not, [16]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [8, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22349.Helpers

theorem PEqualNP.Outside.L_meta_22349 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17048 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22349.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22349.Helpers.witness]
