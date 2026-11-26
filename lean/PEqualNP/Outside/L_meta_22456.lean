import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22456.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [9, 16]⟩, ⟨GateOp.and, [14, 17]⟩, ⟨GateOp.or, [8, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22456.Helpers

theorem PEqualNP.Outside.L_meta_22456 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20030 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22456.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22456.Helpers.witness]
