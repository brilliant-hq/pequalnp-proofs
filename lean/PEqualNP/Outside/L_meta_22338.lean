import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22338.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [13, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22338.Helpers

theorem PEqualNP.Outside.L_meta_22338 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20027 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22338.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22338.Helpers.witness]
