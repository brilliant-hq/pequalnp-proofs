import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22336.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22336.Helpers

theorem PEqualNP.Outside.L_meta_22336 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18360 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22336.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22336.Helpers.witness]
