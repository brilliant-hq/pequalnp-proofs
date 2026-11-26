import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22346.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.not, [18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22346.Helpers

theorem PEqualNP.Outside.L_meta_22346 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16569 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22346.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22346.Helpers.witness]
