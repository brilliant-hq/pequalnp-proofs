import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22462.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [5, 17]⟩, ⟨GateOp.and, [16, 18]⟩, ⟨GateOp.not, [19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22462.Helpers

theorem PEqualNP.Outside.L_meta_22462 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17084 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22462.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22462.Helpers.witness]
