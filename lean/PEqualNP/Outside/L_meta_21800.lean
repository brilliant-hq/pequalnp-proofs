import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21800.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [10, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_21800.Helpers

theorem PEqualNP.Outside.L_meta_21800 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266974 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21800.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21800.Helpers.witness]
