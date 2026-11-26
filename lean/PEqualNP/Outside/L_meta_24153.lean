import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24153.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [6, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_24153.Helpers

theorem PEqualNP.Outside.L_meta_24153 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12633 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24153.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24153.Helpers.witness]
