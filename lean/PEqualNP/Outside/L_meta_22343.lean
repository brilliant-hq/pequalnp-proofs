import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22343.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.not, [17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22343.Helpers

theorem PEqualNP.Outside.L_meta_22343 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33953 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22343.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22343.Helpers.witness]
