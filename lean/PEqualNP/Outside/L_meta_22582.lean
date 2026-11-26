import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22582.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [10, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_22582.Helpers

theorem PEqualNP.Outside.L_meta_22582 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (412 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22582.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22582.Helpers.witness]
