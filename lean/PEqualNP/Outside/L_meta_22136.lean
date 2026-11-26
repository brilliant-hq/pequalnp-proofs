import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22136.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.and, [8, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [10, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22136.Helpers

theorem PEqualNP.Outside.L_meta_22136 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33713 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22136.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22136.Helpers.witness]
