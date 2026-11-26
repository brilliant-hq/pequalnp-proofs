import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22117.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [9, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22117.Helpers

theorem PEqualNP.Outside.L_meta_22117 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18235 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22117.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22117.Helpers.witness]
