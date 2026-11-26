import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22094.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [8, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22094.Helpers

theorem PEqualNP.Outside.L_meta_22094 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17173 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22094.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22094.Helpers.witness]
