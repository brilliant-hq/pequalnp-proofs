import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22238.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [13, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22238.Helpers

theorem PEqualNP.Outside.L_meta_22238 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18094 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22238.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22238.Helpers.witness]
