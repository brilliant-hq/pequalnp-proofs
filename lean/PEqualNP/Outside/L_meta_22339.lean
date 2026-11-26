import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22339.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.and, [7, 15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22339.Helpers

theorem PEqualNP.Outside.L_meta_22339 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20028 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22339.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22339.Helpers.witness]
