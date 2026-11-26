import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22454.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [8, 14]⟩, ⟨GateOp.and, [6, 15]⟩, ⟨GateOp.and, [2, 16]⟩, ⟨GateOp.or, [17, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22454.Helpers

theorem PEqualNP.Outside.L_meta_22454 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20024 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22454.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22454.Helpers.witness]
