import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22457.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.and, [17, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22457.Helpers

theorem PEqualNP.Outside.L_meta_22457 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20153 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22457.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22457.Helpers.witness]
