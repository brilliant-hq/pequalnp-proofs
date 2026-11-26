import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21975.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_21975.Helpers

theorem PEqualNP.Outside.L_meta_21975 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (397 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21975.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21975.Helpers.witness]
