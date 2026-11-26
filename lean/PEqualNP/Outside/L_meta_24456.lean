import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24456.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [8, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24456.Helpers

theorem PEqualNP.Outside.L_meta_24456 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24456.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24456.Helpers.witness]
