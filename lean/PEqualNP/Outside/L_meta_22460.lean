import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22460.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.and, [9, 15]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.not, [18]⟩, ⟨GateOp.or, [16, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22460.Helpers

theorem PEqualNP.Outside.L_meta_22460 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17081 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22460.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22460.Helpers.witness]
