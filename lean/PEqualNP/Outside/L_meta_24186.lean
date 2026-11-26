import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24186.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_24186.Helpers

theorem PEqualNP.Outside.L_meta_24186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266774 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24186.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24186.Helpers.witness]
