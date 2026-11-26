import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24127.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24127.Helpers

theorem PEqualNP.Outside.L_meta_24127 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267165 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24127.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24127.Helpers.witness]
