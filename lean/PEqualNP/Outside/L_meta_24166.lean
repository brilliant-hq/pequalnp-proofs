import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24166.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_24166.Helpers

theorem PEqualNP.Outside.L_meta_24166 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274966 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24166.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24166.Helpers.witness]
