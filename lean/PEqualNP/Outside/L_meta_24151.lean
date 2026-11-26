import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24151.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_24151.Helpers

theorem PEqualNP.Outside.L_meta_24151 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4442 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24151.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24151.Helpers.witness]
