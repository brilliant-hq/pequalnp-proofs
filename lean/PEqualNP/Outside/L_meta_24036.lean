import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24036.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [5, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24036.Helpers

theorem PEqualNP.Outside.L_meta_24036 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4378 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24036.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24036.Helpers.witness]
