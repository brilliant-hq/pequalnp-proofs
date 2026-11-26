import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24502.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [9, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24502.Helpers

theorem PEqualNP.Outside.L_meta_24502 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147475 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24502.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24502.Helpers.witness]
