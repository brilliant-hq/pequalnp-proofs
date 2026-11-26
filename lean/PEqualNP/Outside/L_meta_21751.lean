import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21751.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [10, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_21751.Helpers

theorem PEqualNP.Outside.L_meta_21751 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279454 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21751.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21751.Helpers.witness]
