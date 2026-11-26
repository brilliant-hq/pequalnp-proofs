import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23984.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23984.Helpers

theorem PEqualNP.Outside.L_meta_23984 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13085 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23984.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_23984.Helpers.witness]
