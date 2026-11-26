import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22122.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.and, [13, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22122.Helpers

theorem PEqualNP.Outside.L_meta_22122 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18366 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22122.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22122.Helpers.witness]
