import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22138.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [11, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22138.Helpers

theorem PEqualNP.Outside.L_meta_22138 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33939 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22138.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22138.Helpers.witness]
