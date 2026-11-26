import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22466.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.or, [11, 18]⟩, ⟨GateOp.or, [17, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_22466.Helpers

theorem PEqualNP.Outside.L_meta_22466 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20026 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22466.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22466.Helpers.witness]
