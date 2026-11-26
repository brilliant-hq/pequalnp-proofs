import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22198.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22198.Helpers

theorem PEqualNP.Outside.L_meta_22198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17210 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22198.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22198.Helpers.witness]
