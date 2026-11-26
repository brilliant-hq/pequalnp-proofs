import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22110.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.and, [12, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22110.Helpers

theorem PEqualNP.Outside.L_meta_22110 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22110.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22110.Helpers.witness]
