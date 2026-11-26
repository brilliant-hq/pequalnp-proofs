import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22017.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_22017.Helpers

theorem PEqualNP.Outside.L_meta_22017 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22017.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22017.Helpers.witness]
