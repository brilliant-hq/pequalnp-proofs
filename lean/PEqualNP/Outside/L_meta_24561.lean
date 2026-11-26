import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24561.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [0, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24561.Helpers

theorem PEqualNP.Outside.L_meta_24561 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4312767 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24561.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24561.Helpers.witness]
