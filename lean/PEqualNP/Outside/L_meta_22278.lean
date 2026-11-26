import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22278.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [7, 16]⟩, ⟨GateOp.or, [13, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22278.Helpers

theorem PEqualNP.Outside.L_meta_22278 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16915 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22278.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22278.Helpers.witness]
