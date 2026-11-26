import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22111.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22111.Helpers

theorem PEqualNP.Outside.L_meta_22111 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17981 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22111.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22111.Helpers.witness]
