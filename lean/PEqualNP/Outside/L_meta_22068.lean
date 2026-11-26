import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22068.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [0, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22068.Helpers

theorem PEqualNP.Outside.L_meta_22068 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22068.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22068.Helpers.witness]
