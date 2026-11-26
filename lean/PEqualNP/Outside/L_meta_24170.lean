import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24170.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [6, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_24170.Helpers

theorem PEqualNP.Outside.L_meta_24170 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279261 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24170.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24170.Helpers.witness]
