import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22468.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 16-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [5, 17]⟩, ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.not, [19]⟩, ⟨GateOp.or, [16, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22468.Helpers

theorem PEqualNP.Outside.L_meta_22468 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 16 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16570 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22468.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22468.Helpers.witness]
