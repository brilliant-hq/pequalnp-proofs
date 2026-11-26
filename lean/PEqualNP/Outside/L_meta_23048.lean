import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23048.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_23048.Helpers

theorem PEqualNP.Outside.L_meta_23048 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23048.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23048.Helpers.witness]
