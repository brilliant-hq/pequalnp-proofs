import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21926.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [8, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_21926.Helpers

theorem PEqualNP.Outside.L_meta_21926 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21926.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21926.Helpers.witness]
