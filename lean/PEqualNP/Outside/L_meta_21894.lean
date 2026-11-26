import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21894.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 5-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_21894.Helpers

theorem PEqualNP.Outside.L_meta_21894 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21894.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21894.Helpers.witness]
