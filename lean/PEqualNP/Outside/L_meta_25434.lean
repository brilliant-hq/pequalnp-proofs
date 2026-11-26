import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25434.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [10, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25434.Helpers

theorem PEqualNP.Outside.L_meta_25434 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549385 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25434.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25434.Helpers.witness]
