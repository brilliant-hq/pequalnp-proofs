import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25306.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25306.Helpers

theorem PEqualNP.Outside.L_meta_25306 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164651 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25306.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25306.Helpers.witness]
