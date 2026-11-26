import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25284.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [10, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25284.Helpers

theorem PEqualNP.Outside.L_meta_25284 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148146 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25284.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25284.Helpers.witness]
