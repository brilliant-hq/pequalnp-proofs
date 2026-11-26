import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25299.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25299.Helpers

theorem PEqualNP.Outside.L_meta_25299 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164511 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25299.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25299.Helpers.witness]
